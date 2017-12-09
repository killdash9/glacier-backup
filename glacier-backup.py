#!/usr/bin/env python3
import sys
import os
import sqlite3
import datetime
import hashlib
import tarfile
import fcntl
import binascii
import boto3
import argparse
import dateutil
import re
import operator
import shutil
import time
import json

# All archives created in the same run are part of an archive set
# Archives in the same set are named with the date and time that the archive process began
# Each archive in a set has an index number,
# and the final archive in the set has a .final in the name.
# An archive set might look like the following.
# 
# 2017-12-04T23:08:50.058748.1.tar
# 2017-12-04T23:08:50.058748.2.tar
# 2017-12-04T23:08:50.058748.3.tar
# 2017-12-04T23:08:50.058748.4.final.tar
# 
# There are two kinds of manifest files:
# 
# .local-manifest
#     One per archive
#     Lists the files in that archive.  Duplicate files are listed in the .local-manifest but are not included in the tar.
#     Each line has the following format
#     
#     md5 path
# 
# .global-manifest
#     One per archive set
#     Only present in final archive of the set
#     Each line has the following format
# 
#     md5 archive_name archive_id path
#
#     where archive_name and archive_id indicate which archive contains the file.
#     If archive_name and archive_id are -, then the file is contained in the same archive as the .global-manifest
#

def process_arguments():
    parser = argparse.ArgumentParser(description='A tool to backup to and restore from a glacier vault.')
    
    subparsers = parser.add_subparsers(help='The operation to perform')
    
    p = add_parser(subparsers, "backup", "Backup a directory to a glacier vault")
    p.add_argument('-d','--directory', help='The directory to back up', required=True)
    p.add_argument('-v','--vault', default='backup', help='The name of the glacier vault to backup to', required=True)
    p.add_argument('-s','--size', help='The target archive size in MB', type=float, default=20)
    p.add_argument('-p','--profile', help='The aws profile to use', default=None)
    p.set_defaults(func=backup)
    
    p = add_parser(subparsers,"restore","Restore to a directory from a glacier vault")
    p.add_argument('-v','--vault', default='backup', help='The name of the glacier vault to backup to', required=True)
    p.add_argument('-d','--destination', help='The destination directory to restore to', required=True)
    p.add_argument('-s','--speed', type=int, help='The target download speed, in Megabits per second', required=True)
    p.add_argument('-a','--archive-id', help='The archive id snapshot to restore from.  If not specified, the inventory will be pulled and it will use the most recent snapshot shown in the inventory.')
    p.add_argument('-t','--tier', help='The request tier.', choices=['Bulk','Standard','Expedited'], default='Bulk')
    p.add_argument('-p','--profile', help='The aws profile to use', default=None)
    p.set_defaults(func=restore)
    
    p = add_parser(subparsers,"list-vaults","List all the glacier vaults in the AWS account")
    p.add_argument('-p','--profile', help='The aws profile to use', default=None)
    p.set_defaults(func=list_vaults)
    
    p = add_parser(subparsers,"list-jobs","List all the glacier jobs in the given vault")
    p.add_argument('-p','--profile', help='The aws profile to use', default=None)
    p.add_argument('-v','--vault', default='backup', help='The name of the glacier vault to backup to', required=True)
    p.set_defaults(func=list_jobs)
    
    p = add_parser(subparsers,"show-restore-errors","List the archives that have had retrieval errors")
    p.set_defaults(func=show_restore_errors)
    p.add_argument('-d','--destination', help='The destination directory to restore to', required=True)
    
    p = add_parser(subparsers,"reset-expired","Reset all the archives whose retrieval has expired")
    p.set_defaults(func=reset_expired)
    p.add_argument('-d','--destination', help='The destination directory to restore to', required=True)
    
    p = add_parser(subparsers,"verify-archives-exist","Verify that archives referenced by the manifest exist in glacier.")
    p.set_defaults(func=verify_archives_exist)
    p.add_argument('-d','--directory', help='The directory to back up', required=True)
    p.add_argument('-p','--profile', help='The aws profile to use', default=None)
    p.add_argument('-v','--vault', default='backup', help='The name of the glacier vault to backup to', required=True)
    
    args=parser.parse_args()
    args.func(args)

#commands
def backup(args):
    glacier_client = get_glacier_client(args.profile)
    verify_vault_exists(glacier_client,args.vault, True)
    glacier_backup_dir=get_glacier_backup_dir(args.directory,True)
    lock_file = os.path.join(glacier_backup_dir,"lock")
    lock_handle = lock(lock_file)
    
    local_manifest_file = os.path.join(glacier_backup_dir,'.local-manifest.txt')
    global_manifest_file = get_global_manifest_file(glacier_backup_dir)

    md5_cache_db_conn = open_md5_cache_db_conn(args.directory, True)
    vault_db_conn = open_vault_db_conn(args.directory, True, args.vault)
    
    # variables for queuing contents of tar files and limiting their size
    md5s_this_archive=set()
    files_to_archive=[]
    files_to_archive_size=0
    archive_index=1
    target_archive_size=args.size*1024*1024

    global_manifest = open(global_manifest_file, 'w')
    local_manifest = open(local_manifest_file, 'w')
    
    print ("==============================================================")
    print ("Archiving " + args.directory + " to glacier vault " + args.vault)
    print ("==============================================================")
    print ()
    
    archive_time = datetime.datetime.now()

    #Start recursing directory to be archived
    dirs=os.walk(args.directory)
    for (dirpath, dirnames, filenames) in dirs:
    
        #Skip the staging directory
        if os.path.samefile(dirpath,glacier_backup_dir):
            continue
    
        print("Directory: " + dirpath)
        for filename in filenames:
            path=os.path.join(dirpath,filename)
            relpath = os.path.relpath(path,args.directory)
    
            if not os.path.isfile(path):
                print ("Skipping %s because it's not a file" % path)
                continue
    
            # Get the md5 hash
            # first check for the hash in the database
            cur = md5_cache_db_conn.execute("select modified,md5 from path where path=?",(relpath,))
            row = cur.fetchone()
            cur.close()
            mtime = os.path.getmtime(path)
    
            if row:
                #it was in the database
                (modified,md5)=row
                modified = float(modified)
    
            if (not row) or mtime != modified:
                #it wasn't in the database or the modification date has changed since the last db insertion
                #compute the hash
                md5=md5_func(path)
                modified = mtime
                #insert it into the database
                md5_cache_db_conn.execute("replace into path (path,md5,modified) values(?,?,?)",(relpath,md5,str(modified))).close()
                md5_cache_db_conn.commit()
    
            #see if the hash has been archived
            cur=vault_db_conn.execute("select archiveid,name from md5_archive where md5=?",(md5,))
            row = cur.fetchone()
            cur.close()

            if row:
                #This file is in another archive
                (archive_id, archive_name) = row
                #place the path in the global manifest
                global_manifest.write(('%s %s %s %s\n' % (md5, archive_name, archive_id, relpath)))
            else :
                #place the path in the local manifest
                local_manifest .write(('%s %s\n' % (md5, relpath)))

                duplicate = md5 in md5s_this_archive
                # queue the file for tarring
                size = os.path.getsize(path)
                files_to_archive.append((path,relpath,md5,duplicate))
                if not duplicate:
                    # don't count duplicates toward file size, since they aren't actually included in the tar
                    files_to_archive_size += size
    
                if files_to_archive_size > target_archive_size:
                    # Have enough files for the tar, create it. 
                    local_manifest.close()

                    (archive_id, archive_name) = make_tar_and_upload_to_glacier(files_to_archive, local_manifest_file, None, archive_index, vault_db_conn, glacier_client, args.vault, archive_time, glacier_backup_dir)

                    #record the archive information in the global manifest
                    for (path,relpath,md5,duplicate) in files_to_archive:
                        global_manifest.write(('%s %s %s %s\n' % (md5, archive_name, archive_id, relpath)))
                    #reset tracking variables for next archive
                    md5s_this_archive=set()
                    files_to_archive = []
                    files_to_archive_size = 0
                    archive_index+=1
                    local_manifest = open(local_manifest_file, 'w')
                    
    #flush any possible queued files
    for (path,relpath,md5,duplicate) in files_to_archive:
        # record them in the global manifest as local files
        global_manifest.write(('%s %s %s %s\n' % (md5, '-', '-', relpath)))
        
    local_manifest.close()
    global_manifest.close()
    (archive_id, archive_file_name) = make_tar_and_upload_to_glacier(files_to_archive, local_manifest_file, global_manifest_file, archive_index, vault_db_conn, glacier_client, args.vault, archive_time, glacier_backup_dir)
    print ("Final archive is %s %s" %(archive_file_name, archive_id))
    
    #clean up resources
    unlock(lock_file, lock_handle)
    md5_cache_db_conn.close()
    vault_db_conn.close()

def restore(args):
    #Args
    tier = args.tier
    destination_dir=args.destination
    vault=args.vault
    target_mega_bits_per_second=args.speed
    target_bytes_per_second=target_mega_bits_per_second*1000000/8
    restore_archive_id = args.archive_id

    #Validation
    if (tier == 'Expedited'):
        if input("Expedited is expensive.  Are you sure you want to do this? ") != "y":
            error_exit("Aborting")

    os.makedirs(destination_dir, exist_ok=True)
    glacier_restore_dir = get_glacier_restore_dir(destination_dir)
    if not os.path.isdir(glacier_restore_dir):
        # make sure the destination directory is empty 
        if os.listdir(destination_dir):
            error_exit("The restoration directory you gave is not empty.  Refusing to restore to that directory.")
    
    glacier_client=get_glacier_client(args.profile)
    verify_vault_exists(glacier_client,vault, None)

    #Validation has passed, proceed with restore.
    os.makedirs(glacier_restore_dir,exist_ok=True)

    lock_file = os.path.join(glacier_restore_dir,"lock")
    lock_handle = lock(lock_file)

    if not restore_archive_id:
        #get an inventory list
        inventory_file = os.path.join(glacier_restore_dir, "inventory.json")
        glacier_retrieve_synchronous(glacier_client, glacier_restore_dir, vault, 'inventory-retrieval', None, inventory_file, None, None)
            
        with open(inventory_file) as json_data:
            inventory = json.load(json_data)
            
        archive_list=inventory['ArchiveList']
        # make sure there are archives
        if len(archive_list) == 0:
            error_exit("There are zero archives in this inventory!  Restore not possible.")
    
        archive_list = [x for x in archive_list if "final" in x['ArchiveDescription']]
        sorted_archive_list = sorted(archive_list, key=operator.itemgetter("CreationDate"), reverse=True)
        most_recent_archive = sorted_archive_list[0]
        print("Most recent archive is %s.  Restoring to that point." % most_recent_archive['ArchiveDescription'])
        restore_archive_id = most_recent_archive['ArchiveId']
        restore_archive_name = most_recent_archive['ArchiveDescription']
        restore_archive_size = most_recent_archive['Size']
    else:
        restore_archive_name = restore_archive_id + '.tar'
        restore_archive_size = None #unknown
        
    restore_archive_file = os.path.join(glacier_restore_dir,restore_archive_name)
    
    glacier_retrieve_synchronous(glacier_client, glacier_restore_dir, vault, 'archive-retrieval', restore_archive_id, restore_archive_file, restore_archive_size, 'Expedited')
    
    restore_database_file = get_restore_database_file(glacier_restore_dir)
    master_manifest_file  = get_global_manifest_file(glacier_restore_dir)

    if os.path.isfile(restore_database_file):
        #check for tables
        db_conn = sqlite3.connect(restore_database_file)
    else:
        print ("Creating:  Restore tracking database")
        db_conn = sqlite3.connect(restore_database_file)
        db_conn.execute("create table path_archive (path text primary key, archive_id text, md5 text)")
        db_conn.execute("create index path_archive_archive_id on path_archive (archive_id)")
        db_conn.execute("create table archive_status (archive_id text primary key, archive_name text, status text)")
    
        # populate the database from the manifest file
    
        # look at the global manifest in the most recent archive
        with tarfile.open(restore_archive_file, "r") as tar:
            tar.extract('.global-manifest.txt',glacier_restore_dir)
            extracted_md5_paths=dict()
            regex = re.compile('^([^ ]+) ([^ ]+) ([^ ]+) (.+)$')
            for line in open(master_manifest_file, 'r'):
                m = regex.match(line)
                if not m:
                    error_exit("Unparsable line in manifest:\n"+line)
        
                (md5,archive_name, archive_id, path) =m.groups()
        
                if archive_id == '-':
                    if md5 in extracted_md5_paths:
                        #tar files don't contain multiple files with the same md5, only the firt one is present.
                        #it's already been extracted to another file, copy it.  
                        shutil.copyfile(os.path.join(destination_dir,extracted_md5_paths[md5]), os.path.join(destination_dir, path))
                    else:
                        #extract the file from this tar
                        tar.extract(path, destination_dir)
                        extracted_md5_paths[md5]=path
                else:
                    db_conn.execute("insert into path_archive (path,archive_id,md5) values(?,?,?) ",(path, archive_id, md5))
                    db_conn.execute("replace into archive_status (archive_id, archive_name, status) values(?,?,'unrequested') ",(archive_id, archive_name))
    
        db_conn.commit()

    #database is now populated
    expired_job_ids=set()
    while True:
        sleep_seconds = 10
    
        # Categorize current jobs
        jobs = glacier_client.list_jobs(vaultName = vault)
        
        succeeded_job_archive_ids=set()
        failed_job_archive_ids=set()
        all_job_archive_ids=set()
        all_job_archive_id_toJob=dict()
        earliest_job_time = None
        total_job_bytes=0
        
        for job in jobs['JobList']:
            if job['Action'] == 'ArchiveRetrieval':
                archive_id = job['ArchiveId']
    
                #keep track of earliest job
                creation_date = dateutil.parser.parse(job['CreationDate'])
                if (not earliest_job_time) or earliest_job_time > creation_date:
                    earliest_job_time = creation_date
                size = job['ArchiveSizeInBytes']
    
                #keep track of total size
                total_job_bytes += size
                
                all_job_archive_ids.add(archive_id)
                if not archive_id in all_job_archive_id_toJob: #take the first one, since it's more recent
                    all_job_archive_id_toJob[archive_id] = job
                if job['StatusCode'] == 'Succeeded':
                    succeeded_job_archive_ids.add(archive_id)
                elif job['StatusCode'] == 'Failed':
                    failed_job_archive_ids.add(archive_id)
    
        # Get database state
        requested_archive_ids=set()
        unrequested_archive_ids=set()
        downloaded_archive_ids=set()
        failed_archive_ids=set()
        archive_count = 0
        for row in db_conn.execute("select archive_id, status from archive_status"):
            archive_count+=1
            (archive_id, status) = row
            if status == 'requested':
                requested_archive_ids.add(archive_id)
            elif status == 'unrequested':
                unrequested_archive_ids.add(archive_id)
            elif status == 'downloaded':
                downloaded_archive_ids.add(archive_id)
            elif status == 'failed':
                failed_archive_ids.add(archive_id)
    
        if (archive_count == 0):
            error_exit("The archive count is zero.  Something's not right.")
    
        # could we be all done?
        if not requested_archive_ids and not unrequested_archive_ids:
            if len(downloaded_archive_ids)==archive_count:
                print("Done downloading and extracting archives.")
                print("Performing a final verification.")
                regex = re.compile('^([^ ]+) ([^ ]+) ([^ ]+) (.+)$')
                for line in open(master_manifest_file, 'r'):
                    m = regex.match(line)
                    if not m:
                        error_exit("Unparsable line in manifest:\n"+line)
            
                    (md5,archive_name, archive_id, path) =m.groups()
    
                    print("Verify:    %s..." % path,end='',flush=True )
                    
                    actual_md5 = md5_func(os.path.join(destination_dir, path))
                    
                    if md5 == actual_md5:
                        print("OK")
                    else:
                        print("Failed")
                        print("%s has an md5 sum of %s, but the manifest expects %s",(path, actual_md5, md5))
                        exit(1)
                
                print("Final verification passed.")
                print("Restore complete.")
                break
            else:
                error_exit("There are no more archives to download, but some archives are in a failed or expired state.  Manual intervention required.")
            
        # Mark expired in db
        expired_archive_ids = requested_archive_ids - all_job_archive_ids
        for expired_archive_id in expired_archive_ids:
            db_conn.execute("update archive_status set status='expired' where archive_id=?",(expired_archive_id,))
            db_conn.commit()
            print ("WARNING:   Job expired: " + id('a',expired_archive_id))
    
        # Mark failed in db
        need_to_be_marked_failed_archiveIds = failed_job_archive_ids - failed_archive_ids
        for need_to_be_marked_failed_archiveId in need_to_be_marked_failed_archiveIds:
            db_conn.execute("update archive_status set status='failed' where archive_id=?",(expired_archive_id,))
            db_conn.commit()
            print ("WARNING: job failed: " + (expired_archive_id))
    
        # Request archives
        if unrequested_archive_ids:
            start_job=False
            if earliest_job_time:
                elapsed_time_seconds = (datetime.datetime.now(datetime.timezone.utc) - earliest_job_time).total_seconds()
                rate = total_job_bytes / elapsed_time_seconds
                start_job = rate < target_bytes_per_second
            else:
                start_job = True
    
            if start_job:
                archive_id_to_request = list(unrequested_archive_ids)[0]
            
                cur = db_conn.execute("select archive_name from archive_status where archive_id=?",(archive_id_to_request,))
                row = cur.fetchone()
                archive_name = row[0]
                cur.close()
                
                job = get_existing_job(glacier_client,vault, 'archive-retrieval', archive_id_to_request, None)
                
                if not job:
                    print("Retrieve:  Archive     %s %s" % (id('a',archive_id_to_request), archive_name))
                    job_parameters={
                        'Description': archive_name,
                        'Type': 'archive-retrieval',
                        'ArchiveId':archive_id_to_request,
                        'Tier': tier
                    }
                                
                    glacier_client.initiate_job(
                        jobParameters=job_parameters,
                        vaultName=vault,
                    )
                
                db_conn.execute("update archive_status set status='requested' where archive_id=?",(archive_id_to_request,))
                db_conn.commit()
    
        # Download archives
        ready_for_download_archiveIds = (requested_archive_ids & succeeded_job_archive_ids) - downloaded_archive_ids
        if ready_for_download_archiveIds:
            archive_id_to_download=list(ready_for_download_archiveIds)[0]
            job_to_download=all_job_archive_id_toJob[archive_id_to_download]
            download_dir = os.path.join(glacier_restore_dir, 'download')
            os.makedirs(download_dir,exist_ok=True)
            archive_name=job_to_download['JobDescription']
            downloaded_archive_file = os.path.join(download_dir, archive_name)
    
            try:
                download_job(glacier_client, vault, job_to_download['JobId'], downloaded_archive_file, job_to_download['ArchiveSizeInBytes'])
            except glacier_client.exceptions.ResourceNotFoundException:
                # it must have expired.  Blacklist it and re-request this one.
                # expired_job_ids.add(jobs_to_download['JobId'])
                # db_conn.execute("update archive_status set status='unrequested' where archive_id=?",(archive_id_to_download,))
                # db_conn.commit()
                raise
            except glacier_client.exceptions.InvalidParameterValueException as e:
                if "The job is not currently available for download" in str(e):
                    print("not currently available for download")
                else:
                    print("not currently available for download???")
                    print(dir(e))
                    print(e)
            else:
                # extracting just the files referenced by the manifest
                md5_to_path=dict()
                for row in db_conn.execute("select md5,path from path_archive where archive_id=?",(archive_id_to_download,)):
                    md5 = row[0]
                    path = row[1]
                    if not md5 in md5_to_path:
                        md5_to_path[md5]=[]
                    md5_to_path[md5].append(path)
        
                if not md5_to_path:
                    error_exit("The archive %s was downloaded but we have nothing to extract from it.  Something's wrong." % downloaded_archive_file)
                
                with tarfile.open(downloaded_archive_file, "r") as tar:
                    tar.extract('.local-manifest.txt',download_dir)
                    regex = re.compile('^([^ ]+) (.+)$')
                    for line in open(os.path.join(download_dir, '.local-manifest.txt'), 'r'):
                        m = regex.match(line)
                        if not m:
                            error_exit("Unparsable line in manifest:\n"+line)
        
                        md5=m.group(1)
                        path=m.group(2)
                        
                        destinations_for_md5 = md5_to_path.pop(md5,None)
                        if destinations_for_md5:
                            tar.extract(path, download_dir)
                            extracted_file = os.path.join(download_dir, path)
            
                            extracted_md5 = md5_func(extracted_file)
                            if md5 != extracted_md5:
                                error_exit("md5 didn't match for path %s.  Manifest said %s but restored file was %s" % (md5, extracted_md5))
        
                            #md5 matches, move it to the correct place(s).
                            first_file=None
                            for destination_path in destinations_for_md5:
                                restored_file_name = os.path.join(destination_dir, destination_path)
                                os.makedirs(os.path.dirname(restored_file_name),exist_ok=True)
                                if first_file:
                                    print("Copy:      %s to %s" % (first_file ,restored_file_name))
                                    shutil.copyfile(first_file, restored_file_name)
                                else:
                                    print("Extract:   %s" % restored_file_name)
                                    os.rename(extracted_file,restored_file_name)
                                    first_file = restored_file_name
        
                #md5_to_path would be empty if we found all the files we were looking for.
                if len(md5_to_path):
                    print ("The archive %s was expected to contain the following files but it did not." % downloaded_archive_file)
                    print(md5_to_path)
                    exit(1)
                    
                db_conn.execute("update archive_status set status='downloaded' where archive_id=?",(archive_id_to_download,))
                db_conn.commit()
        
                shutil.rmtree(download_dir)
                
                sleep_seconds=0
        time.sleep(sleep_seconds)
        
    #clean up resources
    unlock(lock_file, lock_handle)
    db_conn.close()

def list_vaults(args):
    glacier_client = get_glacier_client(args.profile)
    print(glacier_client.list_vaults()['VaultList'])

def list_jobs(args):
    glacier_client=get_glacier_client(args.profile)
    jobs = glacier_client.list_jobs(vaultName = args.vault)
    for s in ["%s %s %s %s %s"%(id('a',x['ArchiveId']) if x['Action'] == 'ArchiveRetrieval' else 'Inventory',id('j',x['JobId']),x['CreationDate'], x['StatusCode'], x['JobDescription']) for x in jobs['JobList']]:
        print(s)

def show_restore_errors(args):
    db_conn = open_restore_db_conn(args.destination)
    for row in db_conn.execute("select * from archive_status where status in ('failed','expired')"):
        print(row)
    db_conn.close()

def reset_expired(args):
    db_conn = open_restore_db_conn(args.destination)
    db_conn.execute("update archive_status set status='unrequested' where status ='expired'")
    db_conn.commit()
    db_conn.close()

def verify_archives_exist(args):
    glacier_backup_dir=get_glacier_backup_dir(args.directory,False)
    vault = args.vault
    inventory_file = os.path.join(glacier_backup_dir, "inventory.json")

    #start another inventory job if there's not one in progress already
    glacier_client=get_glacier_client(args.profile)
    start_inventory_job=True
    job = get_existing_job(glacier_client, vault, 'inventory-retrieval', None, None)
    if job:
        status = job['StatusCode']
        if status == 'InProgress':
            start_inventory_job=False #no more than one concurrent inventory job
        elif status == 'Succeeded':
            download_job(glacier_client, vault, job['JobId'], inventory_file, job['ArchiveSizeInBytes'])
        elif status == 'Failed':
            pass
    
    if start_inventory_job:
        print ("Retrieve:  Inventory")

        job_parameters={
            'Description': 'glacier-backup.py inventory job',
            'Format': 'JSON',
            'Type': 'inventory-retrieval'
        }
        
        job = glacier_client.initiate_job(
            jobParameters=job_parameters,
            vaultName=vault,
        )
    
    inventory = None
    global_manifest_file = get_global_manifest_file(glacier_backup_dir)
    if not os.path.isfile(global_manifest_file):
        error_exit("No global manifest file to check.  %s not found." % global_manifest_file)

    if time.time() - os.path.getmtime(global_manifest_file) > (2 * 24 * 60 * 60):
        print ("WARNING:   % is older than two days.  Is the backup being run regularly?" % global_manifest_file)
        
    if os.path.isfile(inventory_file):
        if time.time() - os.path.getmtime(inventory_file) > (2 * 24 * 60 * 60):
            print ("WARNING:   % is older than two days.  Is verify-archives-exist being run regularly?" % inventory_file)
            
        #make sure every archive listed in the most recent global manifest exists in the inventory

        with open(inventory_file) as json_data:
            inventory = json.load(json_data)

        inventory_archives=set()
        inventory_size=dict()
        manifest_archives=set()
        
        for archive in inventory['ArchiveList']:
            inventory_archives.add(archive['ArchiveId'],archive['ArchiveDescription'])
            inventory_size(archive['ArchiveId'], archive['ArchiveSizeInBytes'])
            
        regex = re.compile('^([^ ]+) ([^ ]+) ([^ ]+) (.+)$')
        for line in open(master_manifest_file, 'r'):
            m = regex.match(line)
            if not m:
                error_exit("Unparsable line in manifest:\n"+line)
            
            (md5,archive_name, archive_id, path) = m.groups()

            manifest_archives.add(archive_id, archive_name)

        m_not_i = (manifest_archives - inventory_archives)
        i_not_m = (inventory_archives - manifest_archives)
        if m_not_i:
            print ("Archives in manifest which are not in Glacier inventory:" )
            print (m_not_i)
        else:
            print ("The Glacier inventory has all archives listed in the manifest.")
        if i_not_m:
            unused_bytes = sum([inventory_size[x[0]] for x in i_not_m])
            print ("Archives in inventory which are not in the manifest, for a total of %s unneeded bytes:" % unused_bytes)
            print (i_not_m)
        else:
            print ("The manifest inventory has all archives listed in the manifest.")
    else:
        print("No inventory file downloaded yet.  Try again later.")

#utility functions
def add_parser(subparsers, name, description):
    return subparsers.add_parser(name,help=description, description=description)

def id(prefix,id):
    return prefix+":"+id[:4]

def error_exit(message):
    print(message)
    exit(1)
    
def lock(lock_file):
    #make sure we're the only one running
    lock_handle=open(lock_file, 'w')
    fcntl.flock(lock_handle, fcntl.LOCK_EX |fcntl.LOCK_NB)
    return lock_handle

def unlock (lock_file, lock_handle):
    fcntl.flock(lock_handle, fcntl.LOCK_UN)
    os.remove(lock_file)

#file and directory locator functions
def get_glacier_backup_dir(archive_dir, create):
    glacier_backup_dir = os.path.join(archive_dir,".glacier-backup")
    if not os.path.isdir(glacier_backup_dir):
        if create:
            os.makedirs(glacier_backup_dir,exist_ok=True)
        else:
            error_exit("No glacier backup directory in %s" % archive_dir)
    return glacier_backup_dir

def get_global_manifest_file(glacier_backup_dir):
    return os.path.join(glacier_backup_dir,'.global-manifest.txt')

def get_restore_database_file(glacier_backup_dir):
    return os.path.join(glacier_restore_dir, 'restore.sqlite3')

def get_glacier_restore_dir(destination):
    return os.path.join(destination,".glacier-restore")

#md5 functions
def hash_bytestr_iter(bytesiter, hasher, ashexstr=False):
    for block in bytesiter:
        hasher.update(block)
        return (hasher.hexdigest() if ashexstr else hasher.digest())

def file_as_blockiter(afile, blocksize=65536):
    with afile:
        block = afile.read(blocksize)
        while len(block) > 0:
            yield block
            block = afile.read(blocksize)
        yield b''

def md5_func(path):
    file=open(path,'rb')
    hash = hash_bytestr_iter(file_as_blockiter(file), hashlib.md5())
    file.close()
    return str(binascii.hexlify(hash), 'ascii')

#glacier functions
def get_glacier_client(profile):
    session = boto3.session.Session(profile_name=profile) #this profile is expected to exist and be mapped to an IAM user with glacier permissions
    return session.client('glacier')

def make_tar_and_upload_to_glacier(files_to_archive, local_manifest_file, global_manifest_file, archive_index, vault_db_conn, glacier_client, vault, archive_time, glacier_backup_dir):
    
    #create the tar
    if global_manifest_file:
        archive_file_name = "%s.%s.final.tar" % (archive_time.isoformat() , archive_index )
    else:
        archive_file_name = "%s.%s.tar" % (archive_time.isoformat() , archive_index )
    archive_full_path = os.path.join(glacier_backup_dir, archive_file_name)

    with tarfile.open(archive_full_path, 'w') as tar:
        #manifest first
        tar.add(local_manifest_file, '.local-manifest.txt')
        if global_manifest_file:
            tar.add(global_manifest_file, '.global-manifest.txt')
        
        #add each of the queued files to the tar, unless it's a duplicate in this archive
        for (path,relpath,md5,duplicate) in files_to_archive:
            if not duplicate:
                print ("Add:       " + relpath)
                tar.add(path,relpath)
            else:
                print ("Duplicate: " + relpath)
        
    #upload the tar to glacier
    with open(archive_full_path, 'rb') as tar:
        print ("Upload:    " + archive_file_name)
        response = glacier_client.upload_archive(vaultName=vault, archiveDescription=archive_file_name, body=tar)
        archive_id = response['archiveId']
        
    #os.remove(archive_full_path); todo put this back
    
    for (path,relpath,md5,duplicate) in files_to_archive:
        vault_db_conn.execute("replace into md5_archive (md5, archiveid, name) values(?,?,?)",(md5,archive_id, archive_file_name)).close()
        vault_db_conn.commit()

    return (archive_id, archive_file_name)

def verify_vault_exists(glacier_client, vault, create):
    print ("Checking for vault %s in glacier..." % vault, end='',flush=True)
    found=False
    existing_vaults = glacier_client.list_vaults()['VaultList']
    for v in existing_vaults:
        if v['VaultName'] == vault:
            found=True
    
    if not found and create:
        choice =input("\nThere's no glacier vault named %s.  Would you like to create it (y/n)? " % vault)
        if (choice != "y"):
            error_exit("Aborting")
            
        print ("Creating glacier vault: " + vault)
        print(glacier_client.create_vault(vaultName=vault))
    else:
        print ("found")
    
def download_job(glacier_client, vault, job_id, dest_file, expected_size):
    print('Download:  %s to %s...' % (id('j',job_id), os.path.basename(dest_file)),end='',flush=True)
    output = glacier_client.get_job_output(
        vaultName=vault,
        jobId=job_id,
    )['body']
    
    with open(dest_file, 'wb') as outfile:
        while outfile.write(output.read(amt=4096)):
            pass
    
    #print("Job output written to file %s" % dest_file)
    if expected_size and os.path.getsize(dest_file) != expected_size:
        print("Expected size of %s doesn't match actual downloaded size of %s" % (expected_size, os.path.getsize(dest_file)))

    print("done")

def get_existing_job(glacier_client, vault, type, archive_id, inventory_job_id ):
    if type == 'inventory-retrieval':
        if inventory_job_id:
            print ("Locate:    Inventory Job %s..." % id('j',inventory_job_id), end='',flush=True)
        else:
            print ("Locate:    Inventory Job...", end='',flush=True)
    else:
        print ("Locate:    Archive Job %s..." % id('a',archive_id), end='',flush=True)
        
    jobs = glacier_client.list_jobs(vaultName = vault)
    for job in jobs['JobList']:
        if (type == 'archive-retrieval' and job['Action'] == 'ArchiveRetrieval' and  job['ArchiveId'] == archive_id ) or (type == 'inventory-retrieval' and job['Action'] == 'InventoryRetrieval' and (not inventory_job_id or job['JobId'] == inventory_job_id)):
            status = job['StatusCode']
            job_id = job['JobId']
            print ("found. %s %s %s" % ( id('j',job_id), status, job['CreationDate']))
            return job
    print("not found")
    return None

def glacier_retrieve_synchronous(glacier_client,glacier_restore_dir, vault, type, archive_id, dest_file, expected_size, tier):
    inventory_job_id_file=os.path.join(glacier_restore_dir, 'inventory-job-id')
    if not os.path.isfile(dest_file) or (expected_size and os.path.getsize(dest_file) != expected_size):

        job_id = None
        inventory_job_id = None
        status = None
        if type == 'inventory-retrieval' and os.path.isfile(inventory_job_id_file):
            with open(inventory_job_id_file,'r') as file:
                inventory_job_id = file.read()

        if inventory_job_id or archive_id:
            job = get_existing_job(glacier_client, vault, type, archive_id, inventory_job_id)
            if job:
                creation_date = dateutil.parser.parse(job['CreationDate'])
                job_id = job['JobId']
                status = job['StatusCode']
        
        if not job_id:
            if type == 'inventory-retrieval':
                print ("Retrieve:  Inventory")
            else:
                print("Retrieve:  Archive     %s" % id('a',archive_id))

            if type == 'archive-retrieval':
                job_parameters={
                    'Description': 'glacier-backup.py archive job',
                    'Type': 'archive-retrieval',
                    'ArchiveId':archive_id,
                    'Tier': tier
                }
            else:
                job_parameters={
                    'Description': 'glacier-backup.py inventory job',
                    'Format': 'JSON',
                    'Type': 'inventory-retrieval'
                }
            
            job = glacier_client.initiate_job(
                jobParameters=job_parameters,
                vaultName=vault,
            )
            job_id = job['jobId']
            creation_date=datetime.datetime.now(datetime.timezone.utc)
            print("Job created, with job id ", id('j',job_id))
            if type == 'inventory-retrieval':
                #save this job id to a file
                with open(inventory_job_id_file, 'w') as file:
                    file.write(job_id)
            
        started_waiting = time.time() #seconds since epoch
        if status != 'Succeeded':
            print ("Waiting on Job: %s" % id('j',job_id))
        while True:
            description = glacier_client.describe_job(
                vaultName = vault,
                jobId=job_id
            )
            status = description['StatusCode']
            print("Waiting:   %s Status: %s       \r" % (datetime.datetime.now(datetime.timezone.utc) - creation_date, status), end='',flush=True)
            
            if status == 'Succeeded':
                break;
            elif status == 'Failed':
                print ("Job failed ")
                print (description)
                exit(1)
            elif status == 'InProgress':
                pass
            else:
                print ("Unknown job status: " + status)
                print(description)
                exit(1)
        
            been_waiting_for = time.time() - started_waiting
            if been_waiting_for > 60 * 60 * 24: #timeout after 24 hours
                error_exit("Timed out.  Job with id %s did not complete within 24 hours" % job_id)
            
            time.sleep(60)
            
        download_job(glacier_client, vault, job_id, dest_file, expected_size)
    else:
        print ("Job has already been retrieved and cached in %s.  Reading that file." % dest_file)

#database functions
def open_sqllite_conn(db_file, create, initialization_statements):
    if not os.path.isfile(db_file):
        if create:
            #initialize the path database
            print ("First time running, creating database file %s" % db_file)
            db = sqlite3.connect(db_file)
            for statement in initialization_statements:
                db.execute(statement).close()
            db.close()
        else:
            error_exit("No database at", db_file)
    return sqlite3.connect(db_file)

def open_vault_db_conn(archive_dir, create, glacier_vault):
    vault_db_file = os.path.join(get_glacier_backup_dir(archive_dir,create),"vault-"+glacier_vault+".sqlite3")
    return open_sqllite_conn(vault_db_file, create, ["create table md5_archive (md5 text primary key, archiveid text, name text)"])

def open_md5_cache_db_conn(archive_dir, create):
    md5_cache_db_file = os.path.join(get_glacier_backup_dir(archive_dir,create),"md5cache.sqlite3")
    return open_sqllite_conn(md5_cache_db_file, create, ["create table md5_archive (md5 text primary key, archiveid text, name text)"])

def open_restore_db_conn(destination):
    glacier_restore_dir = get_glacier_restore_dir(destination)
    restore_database_file = get_restore_database_file(glacier_restore_dir)
    if not os.path.isfile(restore_database_file):
        error_exit("no database at %s" % restore_database_file)
    return sqlite3.connect(restore_database_file)

process_arguments()

