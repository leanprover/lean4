#!/usr/bin/env python
import dropbox
import os
import sys

# Paths
local_path = sys.argv[1]
server_path = sys.argv[2]

# AUTH INFO
access_token = sys.argv[3]

# Connect DROPBOX
client = dropbox.client.DropboxClient(access_token)
print(client.account_info())

count = 0
def copy_file_with_retry(fullpath, targetpath, max_try):
    global count
    print("==> " + targetpath)
    try:
        handle = open(fullpath)
        response = client.put_file(targetpath, handle)
    except:
        handle.close()
        print("FAILED: " + targetpath)
        if count < max_try:
            count = count + 1
            copy_file_with_retry(fullpath, targetpath, max_try)
        else:
            raise
    count = 0
    handle.close()

def upload_dir_to_dropbox(localDir, serverDir):
    localDir = os.path.expanduser(localDir)
    for dirName, subdirList, fileList in os.walk(localDir):
        for fname in fileList:
            fullpath = os.path.normpath(dirName + "/" + fname)
            targetpath = os.path.normpath(serverDir + "/" + fullpath[len(localDir):])
            copy_file_with_retry(fullpath, targetpath, 5)

def remove_dir_from_dropbox(serverDir):
    try:
        client.file_delete(serverDir)
    except dropbox.rest.ErrorResponse:
        print (serverDir + " not exists")

print ("Copy: " + local_path + " ==> " + server_path)
remove_dir_from_dropbox(server_path)
upload_dir_to_dropbox(local_path, server_path)
