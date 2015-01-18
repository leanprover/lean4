#!/usr/bin/env python
#
# Copyright (c) 2013 Microsoft Corporation. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
#
# Author: Soonho Kong
#

# Python 2/3 compatibility
from __future__ import print_function

import dropbox
import os
import argparse

parser = argparse.ArgumentParser()
parser.add_argument('--dropbox-token', type=str, help='Dropbox token for authentication', required=True)
parser.add_argument('--destpath',      type=str, help='Destination in Dropbox', required=True)
parser.add_argument('--srcpath',       type=str, help='Local directory to copy')
parser.add_argument('--copylist',      type=str, help='File containing a list of files to copy')
parser.add_argument('--deletelist',    type=str, help='File containing a list of files to delete')
args = parser.parse_args()

if not args.srcpath and not args.copylist and not args.deletelist:
    print("You need to specify one of the following options:")
    print("    --srcpath,")
    print("    --copylist,")
    print("    --deletelist")
    exit(1)

access_token = args.dropbox_token
server_path = args.destpath

# Connect DROPBOX
try:
    client = dropbox.client.DropboxClient(access_token)
    client.account_info()
except:
    print("Failed to connect to Dropbox. Please check the access token.")
    exit(1)

count = 0
def copy_file_with_retry(fullpath, targetpath, max_try):
    global count
    print("==> " + targetpath)
    try:
        handle = open(fullpath)
    except:
        print("FAILED: " + fullpath + " not found")
        return

    try:
        response = client.put_file(targetpath, handle, True)
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

def remove_from_dropbox(p):
    try:
        client.file_delete(p)
        print (p + " deleted from Dropbox")
    except dropbox.rest.ErrorResponse:
        print (p + " not exists")

if args.srcpath:
    local_path = args.srcpath
    print ("Copy: " + local_path + " ==> " + server_path)
    upload_dir_to_dropbox(local_path, server_path)
    exit(0)

if args.copylist:
    copylist = args.copylist
    print ("Copy files in " + copylist + " ==> " + server_path)
    try:
        copylist_handle = open(copylist, "r")
    except IOError:
        print('Failed to open ' + copylist)
    for line in copylist_handle:
        fullpath = os.path.normpath(line.strip())
        copy_file_with_retry(fullpath, os.path.normpath(server_path + "/" + fullpath), 5)
    exit(0)

if args.deletelist:
    deletelist = args.deletelist
    print ("Delete files in " + deletelist + " from Dropbox " + server_path)
    try:
        deletelist_handle = open(deletelist, "r")
    except IOError:
        print('Failed to open ' + deletelist)
    deletelist_handle = open(deletelist, "r")
    for line in deletelist_handle:
        fullpath = os.path.normpath(line.strip())
        remove_from_dropbox(os.path.normpath(server_path + "/" + fullpath))
    exit(0)
