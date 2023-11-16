#!/bin/bash

# Name of the remote repository
remote_name="nightly"

# Prefix for tags to search for
tag_prefix="nightly-"

# Fetch all tags from the remote repository
git fetch $remote_name --tags > /dev/null

# Get the most recent commit that has a matching tag
tag_name=$(git tag --merged HEAD --list "${tag_prefix}*" | sort -rV | head -n 1 | sed "s/^$tag_prefix//")

if [ -z "$tag_name" ]; then
    exit 1
fi

echo "$tag_name"
