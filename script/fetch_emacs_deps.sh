#!/bin/bash
# Script for copying the Lean Emacs mode dependencies from https://github.com/leanprover/emacs-dependencies.git.
# We usually use it to test `leanemacs` without installing Lean.
# We execute this script at src/emacs.
read -p "Script will delete directory 'dependencies' and create it again with the content of https://github.com/leanprover/emacs-dependencies.git, Are you sure [y/n]? " -n 1 -r
echo    # (optional) move to a new line
if [[ ! $REPLY =~ ^[Yy]$ ]]
then
    echo "ABORTED."
    exit 1
fi
rm -r -f dependencies
git clone https://github.com/leanprover/emacs-dependencies.git
rm -r -f emacs-dependencies/.git
mv emacs-dependencies dependencies
