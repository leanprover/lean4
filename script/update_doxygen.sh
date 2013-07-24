#!/usr/bin/env bash
#
# update_doxygen.sh:
#       1) Install and run doxygen
#       2) Push the result to gh-pages branch
#
# author: Soonho Kong
#
if [ "$TRAVIS_PULL_REQUEST" == "false" ]; then
    echo -e "Starting to generate doxygen pages"
    sudo apt-get -qq install doxygen graphviz;
    doxygen src/Doxyfile;
    COMMIT_LOG=`git log --oneline -n 1`;
    mv doc $HOME
    echo -e "Done.\n"

    echo -e "Starting to update gh-pages\n"
    #go to home and setup git
    cd $HOME
    git config --global user.email "travis@travis-ci.org"
    git config --global user.name "Travis"

    #using token clone gh-pages branch
    git clone --quiet --branch=gh-pages https://${GH_TOKEN}@github.com/leodemoura/lean.git  gh-pages > /dev/null
    #go into diractory and copy data we're interested in to that directory
    cd gh-pages
    mv -Rf $HOME/doc .
    #add, commit and push files
    git add -A doc
    git commit -m "Push doxygen for the commit -- $COMMIT_LOG -- to gh-pages"
    git push -fq origin gh-pages > /dev/null
    echo -e "Done.\n"
fi
