#!/bin/bash

# This script assumes the HPC command line tool `job` is in your path.
# To install HPC go to \\msr-arrays\Tools\HPC-V3-SP3

# Script configuration
HEAD=RR1-N13-09-H44   # HEAD node of a HPC cluster
WORKDIR="\\\\msr-arrays\\Scratch\\msr-pool\\Redmond\\leonardo" # Path for the working directory in the HPC Cluster. It must contain input test files and auxiliary DLLs needed for executing Lean
LEAN_PATH=/cygdrive/c/Users/leonardo/projects/lean
BUILD_PATH=$LEAN_PATH/build
BUILD_TYPE=Debug
REPO=origin
BRANCH=master
LOG=$LEAN_PATH/build_log
RESULT_DIR=$LEAN_PATH/build/results
MAKE_JOBS=20
################################

PREV_COMMIT=$LEAN_PATH/prev_commit

# Update Lean binary
cd $LEAN_PATH
git fetch $REPO
git reset --hard $REPO/$BRANCH
GIT_COMMIT=`git log --oneline -n 1 | cut -d ' ' -f 1`    # Used for BUILDNAME
if [[ ! -a $PREV_COMMIT ]] || [[ `cat $PREV_COMMIT` != $GIT_COMMIT ]] 
then
    mkdir -p $BUILD_PATH
    cd $BUILD_PATH
    rm -rf *
    cmake $LEAN_PATH/src -DCMAKE_BUILD_TYPE=$BUILD_TYPE
    make -j $MAKE_JOBS
    echo `date` : Build $GIT_COMMIT | tee -a $LOG
    echo $GIT_COMMIT > $PREV_COMMIT
else
    echo "$GIT_COMMIT is already built." | tee -a $LOG 
fi 

# Copy lean to workdir in the cluster
cd $BUILD_PATH
cp shell/lean.exe $WORKDIR

# Create new job
JobId=`job new /scheduler:$HEAD | awk '{ print $4 }'`
echo "Created HPC job $JobId"

# Add tasks for executing .lean files at $WORKDIR
for f in `ls $WORKDIR`; do
   if [ ${f:(-5)} == ".lean" ]; then
       job add $JobId /scheduler:$HEAD /workdir:$WORKDIR /stdout:$f.$JobId.out /stderr:$f.$JobId.err /stdin:$f lean.exe
   fi
done

# Submit job
job submit /id:$JobId /scheduler:$HEAD

# Wait job to finish
for (( ; ; )); do
    if job view $JobId /scheduler:$HEAD | grep "State.*Finished"; then
        echo "Job $JobId has finished"
	break
    else 
    if job view $JobId /scheduler:$HEAD | grep "State.*Failed"; then
        echo "Job $JobId has failed"
	echo "======= FAILURE Details from HPC ========="
	job view $JobId /scheduler:$HEAD
	echo "=========================================="
	break
    else
	echo "Waiting for job $JobId"
        sleep 1
    fi 
    fi
done


# Move results to RESULT_DIR
mkdir -p $RESULT_DIR
for f in `ls $WORKDIR`; do
    if [ `expr match "$f" ".*$JobId.out.*"` != 0 ]; then
	echo "Copying $WORKDIR\\$f"
	cp "$WORKDIR\\$f" $RESULT_DIR
	rm "$WORKDIR\\$f"
    fi
    if [ `expr match "$f" ".*$JobId.err.*"` != 0 ]; then
	echo "Copying $WORKDIR\\$f"
	cp "$WORKDIR\\$f" $RESULT_DIR
	rm "$WORKDIR\\$f"
    fi
done



