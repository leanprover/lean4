LAKE_HOME=../..
LEAN_HOME=$(dirname $(dirname $(cygpath -u $(elan which lean))))
export LEAN_PATH="${LEAN_HOME}/lib/lean:${LAKE_HOME}/build"
${LAKE_HOME}/build/bin/Lake.exe build bin
