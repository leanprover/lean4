LAKE_HOME=../..
LEAN_HOME=$(dirname $(dirname $(elan which lean)))
export LEAN_PATH="${LEAN_HOME}/lib/lean:${LAKE_HOME}/build"
${LAKE_HOME}/build/bin/Lake build bin
