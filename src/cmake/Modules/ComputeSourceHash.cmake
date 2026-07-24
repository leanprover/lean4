# Computes a SHA-256 content hash of all files (tracked + untracked, dirty-aware)
# under HASH_DIR and renders a header by substituting @GIT_SHA1@ in TEMPLATE.
#
# Invoke via `cmake -P` with the following -D variables set:
#   HASH_DIR  — absolute path to the directory whose contents to hash
#   TEMPLATE  — path to the .in template (e.g. githash.h.in)
#   OUTPUT    — path where the rendered file should be written
#
# Caller should pair with `cmake -E copy_if_different` so an unchanged hash
# does not trigger a downstream rebuild.

cmake_minimum_required(VERSION 3.10)

foreach(_arg HASH_DIR TEMPLATE OUTPUT)
  if(NOT DEFINED ${_arg})
    message(FATAL_ERROR "ComputeSourceHash: -D${_arg}=... is required")
  endif()
endforeach()

include("${CMAKE_CURRENT_LIST_DIR}/SourceFileList.cmake")
_list_source_files("${HASH_DIR}" _all)

set(_combined "")
foreach(_f IN LISTS _all)
  set(_full "${HASH_DIR}/${_f}")
  if(EXISTS "${_full}" AND NOT IS_DIRECTORY "${_full}")
    file(SHA256 "${_full}" _h)
    string(APPEND _combined "${_h}\t${_f}\n")
  else()
    # Tracked but deleted, or nested-repo entry the lister did not flag.
    string(APPEND _combined "D\t${_f}\n")
  endif()
endforeach()

string(SHA256 GIT_SHA1 "${_combined}")

configure_file("${TEMPLATE}" "${OUTPUT}" @ONLY)
