# Defines `_list_source_files(<dir> <out_var>)` which sets <out_var> to the
# sorted, deduplicated list of files under <dir> that participate in the
# source content hash. Uses `git ls-files` when available (covers tracked +
# untracked, honoring .gitignore) and falls back to `jj file list` for pure-jj
# workspaces. Paths are relative to <dir>.

function(_list_source_files _dir _out)
  set(_files_out "")
  set(_listed FALSE)
  find_program(_lsf_git git)
  if(_lsf_git)
    execute_process(
      COMMAND "${_lsf_git}" ls-files
      WORKING_DIRECTORY "${_dir}"
      OUTPUT_VARIABLE _tracked
      OUTPUT_STRIP_TRAILING_WHITESPACE
      RESULT_VARIABLE _rc
      ERROR_QUIET
    )
    if(_rc EQUAL 0)
      execute_process(
        COMMAND "${_lsf_git}" ls-files --others --exclude-standard
        WORKING_DIRECTORY "${_dir}"
        OUTPUT_VARIABLE _untracked
        OUTPUT_STRIP_TRAILING_WHITESPACE
      )
      set(_files_out "${_tracked}\n${_untracked}")
      set(_listed TRUE)
    endif()
  endif()
  if(NOT _listed)
    find_program(_lsf_jj jj)
    if(_lsf_jj)
      execute_process(
        COMMAND "${_lsf_jj}" file list
        WORKING_DIRECTORY "${_dir}"
        OUTPUT_VARIABLE _files_out
        OUTPUT_STRIP_TRAILING_WHITESPACE
        RESULT_VARIABLE _rc
        ERROR_QUIET
      )
      if(_rc EQUAL 0)
        set(_listed TRUE)
      endif()
    endif()
  endif()
  if(NOT _listed)
    message(FATAL_ERROR "SourceFileList: could not list files in ${_dir} (no usable git or jj)")
  endif()
  string(REPLACE "\n" ";" _files "${_files_out}")
  list(REMOVE_DUPLICATES _files)
  list(SORT _files)
  set(_result "")
  foreach(_f IN LISTS _files)
    # Skip empty entries and nested-repo directory listings (trailing slash).
    if(NOT _f STREQUAL "" AND NOT _f MATCHES "/$")
      list(APPEND _result "${_f}")
    endif()
  endforeach()
  set(${_out} "${_result}" PARENT_SCOPE)
endfunction()
