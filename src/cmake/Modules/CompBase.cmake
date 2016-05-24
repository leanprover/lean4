# Copyright (C) 2015-2016 Jonathan Müller <jonathanmueller.dev@gmail.com>
# This file is subject to the license terms in the LICENSE file
# found in the top-level directory of this distribution.

# comp_base.cmake - base functionality for all compatibility files

include(CheckCXXSourceCompiles)
include(CheckCXXCompilerFlag)
include(CMakeParseArguments)

# EXTERNAL
# the current API version
set(COMP_API_VERSION 1.1 CACHE STRING "compatibility api version" FORCE)

# EXTERNAL
# download location for feature files, the feature file name will be appended
# to circumvent download process, manually place the files at the CMAKE_PATH
set(COMP_REMOTE_URL "https://raw.githubusercontent.com/foonathan/compatibility/master/" CACHE STRING "url of remote repository to be used for downloading the feature files")

# EXTERNAL; feature module
# requires a certain API version
function(comp_api_version version)
    string(FIND "${version}" "." first_dot)
    string(SUBSTRING "${version}" 0 ${first_dot} major_version)
    string(FIND "${COMP_API_VERSION}" "." first_dot)
    string(SUBSTRING "${COMP_API_VERSION}" 0 ${first_dot} comp_major_version)

    if(NOT major_version EQUAL comp_major_version OR COMP_API_VERSION VERSION_LESS version)
        message(FATAL_ERROR "compatibility version is ${COMP_API_VERSION}, required is ${version}")
    endif()
endfunction()

# INTERNAL
# gets name, followed by flag, name, flag, name, flag...
# checks flags in order of occurence
# first matching flag will be used!
# result is written into named cache option
function(_comp_check_flags result standard_name)
    message(STATUS "Checking flags for ${standard_name}")
    foreach(flag ${ARGN})
        if(NOT DEFINED name)
            set(name ${flag})
        else()
            set(CMAKE_REQUIRED_QUIET ON)
            check_cxx_compiler_flag("${flag}" ${name})
            if(${name})
                message(STATUS "Checking flags for ${standard_name} - Found: ${flag}")
                set(${result} ${flag} CACHE STRING "Flag to activate ${standard_name}")
                return()
            endif()
            unset(name)
        endif()
    endforeach()
    message(STATUS "Checking flags for ${standard_name} - No required ${standard_name} flag found, this could either be the case or missing support for your compiler.")
    set(${result} "" CACHE STRING "Flag to activate ${standard_name}")
endfunction()

set(COMP_CPP98_FLAG "" CACHE STRING "Flag to activate C++98")
_comp_check_flags(COMP_CPP11_FLAG "C++11" std_cpp11_flag -std=c++11 std_cpp0x_flag -std=c++0x)
_comp_check_flags(COMP_CPP14_FLAG "C++14" std_cpp14_flag -std=c++14 std_cpp1y_flag -std=c++1y)
_comp_check_flags(COMP_CPP17_FLAG "C++17" std_cpp17_flag -std=c++17 std_cpp1z_flag -std=c++1z)

# INTERNAL
# parses arguments for comp_compile_features
macro(_comp_parse_arguments)
    cmake_parse_arguments(COMP "NOPREFIX;CPP11;CPP14;CPP17;NOFLAGS" # no arg
                               "PREFIX;NAMESPACE;CMAKE_PATH;INCLUDE_PATH" # single arg
                                "" ${ARGN})
    if(COMP_NOPREFIX)
        set(COMP_PREFIX "")
        set(COMP_ID "")
    elseif(NOT DEFINED COMP_PREFIX)
        set(COMP_PREFIX "COMP_")
        set(COMP_ID "comp")
    elseif(${COMP_PREFIX} MATCHES "^.*_$")
        string(TOLOWER "${COMP_PREFIX}" COMP_ID)
        string(LENGTH "${COMP_ID}" length)
        math(EXPR length "${length} - 1")
        string(SUBSTRING "${COMP_ID}" 0 ${length} COMP_ID)
    else()
        string(TOLOWER "${COMP_PREFIX}" COMP_ID)
    endif()

    if(NOT DEFINED COMP_NAMESPACE)
        set(COMP_NAMESPACE "comp")
    endif()
    if(DEFINED _COMP_${COMP_ID}_namespace)
        if (NOT "${_COMP_${COMP_ID}_namespace}" STREQUAL "${COMP_NAMESPACE}")
            message(SEND_ERROR "Prefix ${COMP_PREFIX} already used with namespace name ${COMP_NAMESPACE} before")
        endif()
    else()
        set(_COMP_${COMP_ID}_namespace "${COMP_NAMESPACE}" CACHE INTERNAL "")
    endif()

    if(NOT DEFINED COMP_CMAKE_PATH)
        set(COMP_CMAKE_PATH "${CMAKE_BINARY_DIR}/comp.downloaded")
    endif()

    if(NOT DEFINED COMP_INCLUDE_PATH)
        set(COMP_INCLUDE_PATH "${CMAKE_BINARY_DIR}/comp.generated")
    endif()
endmacro()

# INTERNAL
# translates feature names
function(_comp_translate_feature feature)
    set(_cxx_alias_templates cpp11_lang/alias_template)
    set(_cxx_alignas cpp11_lang/alignas)
    set(_cxx_alignof cpp11_lang/alignof)
    set(_cxx_attribute_deprecated cpp14_lang/deprecated)
    set(_cxx_constexpr cpp11_lang/constexpr)
    set(_cxx_decltype cpp11_lang/decltype)
    set(_cxx_deleted_functions cpp11_lang/delete_fnc)
    set(_cxx_explicit_conversions cpp11_lang/explicit_conversion_op)
    set(_cxx_final cpp11_lang/final)
    set(_cxx_noexcept cpp11_lang/noexcept)
    set(_cxx_nullptr cpp11_lang/nullptr)
    set(_cxx_override cpp11_lang/override)
    set(_cxx_relaxed_constexpr cpp14_lang/general_constexpr)
    set(_cxx_rvalue_references cpp11_lang/rvalue_ref)
    set(_cxx_static_assert cpp11_lang/static_assert)
    set(_cxx_thread_local cpp11_lang/thread_local)
    set(_cxx_user_literals cpp11_lang/literal_op)
    set(_cxx_variable_templates cpp14_lang/variable_template)

    # note: triple underscore at beginning!
    set(___cpp_alias_templates cpp11_lang/alias_template)
    set(___cpp_constexpr cpp11_lang/constexpr)
    set(___cpp_decltype cpp11_lang/decltype)
    set(___cpp_user_defined_literals cpp11_lang/literal_op)
    set(___cpp_noexcept cpp11_lang/noexcept)
    set(___cpp_rvalue_references cpp11_lang/rvalue_ref)
    set(___cpp_static_assert cpp11_lang/static_assert)

    set(___cpp_return_type_deduction cpp14_lang/return_type_deduction)
    set(___cpp_sized_deallocation cpp14_lang/sized_deallocation)
    set(___cpp_variable_templates cpp14_lang/variable_template)

    set(___cpp_lib_exchange_function cpp14_lib/exchange)
    set(___cpp_lib_transparent_operators cpp14_lib/generic_operator_functors)
    set(___cpp_lib_integer_sequence cpp14_lib/integer_sequence)
    set(___cpp_lib_make_unique cpp14_lib/make_unique)
    set(___cpp_lib_quoted_string_io cpp14_lib/quoted)
    set(___cpp_lib_shared_timed_mutex cpp14_lib/shared_lock)
    set(___cpp_lib_robust_nonmodifying_seq_ops cpp14_lib/two_range_algorithms)

    set(___cpp_fold_expressions cpp17_lang/fold_expressions)
    set(___cpp_unicode_characters cpp17_lang/utf8_char_literal)

    set(___cpp_lib_nonmember_container_access cpp17_lib/container_access)
    set(___cpp_lib_invoke cpp17_lib/invoke)
    set(___cpp_lib_map_insertion cpp17_lib/map_insertion)
    set(___cpp_lib_unordered_map_insertion cpp17_lib/map_insertion)
    set(___cpp_lib_map_try_emplace cpp17_lib/map_insertion)
    set(___cpp_lib_unordered_map_try_emplace cpp17_lib/map_insertion)
    set(___cpp_lib_uncaught_exceptions cpp17_lib/uncaught_exceptions)
    set(___cpp_lib_void_t cpp17_lib/void_t)

    if(DEFINED _${feature})
        set(feature "${_${feature}}" PARENT_SCOPE)
    elseif(${feature} MATCHES "cxx_*")
        message(WARNING "no compatibility option for CMake feature ${feature}")
    elseif(${feature} MATCHES "__cpp_*")
        message(WARNING "no compatibility option for SD-6 feature ${feature}")
    endif()
endfunction()

# INTERNAL
# downloads the file for a feature
function(_comp_fetch_feature path feature)
    if(NOT EXISTS "${path}/${feature}.cmake")
        file(DOWNLOAD ${COMP_REMOTE_URL}${feature}.cmake
                     ${path}/${feature}.cmake
                     SHOW_PROGESS
                     STATUS status
                     LOG log)
        list(GET status 0 status_code)
        list(GET status 1 status_string)
        if(NOT status_code EQUAL 0)
            message(FATAL_ERROR "error downloading feature file ${feature}.cmake: ${status_string} - ${log}")
        endif()
    endif()
endfunction()

# INTERNAL
# writes the header and testing code, if needed
function(_comp_gen_files feature)
    get_filename_component(name "${feature}" NAME_WE)
    string(TOUPPER "${name}" macro_name)

    if (COMP_HAS_${macro_name})
        set(result "1")
    else()
        set(result "0")
    endif()

    set(headers ${headers} ${COMP_PREFIX}${macro_name}_HEADER="${COMP_INCLUDE_PATH}/${COMP_ID}/${name}.hpp" PARENT_SCOPE)
    file(WRITE ${COMP_INCLUDE_PATH}/${COMP_ID}/${name}.hpp
"// This file was autogenerated using foonathan/compatibility.
// See https://github.com/foonathan/compatibility for further information.
// Do not edit manually!

#ifndef COMP_${COMP_PREFIX}${macro_name}_HPP_INCLUDED
#define COMP_${COMP_PREFIX}${macro_name}_HPP_INCLUDED

#include <cstddef>

#define ${COMP_PREFIX}HAS_${macro_name} ${result}

${${name}_sd6_macro}
${${name}_requires}
${${name}_workaround}

#endif
")
    if(${name}_test_code)
        file(WRITE ${_COMP_TEST}/${name}.cpp
                "#define COMP_IN_PARENT_HEADER
                #include <cstddef>
                #include <comp/${name}.hpp>

                #include \"catch.hpp\"

                ${${name}_test_global}

                TEST_CASE(\"${name}\", \"\")
                {
                    ${${name}_test_code}
                }")
    endif()
endfunction()

# INTERNAL
# handles a feature file
macro(_comp_handle_feature feature)
    _comp_translate_feature(${feature})
    _comp_fetch_feature(${COMP_CMAKE_PATH} ${feature})
    include(${COMP_CMAKE_PATH}/${feature}.cmake)
    _comp_gen_files(${feature})
endmacro()

# EXTERNAL; user
# setups certain features for a target
function(comp_target_features target include_policy)
    _comp_parse_arguments(${ARGN})

    # these variables are modified/accessed by the feature modules
    # deprecated
    set(cpp11_flag ${COMP_CPP11_FLAG})
    set(cpp14_flag ${COMP_CPP14_FLAG})
    set(cpp17_flag ${COMP_CPP17_FLAG})

    foreach(feature ${COMP_UNPARSED_ARGUMENTS})
        _comp_handle_feature(${feature})
    endforeach()
    target_include_directories(${target} ${include_policy} ${COMP_INCLUDE_PATH})
    target_compile_definitions(${target} ${include_policy} ${headers})

    if(COMP_NOFLAGS)
        return()
    endif()

    # first explicit option, then implicit; 17 over 14 over 11
    if(COMP_CPP17)
        target_compile_options(${target} PRIVATE ${COMP_CPP17_FLAG})
    elseif(COMP_CPP14)
        target_compile_options(${target} PRIVATE ${COMP_CPP14_FLAG})
    elseif(COMP_CPP11)
        target_compile_options(${target} PRIVATE ${COMP_CPP11_FLAG})
    elseif(need_COMP_CPP17_FLAG)
        target_compile_options(${target} PRIVATE ${COMP_CPP17_FLAG})
    elseif(need_COMP_CPP14_FLAG)
        target_compile_options(${target} PRIVATE ${COMP_CPP14_FLAG})
    elseif(need_COMP_CPP11_FLAG)
        target_compile_options(${target} PRIVATE ${COMP_CPP11_FLAG})
    endif()
endfunction()

# EXTERNAL; feature module
# checks for a feature with ${name} by compiling ${test_code}
# standard is COMP_CPPXX_FLAG and will be used for testing
# additional arguments are required other features, if they are not supported, it will be neither
function(comp_feature name test_code standard)
    string(TOUPPER "${name}" macro_name)
    message(STATUS "Checking for feature ${name}")

    if(_COMP_TEST_WORKAROUND)
        set(COMP_HAS_${macro_name} OFF CACHE INTERNAL "" FORCE)
    elseif(DEFINED COMP_HAS_${macro_name})
        message(STATUS "Checking for feature ${name} - overriden")
        if(COMP_HAS_${macro_name})
            set(need_${standard} TRUE PARENT_SCOPE)
        endif()
    else()
        set(result ON)
        foreach(feature ${ARGN})
            _comp_handle_feature(${feature})
            get_filename_component(cur_name "${feature}" NAME_WE)
            string(TOUPPER "${cur_name}" cur_name)
            if(NOT COMP_HAS_${cur_name})
                set(result OFF)
                message(STATUS "Checking for feature ${name} - Requirement failure: ${feature}")
            endif()
        endforeach()

        if(result)
            set(CMAKE_REQUIRED_FLAGS "${${standard}}")
            set(CMAKE_REQUIRED_QUIET ON)
            check_cxx_source_compiles("${test_code}" has_${name})

            if(has_${name})
                option(COMP_HAS_${macro_name} "whether or not ${name} is available" ON)
                set(need_${standard} TRUE PARENT_SCOPE)
                message(STATUS "Checking for feature ${name} - Success")
            else()
                option(COMP_HAS_${macro_name} "whether or not ${name} is available" OFF)
                message(STATUS "Checking for feature ${name} - Failed")
            endif()
        else()
            option(COMP_HAS_${macro_name} "whether or not ${name} is available" OFF)
        endif()
    endif()
endfunction()

# EXTERNAL; feature module
# writes workaround code
# test result is available via macro ${COMP_PREFIX}HAS_${name in uppercase}
# standard is COMP_CPPXX_FLAG required for the workaround code
# if the test succeds, the standard of the test is also activated
# additional arguments are required other features, their headers are also included then
function(comp_workaround name workaround standard)
    set(${name}_workaround "${workaround}" PARENT_SCOPE)
    set(need_${standard} TRUE PARENT_SCOPE)
    set(requires "")
    foreach(feature ${ARGN})
        get_filename_component(header "${feature}" NAME_WE)
        set(requires "${requires}#include \"${header}.hpp\"\n")
        _comp_handle_feature(${feature})
    endforeach()
    set(${name}_requires ${requires} PARENT_SCOPE)
    set(headers "${headers}" PARENT_SCOPE)
endfunction()

# EXTERNAL; feature module
# generates a unit test file for workaround of feature ${name}
# the include for the feature is available as is the Catch library
# ${code} will be placed inside a Catch TEST_CASE, ${global} in the global scope in front of it
function(comp_unit_test name global code)
    if (NOT _COMP_TEST)
        return()
    endif()
    set(${name}_test_code "${code}" PARENT_SCOPE)
    set(${name}_test_global "${global}" PARENT_SCOPE)
endfunction()

# EXTERNAL; feature module
# writes SD-6 feature macro with given name and value
# overrides existing value if given one is greater or macro COMP_OVERRIDE_SD6 is defined
function(comp_sd6_macro name sd6_name value)
    string(TOUPPER "${name}" macro_name)

    set(${name}_sd6_macro
"${${name}_sd6_macro}
#if ${COMP_PREFIX}HAS_${macro_name}
    #if !defined(${sd6_name})
        #define ${sd6_name} ${value}
    #elif ${value} > ${sd6_name}
        #undef ${sd6_name}
        #define ${sd6_name} ${value}
    #elif defined(COMP_OVERRIDE_SD6)
        #undef ${sd6_name}
        #define ${sd6_name} ${value}
    #endif
#endif" PARENT_SCOPE)
endfunction()

# EXTERNAL; umbrella feature module
# downloads and includes a feature named ${feature}
function(comp_fetch_include feature)
    _comp_fetch_feature(${COMP_CMAKE_PATH} ${feature})
    include(${COMP_CMAKE_PATH}/${feature}.cmake)
endfunction()

# DEPRECATED, use comp_workaround
macro(comp_gen_header name workaround)
    message(AUTHOR_WARNING "deprecated, use comp_workaround()")
    comp_workaround("${name}" "${workaround}" COMP_CPP98_FLAG)
endmacro()

# DEPRECATED, use comp_feature()
macro(comp_check_feature code name)
    message(AUTHOR_WARNING "deprecated, use comp_feature()")
    string(FIND "${ARGN}" "${cpp17_flag}" res)
    if (NOT (res EQUAL -1))
        comp_feature(${name} ${code} COMP_CPP17_FLAG)
    else()
        string(FIND "${ARGN}" "${cpp14_flag}" res)
        if(NOT (res EQUAL -1))
            comp_feature(${name} ${code} COMP_CPP14_FLAG)
        else()
            string(FIND "${ARGN}" "${cpp11_flag}" res)
            if(NOT (res EQUAL -1))
                comp_feature(${name} ${code} COMP_CPP11_FLAG)
            else()
                comp_feature(${name} ${code} COMP_CPP98_FLAG)
            endif()
        endif()
    endif()
endmacro()
