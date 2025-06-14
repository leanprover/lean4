/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura, Gabriel Ebner
*/
#pragma once
#include <string>
#include <vector>
#include <ios>
#include "runtime/exception.h"
#include "runtime/optional.h"

namespace lean {
class file_not_found_exception : public exception {
    std::string m_fname;
public:
    file_not_found_exception(std::string const & fname);
};

#if !defined(LEAN_EMSCRIPTEN)
std::string get_exe_location();
#endif

char const * get_dir_sep();
char get_dir_sep_ch();
bool is_path_sep(char c);

std::string normalize_path(std::string f);

/** \brief Find all files with the given extension recursively. */
void find_files(std::string const & base, char const * ext, std::vector<std::string> & files);
bool has_file_ext(std::string const & fname, char const * ext);

std::string resolve(std::string const & rel_or_abs, std::string const & base);
std::string dirname(std::string const & fn);
/** \brief Get the file name without the extension. */
LEAN_EXPORT std::string stem(std::string const & fn);

LEAN_EXPORT std::string read_file(std::string const & fname, std::ios_base::openmode mode = std::ios_base::in);

bool is_directory(std::string const & fn);
optional<bool> is_dir(std::string const & fn);
std::vector<std::string> read_dir(std::string const & dirname);

time_t get_mtime(std::string const & fname);
}
