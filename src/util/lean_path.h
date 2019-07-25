/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura, Gabriel Ebner
*/
#pragma once
#include <string>
#include <vector>
#include "runtime/exception.h"
#include "util/name.h"
#include "util/path.h"

namespace lean {
class lean_file_not_found_exception : public exception {
    std::string m_fname;
public:
    lean_file_not_found_exception(std::string const & fname);
};

using search_path = std::vector<std::string>;

optional<search_path> get_lean_path_from_env();
search_path get_builtin_search_path();

#if !defined(LEAN_EMSCRIPTEN)
std::string get_exe_location();
#endif

/** \brief A module name is an absolute import path like 'init.lean.core'. We do not use actual absolute file paths
 * because we store module names in .olean files, which should not be completely system-specific.
 */
using module_name = name;

struct rel_module_name {
    optional<unsigned> m_updirs;
    module_name m_name;

    rel_module_name(unsigned int const & updirs, module_name const & name) : m_updirs(some(updirs)), m_name(name) {}
    explicit rel_module_name(module_name const & name) : m_name(name) {}
};

/** \brief Hierarchical names are converted into paths using the path separator. Example: foo.bar is converted into 'foo/bar.lean' */
std::string find_file(search_path const &, module_name const & mod_name);
std::string find_file(search_path const &, module_name const & mod_name, std::initializer_list<char const *> const & exts);

/** \brief \brief Similar to previous find_file, but if k is not none then search at the k-th parent of base. */
std::string find_file(search_path const &, std::string const & base, optional<unsigned> const & rel, module_name const & mod_name,
                      std::initializer_list<char const *> const & extensions);
std::string find_file(search_path const &, std::string const & base, optional<unsigned> const & k, module_name const & mod_name, char const * ext);

/** \brief Inverse function of \c find_file */
module_name module_name_of_file(search_path const &, std::string const & fname);

/** \brief Resolve path like '.instances' in 'library/init/data/list' to 'init.data.list.instances' */
module_name absolutize_module_name(search_path const &, std::string const & base, rel_module_name const & rel);

/** \brief Return true iff fname ends with ".lean" */
bool is_lean_file(std::string const & fname);
/** \brief Return true iff fname ends with ".olean" */
bool is_olean_file(std::string const & fname);

std::string olean_of_lean(std::string const & lean_fn);
}
