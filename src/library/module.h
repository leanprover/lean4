/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <iostream>
#include <utility>
#include <vector>
#include "util/serializer.h"
#include "util/optional.h"
#include "kernel/pos_info_provider.h"
#include "kernel/inductive/inductive.h"
#include "library/io_state.h"
#include "library/task_queue.h"

namespace lean {
class corrupted_file_exception : public exception {
public:
    corrupted_file_exception(std::string const & fname);
};

struct module_name {
    name               m_name;
    optional<unsigned> m_relative;
};

struct loaded_module {
    std::string m_module_name;
    std::string m_obj_code;
    std::vector<task_result<expr>> m_delayed_proofs;
};
using module_loader = std::function<loaded_module(std::string const &, module_name const &)>;
module_loader mk_olean_loader();
module_loader mk_dummy_loader();

/** \brief Return the list of declarations performed in the current module */
list<name> const & get_curr_module_decl_names(environment const & env);
/** \brief Return the list of universes declared in the current module */
list<name> const & get_curr_module_univ_names(environment const & env);
/** \brief Return the list of modules directly imported by the current module */
list<module_name> get_curr_module_imports(environment const & env);

/** \brief Return an environment based on \c env, where all modules in \c modules are imported.
    Modules included directly or indirectly by them are also imported.
    The environment \c env is usually an empty environment.

    If \c keep_proofs is false, then the proof of the imported theorems is discarded after being
    checked. The idea is to save memory.
*/
environment
import_module(environment const & env,
              std::string const & current_mod, module_name const & ref,
              module_loader const & mod_ldr);

/** \brief Return the .olean file where decl_name was defined. The result is none if the declaration
    was not defined in an imported file. */
optional<std::string> get_decl_olean(environment const & env, name const & decl_name);

/** \brief Return position (line and column number) where the given declaration was defined. */
optional<pos_info> get_decl_pos_info(environment const & env, name const & decl_name);

/** \brief Associate the given position with the given declaration. The information is not saved on
    .olean files. We use this function for attaching position information to temporary functions. */
environment add_transient_decl_pos_info(environment const & env, name const & decl_name, pos_info const & pos);

/** \brief Store/Export module using \c env to the output stream \c out. */
void export_module(std::ostream & out, environment const & env);
std::vector<task_result<expr>> export_module_delayed(std::ostream & out, environment const & env);

std::pair<std::vector<module_name>, std::vector<char>> parse_olean(
        std::istream & in, std::string const & file_name, bool check_hash = true);
void import_module(std::vector<char> const & olean_code, std::string const & file_name, environment & env,
                   std::vector<task_result<expr>> const & delayed_proofs);

/** \brief A reader for importing data from a stream using deserializer \c d.
    There is one way to update the environment being constructed.
     1- Direct update it using \c env.
*/
typedef void (*module_object_reader)(deserializer & d, environment & env);

/** \brief Register a module object reader. The key \c k is used to identify the class of objects
    that can be read by the given reader.
*/
void register_module_object_reader(std::string const & k, module_object_reader r);

namespace module {
/** \brief Add a function that should be invoked when the environment is exported.
    The key \c k identifies which module_object_reader should be used to deserialize the object
    when the module is imported.

    \see module_object_reader
*/
environment add(environment const & env, std::string const & k, std::function<void(environment const &, serializer &)> const & writer);

/** \brief Add the global universe declaration to the environment, and mark it to be exported. */
environment add_universe(environment const & env, name const & l);

/** \brief Add the given declaration to the environment, and mark it to be exported. */
environment add(environment const & env, certified_declaration const & d);

/** \brief Return true iff \c n is a definition added to the current module using #module::add */
bool is_definition(environment const & env, name const & n);

/** \brief Add the given inductive declaration to the environment, and mark it to be exported. */
environment add_inductive(environment                       env,
                          inductive::inductive_decl const & decl,
                          bool                              is_trusted);

/** \brief The following function must be invoked to register the quotient type computation rules in the kernel. */
environment declare_quotient(environment const & env);

/* Auxiliary object for setting position information for module declarations.
   It affects module::add and module::add_inductive methods. */
class scope_pos_info {
public:
    scope_pos_info(pos_info const & pos_info);
    ~scope_pos_info();
};
}
void initialize_module();
void finalize_module();
}
