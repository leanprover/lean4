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
#include "util/task.h"

namespace lean {
class corrupted_file_exception : public exception {
public:
    corrupted_file_exception(std::string const & fname);
};

struct module_name {
    name               m_name;
    optional<unsigned> m_relative;
    module_name() {}
    module_name(name const & n, unsigned k):m_name(n), m_relative(k) {}
    explicit module_name(name const & n):m_name(n) {}
};

struct modification;

using modification_list = std::vector<std::shared_ptr<modification const>>;
struct loaded_module {
    std::string m_module_name;
    std::vector<module_name> m_imports;
    modification_list m_modifications;
    task<bool> m_uses_sorry;

    task<environment> m_env;
};
using module_loader = std::function<std::shared_ptr<loaded_module const> (std::string const &, module_name const &)>;
module_loader mk_olean_loader(std::vector<std::string> const &);
module_loader mk_dummy_loader();

/** \brief Return the list of declarations performed in the current module */
list<name> const & get_curr_module_decl_names(environment const & env);
/** \brief Return the list of universes declared in the current module */
list<name> const & get_curr_module_univ_names(environment const & env);
/** \brief Return the list of modules directly imported by the current module */
std::vector<module_name> get_curr_module_imports(environment const & env);

/** \brief Return an environment based on \c env, where all modules in \c modules are imported.
    Modules included directly or indirectly by them are also imported.
    The environment \c env is usually an empty environment.
*/
environment
import_modules(environment const & env,
               std::string const & current_mod, std::vector<module_name> const & ref,
               module_loader const & mod_ldr);

using module_id = std::string;

struct import_error {
    module_id m_mod;
    module_name m_import;
    std::exception_ptr m_ex;
};
environment
import_modules(environment const & env,
               std::string const & current_mod, std::vector<module_name> const & ref,
               module_loader const & mod_ldr, buffer<import_error> & errors);

/** \brief Return the .olean file where decl_name was defined. The result is none if the declaration
    was not defined in an imported file. */
optional<std::string> get_decl_olean(environment const & env, name const & decl_name);

/** \brief Return position (line and column number) where the given declaration was defined. */
optional<pos_info> get_decl_pos_info(environment const & env, name const & decl_name);

/** \brief Associate the given position with the given declaration. The information is not saved on
    .olean files. We use this function for attaching position information to temporary functions. */
environment add_transient_decl_pos_info(environment const & env, name const & decl_name, pos_info const & pos);

/** \brief Store/Export module using \c env. */
loaded_module export_module(environment const & env, std::string const & mod_name);
void write_module(loaded_module const & mod, std::ostream & out);

std::shared_ptr<loaded_module const> cache_preimported_env(
        loaded_module &&, environment const & initial_env,
        std::function<module_loader()> const & mk_mod_ldr);

/** \brief Check whether we should try to load the given .olean file according to its header and Lean version. */
bool is_candidate_olean_file(std::string const & file_name);

struct olean_data {
    std::vector<module_name> m_imports;
    std::string m_serialized_modifications;
    bool m_uses_sorry;
};
olean_data parse_olean(std::istream & in, std::string const & file_name, bool check_hash = true);
modification_list parse_olean_modifications(std::string const & serialized_modifications, std::string const & file_name);
void import_module(modification_list const & modifications, std::string const & file_name, environment & env);

struct modification {
public:
    virtual ~modification() {}
    virtual const char * get_key() const = 0;
    virtual void perform(environment &) const = 0;
    virtual void serialize(serializer &) const = 0;
    virtual void get_task_dependencies(buffer<gtask> &) const {}

    // Used to check for sorrys.
    virtual void get_introduced_exprs(std::vector<task<expr>> &) const {}
};

#define LEAN_MODIFICATION(k) \
  static void init() { \
    register_module_object_reader(k, module_modification_reader(deserialize)); \
  } \
  static void finalize() {} \
  const char * get_key() const override { return k; }

using module_modification_reader = std::function<std::shared_ptr<modification const>(deserializer &)>;

/** \brief Register a module object reader. The key \c k is used to identify the class of objects
    that can be read by the given reader.
*/
void register_module_object_reader(std::string const & k, module_modification_reader && r);

namespace module {
/** \brief Add a function that should be invoked when the environment is exported.
    The key \c k identifies which module_object_reader should be used to deserialize the object
    when the module is imported.

    \see module_object_reader
*/
environment add(environment const & env, std::shared_ptr<modification const> const & modif);
environment add_and_perform(environment const & env, std::shared_ptr<modification const> const & modif);

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
