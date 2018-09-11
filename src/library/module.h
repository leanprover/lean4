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
#include "runtime/serializer.h"
#include "runtime/optional.h"
#include "library/io_state.h"
#include "kernel/environment.h"

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
};
using module_loader = std::function<std::shared_ptr<loaded_module const> (std::string const &, module_name const &)>;
module_loader mk_olean_loader(std::vector<std::string> const &);
module_loader mk_dummy_loader();

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

/** \brief Store/Export module using \c env. */
loaded_module export_module(environment const & env, std::string const & mod_name);
void write_module(loaded_module const & mod, std::ostream & out);

/** \brief Check whether we should try to load the given .olean file according to its header and Lean version. */
bool is_candidate_olean_file(std::string const & file_name);

struct olean_data {
    std::vector<module_name> m_imports;
    std::string m_serialized_modifications;
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
environment add(environment const & env, declaration const & d);
}
void initialize_module();
void finalize_module();
}
