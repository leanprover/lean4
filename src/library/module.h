/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Leonardo de Moura, Gabriel Ebner, Sebastian Ullrich
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
#include "util/lean_path.h"

namespace lean {
struct modification;

using modification_list = std::vector<modification*>;

/** \brief A finished module. The in-memory representation of a .olean file. */
struct loaded_module {
    module_name m_name; // not serialized
    std::vector<module_name> m_imports;
    modification_list m_modifications;
};

/** \brief Return an environment based on \c env, where all modules in \c modules are imported.
    Modules included directly or indirectly by them are also imported.
    The environment \c env is usually an empty environment (but with the trust level set).
*/
environment
import_modules(environment const & env, std::vector<module_name> const & imports, search_path const & path);

/** \brief Store module using \c env. */
void write_module(environment const & env, module_name const & mod, std::string const & olean_fn);

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

using module_modification_reader = std::function<modification*(deserializer &)>;

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
environment add(environment const & env, modification * modif);
environment add_and_perform(environment const & env, modification * modif);

/** \brief Add the given declaration to the environment, and mark it to be exported. */
environment add(environment const & env, declaration const & d, bool check = true);
}
void initialize_module();
void finalize_module();
}
