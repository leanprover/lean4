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
/** Set .olean search path. This function is invoked during initialization. */
void set_search_path(search_path const & p);

/** \brief Return an environment where all modules in \c modules are imported.
    Modules included directly or indirectly by them are also imported.

    This procedure looks for imported files in the search path set using `set_search_path`. */
environment import_modules(unsigned trust_lvl, std::vector<module_name> const & imports);

/** \brief Store module using \c env. */
void write_module(environment const & env, std::string const & olean_fn);

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
}
void initialize_module();
void finalize_module();
}
