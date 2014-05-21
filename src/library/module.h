/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include <iostream>
#include "util/serializer.h"
#include "library/shared_environment.h"

namespace lean {
/**
   \brief Return an environment based on \c env, where all modules in \c modules are imported.
   Modules included directly or indirectly by them are also imported.
   The environment \c env is usually an empty environment.
*/
environment import_modules(environment const & env, unsigned num_modules, std::string const * modules);
environment import_module(environment const & env, std::string const & module);

/**
   \brief Store/Export module using \c env to the output stream \c out.
*/
void export_module(std::ostream & out, environment const & env);

typedef std::function<environment(environment const & env)> update_env_fn;

/**
   \brief A reader for importing data from a stream using deserializer \c d.
   There are two way to update the environment being constructed.
   We can directly update it using \c senv, or we may register a delayed
   update using \c delayed_update. The delayed updates are executed using
   an order based on import order. The delayed updates are useful for
   objects such as rewrite rule sets where the order in which they are
   constructed matter.
*/
typedef void (*module_object_reader)(deserializer & d,
                                     shared_environment & senv,
                                     std::function<void(update_env_fn const &)> & delayed_update);

/**
   \brief Register a module object reader. The key \c k is used to identify the class of objects
   that can be read by the given reader.
*/
void register_module_object_reader(std::string const & k, module_object_reader r);

/** \brief Auxiliary class for registering module readers when the lean executable is loaded. */
struct register_module_object_reader_fn {
    register_module_object_reader_fn(std::string const & k, module_object_reader r) {
        register_module_object_reader(k, r);
    }
};

/**
    \brief Add a function that should be invoked when the environment is exported.
    The key \c k identifies which module_object_reader should be used to deserialize the object
    when the module is imported.

    \see module_object_reader
*/
environment add(environment const & env, std::string const & k, std::function<void(serializer &)> const & writer);

/** \brief Add the given declaration to the environment, and mark it to be exported. */
environment add(environment const & env, certified_declaration const & d);
}
