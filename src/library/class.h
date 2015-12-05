/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/util.h"
namespace lean {
/** \brief Create type checker that treats classes as opaque constants */
type_checker_ptr mk_class_type_checker(environment const & env, name_generator && ngen, bool conservative);
/** \brief Add a new 'class' to the environment (if it is not already declared) */
environment add_class(environment const & env, name const & n, name const & ns, bool persistent);
/** \brief Add a new 'class instance' to the environment with default priority. */
environment add_instance(environment const & env, name const & n, name const & ns, bool persistent);
/** \brief Add a new 'class instance' to the environment. */
environment add_instance(environment const & env, name const & n, unsigned priority, name const & ns, bool persistent);
/** \brief Add a new 'class transitive instance' to the environment with default priority. */
environment add_trans_instance(environment const & env, name const & n, name const & ns, bool persistent);
/** \brief Add a new 'class transitive instance' to the environment. */
environment add_trans_instance(environment const & env, name const & n, unsigned priority, name const & ns, bool persistent);
/** \brief Return true iff \c c was declared with \c add_class. */
bool is_class(environment const & env, name const & c);
/** \brief Return true iff \c i was declared with \c add_instance. */
bool is_instance(environment const & env, name const & i);
/** \brief Return the set of active classes (as a predicate) for the given environment */
name_predicate mk_class_pred(environment const & env);
/** \brief Return the set of active instances (as a predicate) for the given environment */
name_predicate mk_instance_pred(environment const & env);
/** \brief Return true iff \c i is a derived transitive instance. */
bool is_derived_trans_instance(environment const & env, name const & i);
/** \brief Return the instances of the given class. */
list<name> get_class_instances(environment const & env, name const & c);
/** \brief Return instances from the transitive closure graph of instances added using add_trans_instance */
list<name> get_class_derived_trans_instances(environment const & env, name const & c);
/** \brief Return the classes in the given environment. */
void get_classes(environment const & env, buffer<name> & classes);
name get_class_name(environment const & env, expr const & e);

/** \brief Mark that multiple instances of class \c n must be explored. */
environment mark_multiple_instances(environment const & env, name const & n, name const & ns, bool persistent);
/** \brief Return true iff multiple instances of class \c n must be explored. */
bool try_multiple_instances(environment const & env, name const & n);

/** \brief Return true iff \c type is a class or Pi that produces a class. */
optional<name> is_ext_class(type_checker & tc, expr const & type);

/** \brief Return a list of instances of the class \c cls_name that occur in \c ctx */
list<expr> get_local_instances(type_checker & tc, list<expr> const & ctx, name const & cls_name);

void initialize_class();
void finalize_class();
}
