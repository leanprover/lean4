/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/util.h"
namespace lean {
/** \brief Add a new 'class' to the environment (if it is not already declared) */
environment add_class(environment const &env, name const &n, bool persistent);
/** \brief Add a new 'class instance' to the environment. */
environment add_instance(environment const & env, name const & n, unsigned priority, bool persistent);
/** \brief Return true iff \c c was declared with \c add_class. */
bool is_class(environment const & env, name const & c);
/** \brief Return true iff \c i was declared with \c add_instance. */
bool is_instance(environment const & env, name const & i);
/** \brief Return the set of active classes (as a predicate) for the given environment */
name_predicate mk_class_pred(environment const & env);
/** \brief Return the set of active instances (as a predicate) for the given environment */
name_predicate mk_instance_pred(environment const & env);
/** \brief Return the instances of the given class. */
list<name> get_class_instances(environment const & env, name const & c);
/** \brief Return the classes in the given environment. */
void get_classes(environment const & env, buffer<name> & classes);
name get_class_name(environment const & env, expr const & e);

/** \brief Return name for attribute [instance] */
name const & get_instance_attr_name();
unsigned get_instance_fingerprint(environment const & env);

name const & get_anonymous_instance_prefix();
name mk_anonymous_inst_name(unsigned idx);
bool is_anonymous_inst_name(name const & n);

/** \brief Return true iff e is of the form (inout_param a) */
bool is_class_inout_param(expr const & e);

void initialize_class();
void finalize_class();
}
