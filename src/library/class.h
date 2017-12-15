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

/** \brief Return true iff e is of the form `out_param a` */
bool is_class_out_param(expr const & e);

/** \brief Return true iff c is a type class that contains an `out_param` */
bool has_class_out_params(environment const & env, name const & c);

/** \brief Add a new attribute for tracking symbols occurring in instances of type classes.

    We use this feature for tracking "algebraic" symbols.
    For example, the class is_commutative is marked with the [algebra] attribute
    registered with this procedure.
    Then, whenever we declarare an is_commutative instance, we store the symbols
    occuring in the application (is_commutative ...) in a set.

    \remark We ignore symbols occurring in types.

    For more details see:
    https://github.com/leanprover/lean/wiki/Refactoring-structures */
void register_class_symbol_tracking_attribute(name const & n, char const * descr);

/** \brief Return true iff \c n is the name of an attribute created with register_class_symbol_tracking_attribute. */
bool is_class_symbol_tracking_attribute(name const & n);

/** \brief Given an attribute created with register_class_symbol_tracking_attribute,
    this function returns the symbols that occur in instances of any class marked with the attribute. */
name_set get_class_attribute_symbols(environment const & env, name const & attr_name);

void initialize_class();
void finalize_class();
}
