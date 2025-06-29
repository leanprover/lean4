/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/util.h"
#include "library/elab_environment.h"
namespace lean {
/** \brief Return true iff \c c was declared with \c add_class. */
bool is_class(elab_environment const & env, name const & c);
/** \brief Return true iff \c i was declared with \c add_instance. */
bool is_instance(elab_environment const & env, name const & i);

name const & get_anonymous_instance_prefix();
name mk_anonymous_inst_name(unsigned idx);
bool is_anonymous_inst_name(name const & n);

/** \brief Return true iff e is of the form `outParam a` */
bool is_class_out_param(expr const & e);

/** \brief Return true iff c is a type class that contains an `outParam` */
bool has_class_out_params(elab_environment const & env, name const & c);

void initialize_class();
void finalize_class();
}
