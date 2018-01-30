/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "frontends/lean/decl_attributes.h"
#include "frontends/lean/decl_util.h"
#include "frontends/lean/cmd_table.h"
namespace lean {
environment structure_cmd(parser & p, cmd_meta const & meta);
environment class_cmd(parser & p, cmd_meta const & meta);
buffer<name> get_structure_fields(environment const & env, name const & S);
void register_structure_cmd(cmd_table & r);
/** \brief Return true iff \c S is a structure created with the structure command */
bool is_structure(environment const & env, name const & S);
/** \brief Map argument name of structure intro rule to actual field name */
name deinternalize_field_name(name const & fname);
/** \brief If \c fname represents the relation to a parent structure \c S, return \c S */
optional<name> is_subobject_field(environment const & env, name const & S_name, name const & fname);
/** \brief Return immediate parent structures */
buffer<name> get_parent_structures(environment const & env, name const & S_name);
/** \brief If \c fname is defined in a parent \c S' of \c S_name, return S' */
optional<name> find_field(environment const & env, name const & S_name, name const & fname);
/** \brief If \c S_name is derived from \c base_S_name, return \c e casted to \c base_S_name */
optional<expr> mk_base_projections(environment const & env, name const & S_name, name const & base_S_name, expr const & e);
/** \brief Return an unelaborated expression applying a field projection */
expr mk_proj_app(environment const & env, name const & S_name, name const & fname, expr const & e, expr const & ref = {});

/* Default value support */
optional<name> has_default_value(environment const & env, name const & S_name, name const & fname);
expr mk_field_default_value(environment const & env, name const & full_field_name, std::function<expr(name const &)> const & get_field_value);
}
