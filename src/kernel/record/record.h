/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <memory>
#include <utility>
#include "util/list.h"
#include "util/optional.h"
#include "kernel/environment.h"

namespace lean { namespace record {
typedef pair<name, expr> field;
inline name const & field_name(field const & f) { return f.first; }
inline expr const & field_type(field const & f) { return f.second; }

/** \brief Declare a record type. */
environment add_record(environment const &          env,
                       level_param_names const &    level_params,
                       name const &                 rec_name,
                       expr const &                 rec_type,
                       name const &                 intro_name,
                       expr const &                 intro_type);

/** \brief Normalizer extension for applying record computational rules. */
class record_normalizer_extension : public normalizer_extension {
public:
    virtual optional<expr> operator()(expr const & e, extension_context & ctx) const;
    virtual bool may_reduce_later(expr const & e, extension_context & ctx) const;
    virtual bool supports(name const & feature) const;
};

/** \brief If \c n is the name of a record in the environment \c env, then return the
    list of all fields. Return none otherwise
*/
optional<list<field>> is_record(environment const & env, name const & n);

/** \brief If \c n is the name of a record's field in \c env, then return the name of the record type
    associated with it.
*/
optional<name> is_field(environment const & env, name const & n);

/** \brief If \c n is the name of an introduction rule for a record in \c env, then return the name of the record type
    associated with it.
*/
optional<name> is_intro_rule(environment const & env, name const & n);

/** \brief If \c n is the name of an elimination rule for a record in \c env, then return the name of the record type
    associated with it.
*/
optional<name> is_elim_rule(environment const & env, name const & n);

/** \brief Given the eliminator \c n, this function return the position of major premise */
optional<unsigned> get_elim_major_idx(environment const & env, name const & n);
}}
