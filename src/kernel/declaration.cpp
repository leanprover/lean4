/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/declaration.h"
#include "kernel/environment.h"
#include "kernel/for_each_fn.h"

namespace lean {
int compare(reducibility_hints const & h1, reducibility_hints const & h2) {
    if (h1.kind() == h2.kind()) {
        if (h1.kind() == reducibility_hints_kind::Regular) {
            if (h1.get_height() == h2.get_height())
                return 0; /* unfold both */
            else if (h1.get_height() > h2.get_height())
                return -1; /* unfold f1 */
            else
                return 1;  /* unfold f2 */
            return h1.get_height() > h2.get_height() ? -1 : 1;
        } else {
            return 0; /* reduce both */
        }
    } else {
        if (h1.kind() == reducibility_hints_kind::Opaque) {
            return 1; /* reduce f2 */
        } else if (h2.kind() == reducibility_hints_kind::Opaque) {
            return -1; /* reduce f1 */
        } else if (h1.kind() == reducibility_hints_kind::Abbreviation) {
            return -1; /* reduce f1 */
        } else if (h2.kind() == reducibility_hints_kind::Abbreviation) {
            return 1; /* reduce f2 */
        } else {
            lean_unreachable();
        }
    }
}

constant_val::constant_val(name const & n, level_param_names const & lparams, expr const & type):
    object_ref(mk_cnstr(0, n, lparams, type)) {
}

axiom_val::axiom_val(name const & n, level_param_names const & lparams, expr const & type, bool is_meta):
    object_ref(mk_cnstr(0, constant_val(n, lparams, type), 1)) {
    cnstr_set_scalar<unsigned char>(raw(), sizeof(object*), static_cast<unsigned char>(is_meta));
}

bool axiom_val::is_meta() const { return cnstr_scalar<unsigned char>(raw(), sizeof(object*)) != 0; }

definition_val::definition_val(name const & n, level_param_names const & lparams, expr const & type, expr const & val, reducibility_hints const & hints, bool is_meta):
    object_ref(mk_cnstr(0, constant_val(n, lparams, type), val, hints, 1)) {
    cnstr_set_scalar<unsigned char>(raw(), sizeof(object*)*3, static_cast<unsigned char>(is_meta));
}

bool definition_val::is_meta() const { return cnstr_scalar<unsigned char>(raw(), sizeof(object*)*3) != 0; }

theorem_val::theorem_val(name const & n, level_param_names const & lparams, expr const & type, expr const & val):
    object_ref(mk_cnstr(0, constant_val(n, lparams, type), val)) {
}

recursor_rule::recursor_rule(name const & cnstr, unsigned nfields, expr const & rhs):
    object_ref(mk_cnstr(0, cnstr, nat(nfields), rhs)) {
}

static unsigned inductive_scalar_offset() { return sizeof(object*)*6; }
static unsigned constructor_scalar_offset() { return sizeof(object*)*3; }
static unsigned recursor_scalar_offset() { return sizeof(object*)*7; }

bool inductive_val::is_rec() const { return (cnstr_scalar<unsigned char>(raw(), inductive_scalar_offset()) & 1) != 0; }
bool inductive_val::is_meta() const { return (cnstr_scalar<unsigned char>(raw(), inductive_scalar_offset()) & 2) != 0; }
bool constructor_val::is_meta() const { return cnstr_scalar<unsigned char>(raw(), constructor_scalar_offset()); }
bool recursor_val::is_k() const { return (cnstr_scalar<unsigned char>(raw(), recursor_scalar_offset()) & 1) != 0; }
bool recursor_val::is_meta() const { return (cnstr_scalar<unsigned char>(raw(), recursor_scalar_offset()) & 2) != 0; }

bool declaration::is_meta() const {
    switch (kind()) {
    case declaration_kind::Definition:       return to_definition_val().is_meta();
    case declaration_kind::Axiom:            return to_axiom_val().is_meta();
    case declaration_kind::Theorem:          return false;
    case declaration_kind::Inductive:        lean_unreachable(); // TODO(Leo):
    case declaration_kind::Quot:             return false;
    case declaration_kind::MutualDefinition: return true;
    }
    lean_unreachable();
}

bool use_meta(environment const & env, expr const & e) {
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (found) return false;
            if (is_constant(e)) {
                if (auto info = env.find(const_name(e))) {
                    if (info->is_meta()) {
                        found = true;
                        return false;
                    }
                }
            }
            return true;
        });
    return found;
}

static declaration * g_dummy = nullptr;
declaration::declaration():declaration(*g_dummy) {}

declaration mk_definition(name const & n, level_param_names const & params, expr const & t, expr const & v,
                          reducibility_hints const & h, bool meta) {
    return declaration(mk_cnstr(static_cast<unsigned>(declaration_kind::Definition), definition_val(n, params, t, v, h, meta)));
}

static unsigned get_max_height(environment const & env, expr const & v) {
    unsigned h = 0;
    for_each(v, [&](expr const & e, unsigned) {
            if (is_constant(e)) {
                auto d = env.find(const_name(e));
                if (d && d->get_hints().get_height() > h)
                    h = d->get_hints().get_height();
            }
            return true;
        });
    return h;
}

declaration mk_definition(environment const & env, name const & n, level_param_names const & params, expr const & t,
                          expr const & v, bool meta) {
    unsigned h = get_max_height(env, v);
    return mk_definition(n, params, t, v, reducibility_hints::mk_regular(h+1), meta);
}

declaration mk_theorem(name const & n, level_param_names const & params, expr const & t, expr const & v) {
    return declaration(mk_cnstr(static_cast<unsigned>(declaration_kind::Theorem), theorem_val(n, params, t, v)));
}

declaration mk_axiom(name const & n, level_param_names const & params, expr const & t, bool meta) {
    return declaration(mk_cnstr(static_cast<unsigned>(declaration_kind::Axiom), axiom_val(n, params, t, meta)));
}

declaration mk_definition_inferring_meta(environment const & env, name const & n, level_param_names const & params,
                                            expr const & t, expr const & v, reducibility_hints const & hints) {
    bool meta = use_meta(env, t) || use_meta(env, v);
    return mk_definition(n, params, t, v, hints, meta);
}

declaration mk_definition_inferring_meta(environment const & env, name const & n, level_param_names const & params,
                                         expr const & t, expr const & v) {
    bool meta  = use_meta(env, t) && use_meta(env, v);
    unsigned h = get_max_height(env, v);
    return mk_definition(n, params, t, v, reducibility_hints::mk_regular(h+1), meta);
}

declaration mk_axiom_inferring_meta(environment const & env, name const & n,
                                    level_param_names const & params, expr const & t) {
    return mk_axiom(n, params, t, use_meta(env, t));
}

declaration mk_quot_decl(name const & n) {
    inc(n.raw());
    return declaration(mk_cnstr(static_cast<unsigned>(declaration_kind::Quot), n.raw()));
}

inductive_type::inductive_type(name const & id, expr const & type, constructors const & cnstrs):
    object_ref(mk_cnstr(0, id, type, cnstrs)) {
}

static unsigned inductive_decl_scalar_offset() { return sizeof(object*)*3; }

declaration mk_inductive_decl(names const & lparams, nat const & nparams, inductive_types const & types, bool is_meta) {
    declaration r(mk_cnstr(static_cast<unsigned>(declaration_kind::Inductive), lparams, nparams, types, 1));
    cnstr_set_scalar<unsigned char>(r.raw(), inductive_decl_scalar_offset(), static_cast<unsigned char>(is_meta));
    return r;
}

bool inductive_decl::is_meta() const { return cnstr_scalar<unsigned char>(raw(), inductive_decl_scalar_offset()) != 0; }

// =======================================
// Constant info
constant_info::constant_info():constant_info(*g_dummy) {}

constant_info::constant_info(declaration const & d):object_ref(d.raw()) {
    lean_assert(d.is_definition() || d.is_theorem() || d.is_axiom());
    inc_ref(d.raw());
}

static reducibility_hints * g_opaque = nullptr;

reducibility_hints const & constant_info::get_hints() const {
    if (is_definition())
        return static_cast<reducibility_hints const &>(cnstr_obj_ref(to_val(), 2));
    else
        return *g_opaque;
}

bool constant_info::is_meta() const {
    switch (kind()) {
    case constant_info_kind::Axiom:       return to_axiom_val().is_meta();
    case constant_info_kind::Definition:  return to_definition_val().is_meta();
    case constant_info_kind::Theorem:     return false;
    case constant_info_kind::Inductive:   return false; // TODO(Leo): to_inductive_val().is_meta();
    case constant_info_kind::Quot:        return false;
    case constant_info_kind::Constructor: return false; // TODO(Leo): to_constructor_val().is_meta();
    case constant_info_kind::Recursor:    return false; // TODO(Leo): to_recursor_val().is_meta();
    }
    lean_unreachable();
}

void initialize_declaration() {
    g_opaque = new reducibility_hints(reducibility_hints::mk_opaque());
    g_dummy  = new declaration(mk_axiom(name(), level_param_names(), expr()));
}

void finalize_declaration() {
    delete g_dummy;
    delete g_opaque;
}
}
