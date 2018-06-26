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

recursor_rule::recursor_rule(name const & cnstr, unsigned nfields, expr const & rhs):
    object_ref(mk_cnstr(0, cnstr.raw(), mk_nat_obj(nfields), rhs.raw())) {
    inc(cnstr.raw());
    inc(rhs.raw());
}

static unsigned definition_scalar_offset() { return sizeof(object*)*3; }
static unsigned constant_scalar_offset() { return sizeof(object*); }
static unsigned inductive_scalar_offset() { return sizeof(object*)*6; }
static unsigned constructor_scalar_offset() { return sizeof(object*)*3; }
static unsigned recursor_scalar_offset() { return sizeof(object*)*7; }

bool inductive_val::is_rec() const { return (cnstr_scalar<unsigned char>(raw(), inductive_scalar_offset()) & 1) != 0; }
bool inductive_val::is_meta() const { return (cnstr_scalar<unsigned char>(raw(), inductive_scalar_offset()) & 2) != 0; }
bool constructor_val::is_meta() const { return cnstr_scalar<unsigned char>(raw(), constructor_scalar_offset()); }
bool recursor_val::is_k() const { return (cnstr_scalar<unsigned char>(raw(), recursor_scalar_offset()) & 1) != 0; }
bool recursor_val::is_meta() const { return (cnstr_scalar<unsigned char>(raw(), recursor_scalar_offset()) & 2) != 0; }

object * declaration::mk_declaration_val(name const & n, level_param_names const & params, expr const & t) {
    object * r = alloc_cnstr(0, 3, 0);
    inc(n.raw());      cnstr_set_obj(r, 0, n.raw());
    inc(params.raw()); cnstr_set_obj(r, 1, params.raw());
    inc(t.raw());      cnstr_set_obj(r, 2, t.raw());
    return r;
}

object * declaration::mk_constant_val(name const & n, level_param_names const & params, expr const & t, bool meta) {
    object * r = alloc_cnstr(0, 1, sizeof(unsigned char));
    cnstr_set_obj(r, 0, mk_declaration_val(n, params, t));
    cnstr_set_scalar<unsigned char>(r, constant_scalar_offset(), static_cast<unsigned char>(meta));
    return r;
}

object * declaration::mk_definition_val(name const & n, level_param_names const & params, expr const & t, expr const & v,
                                        reducibility_hints const & h, bool meta) {
    object * r = alloc_cnstr(0, 3, sizeof(unsigned char));
    cnstr_set_obj(r, 0, mk_declaration_val(n, params, t));
    inc(v.raw()); cnstr_set_obj(r, 1, v.raw());
    inc(h.raw()); cnstr_set_obj(r, 2, h.raw());
    cnstr_set_scalar<unsigned char>(r, definition_scalar_offset(), static_cast<unsigned char>(meta));
    return r;
}

object * declaration::mk_axiom_val(name const & n, level_param_names const & params, expr const & t) {
    return mk_declaration_val(n, params, t);
}

object * declaration::mk_theorem_val(name const & n, level_param_names const & params, expr const & t, expr const & v) {
    object * r = alloc_cnstr(0, 2, 0);
    cnstr_set_obj(r, 0, mk_declaration_val(n, params, t));
    inc(v.raw()); cnstr_set_obj(r, 1, v.raw());
    return r;
}

object * declaration::mk_inductive_val(name const & n, level_param_names const & params, expr const & t, unsigned nparams, unsigned nindices,
                                       names const & all, names const & cnstrs, names const & recs, bool is_rec, bool is_meta) {
    object * r = alloc_cnstr(0, 6, 1);
    cnstr_set_obj(r, 0, mk_declaration_val(n, params, t));
    cnstr_set_obj(r, 1, mk_nat_obj(nparams));
    cnstr_set_obj(r, 2, mk_nat_obj(nindices));
    inc(all.raw()); cnstr_set_obj(r, 3, all.raw());
    inc(cnstrs.raw()); cnstr_set_obj(r, 4, cnstrs.raw());
    inc(recs.raw()); cnstr_set_obj(r, 5, recs.raw());
    cnstr_set_scalar<unsigned char>(r, inductive_scalar_offset(), (is_rec ? 1 : 0) + (is_meta ? 2 : 0));
    return r;
}

object * declaration::mk_constructor_val(name const & n, level_param_names const & params, expr const & t, name const & induct, unsigned nparams,
                                         bool is_meta) {
    object * r = alloc_cnstr(0, 3, 1);
    cnstr_set_obj(r, 0, mk_declaration_val(n, params, t));
    inc(induct.raw()); cnstr_set_obj(r, 1, induct.raw());
    cnstr_set_obj(r, 2, mk_nat_obj(nparams));
    cnstr_set_scalar<unsigned char>(r, inductive_scalar_offset(), static_cast<unsigned char>(is_meta));
    return r;
}

object * declaration::mk_recursor_val(name const & n, level_param_names const & params, expr const & t, name const & induct, unsigned nparams,
                                      unsigned nindices, unsigned nmotives, unsigned nminor, bool k, recursor_rules const & rules, bool is_meta) {
    object * r = alloc_cnstr(0, 7, 1);
    cnstr_set_obj(r, 0, mk_declaration_val(n, params, t));
    cnstr_set_obj(r, 0, mk_declaration_val(n, params, t));
    inc(induct.raw()); cnstr_set_obj(r, 1, induct.raw());
    cnstr_set_obj(r, 2, mk_nat_obj(nparams));
    cnstr_set_obj(r, 3, mk_nat_obj(nindices));
    cnstr_set_obj(r, 4, mk_nat_obj(nmotives));
    cnstr_set_obj(r, 5, mk_nat_obj(nminor));
    inc(rules.raw()); cnstr_set_obj(r, 6, rules.raw());
    cnstr_set_scalar<unsigned char>(r, recursor_scalar_offset(), (k ? 1 : 0) + (is_meta ? 2 : 0));
    return r;
}

bool declaration::is_meta() const {
    switch (kind()) {
    case declaration_kind::Definition:  return cnstr_scalar<unsigned char>(get_val_obj(), definition_scalar_offset()) != 0;
    case declaration_kind::Constant:    return cnstr_scalar<unsigned char>(get_val_obj(), constant_scalar_offset()) != 0;
    case declaration_kind::Inductive:   return to_inductive_val().is_meta();
    case declaration_kind::Constructor: return to_constructor_val().is_meta();
    case declaration_kind::Recursor:    return to_recursor_val().is_meta();
    case declaration_kind::Axiom:       return false;
    case declaration_kind::Theorem:     return false;
    }
    lean_unreachable();
}

static reducibility_hints * g_opaque = nullptr;

reducibility_hints const & declaration::get_hints() const {
    if (is_definition())
        return static_cast<reducibility_hints const &>(cnstr_obj_ref(to_val(), 2));
    else
        return *g_opaque;
}

bool use_meta(environment const & env, expr const & e) {
    bool found = false;
    for_each(e, [&](expr const & e, unsigned) {
            if (found) return false;
            if (is_constant(e)) {
                if (auto d = env.find(const_name(e))) {
                    if (d->is_meta()) {
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
    return declaration(mk_cnstr(static_cast<unsigned>(declaration_kind::Definition), declaration::mk_definition_val(n, params, t, v, h, meta)));
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
    return declaration(mk_cnstr(static_cast<unsigned>(declaration_kind::Theorem), declaration::mk_theorem_val(n, params, t, v)));
}

declaration mk_axiom(name const & n, level_param_names const & params, expr const & t) {
    return declaration(mk_cnstr(static_cast<unsigned>(declaration_kind::Axiom), declaration::mk_axiom_val(n, params, t)));
}

declaration mk_constant_assumption(name const & n, level_param_names const & params, expr const & t, bool meta) {
    return declaration(mk_cnstr(static_cast<unsigned>(declaration_kind::Constant), declaration::mk_constant_val(n, params, t, meta)));
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

declaration mk_constant_assumption_inferring_meta(environment const & env, name const & n,
                                                  level_param_names const & params, expr const & t) {
    return mk_constant_assumption(n, params, t, use_meta(env, t));
}

declaration mk_inductive(name const & n, level_param_names const & params, expr const & t, unsigned nparams, unsigned nindices,
                         names const & all, names const & cnstrs, names const & recs, bool is_rec, bool is_meta) {
    return declaration(mk_cnstr(static_cast<unsigned>(declaration_kind::Inductive),
                                declaration::mk_inductive_val(n, params, t, nparams, nindices, all, cnstrs, recs, is_rec, is_meta)));
}

declaration mk_constructor(name const & n, level_param_names const & params, expr const & t, name const & induct, unsigned nparams, bool is_meta) {
    return declaration(mk_cnstr(static_cast<unsigned>(declaration_kind::Constructor), declaration::mk_constructor_val(n, params, t, induct, nparams, is_meta)));
}

declaration mk_recursor(name const & n, level_param_names const & params, expr const & t, name const & induct, unsigned nparams,
                        unsigned nindices, unsigned nmotives, unsigned nminor, bool k, recursor_rules const & rules, bool is_meta) {
    return declaration(mk_cnstr(static_cast<unsigned>(declaration_kind::Constructor),
                                declaration::mk_recursor_val(n, params, t, induct, nparams, nindices, nmotives, nminor, k, rules, is_meta)));
}

inductive_type::inductive_type(name const & id, expr const & type, constructors const & cnstrs):
    object_ref(mk_cnstr(0, id.raw(), type.raw(), cnstrs.raw())) {
    inc(id.raw()); inc(type.raw()); inc(cnstrs.raw());
}

static unsigned inductive_decl_scalar_offset() { return sizeof(object*)*3; }

inductive_decl::inductive_decl(names const & lparams, nat const & nparams, inductive_types const & types, bool is_meta):
    object_ref(mk_cnstr(0, lparams.raw(), nparams.raw(), types.raw(), sizeof(unsigned char))) {
    inc(lparams.raw()), inc(nparams.raw()); inc(types.raw());
    cnstr_set_scalar<unsigned char>(raw(), inductive_decl_scalar_offset(), static_cast<unsigned char>(is_meta));
}

bool inductive_decl::is_meta() const { return cnstr_scalar<unsigned char>(raw(), inductive_decl_scalar_offset()) != 0; }

void initialize_declaration() {
    g_opaque = new reducibility_hints(reducibility_hints::mk_opaque());
    g_dummy  = new declaration(mk_axiom(name(), level_param_names(), expr()));
}

void finalize_declaration() {
    delete g_dummy;
    delete g_opaque;
}
}
