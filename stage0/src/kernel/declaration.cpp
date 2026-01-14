/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "kernel/declaration.h"
#include "kernel/environment.h"
#include "kernel/for_each_fn.h"

namespace lean {

extern "C" object * lean_mk_reducibility_hints_regular(uint32 h);
extern "C" uint32 lean_reducibility_hints_get_height(object * o);

reducibility_hints reducibility_hints::mk_regular(unsigned h) {
    return reducibility_hints(lean_mk_reducibility_hints_regular(h));
}

unsigned reducibility_hints::get_height() const {
    return lean_reducibility_hints_get_height(to_obj_arg());
}

int compare(reducibility_hints const & h1, reducibility_hints const & h2) {
    if (h1.kind() == h2.kind()) {
        if (h1.kind() == reducibility_hints_kind::Regular) {
            if (h1.get_height() == h2.get_height())
                return 0; /* unfold both */
            else if (h1.get_height() > h2.get_height())
                return -1; /* unfold f1 */
            else
                return 1;  /* unfold f2 */
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

constant_val::constant_val(name const & n, names const & lparams, expr const & type):
    object_ref(mk_cnstr(0, n, lparams, type)) {
}

extern "C" object * lean_mk_axiom_val(object * n, object * lparams, object * type, uint8 is_unsafe);
extern "C" uint8 lean_axiom_val_is_unsafe(object * v);

axiom_val::axiom_val(name const & n, names const & lparams, expr const & type, bool is_unsafe):
    object_ref(lean_mk_axiom_val(n.to_obj_arg(), lparams.to_obj_arg(), type.to_obj_arg(), is_unsafe)) {
}

bool axiom_val::is_unsafe() const { return lean_axiom_val_is_unsafe(to_obj_arg()); }

extern "C" object * lean_mk_definition_val(object * n, object * lparams, object * type, object * value, object * hints, uint8 safety, object * all);
extern "C" uint8 lean_definition_val_get_safety(object * v);

definition_val::definition_val(name const & n, names const & lparams, expr const & type, expr const & val, reducibility_hints const & hints, definition_safety safety, names const & all):
    object_ref(lean_mk_definition_val(n.to_obj_arg(), lparams.to_obj_arg(), type.to_obj_arg(), val.to_obj_arg(),
                                      hints.to_obj_arg(), static_cast<uint8>(safety), all.to_obj_arg())) {
}

definition_safety definition_val::get_safety() const { return static_cast<definition_safety>(lean_definition_val_get_safety(to_obj_arg())); }

extern "C" object * lean_mk_theorem_val(object * n, object * lparams, object * type, object * value, object * all);

theorem_val::theorem_val(name const & n, names const & lparams, expr const & type, expr const & val, names const & all):
    object_ref(lean_mk_theorem_val(n.to_obj_arg(), lparams.to_obj_arg(), type.to_obj_arg(), val.to_obj_arg(), all.to_obj_arg())) {
}

extern "C" object * lean_mk_opaque_val(object * n, object * lparams, object * type, object * value, uint8 is_unsafe, object * all);
extern "C" uint8 lean_opaque_val_is_unsafe(object * v);

opaque_val::opaque_val(name const & n, names const & lparams, expr const & type, expr const & val, bool is_unsafe, names const & all):
    object_ref(lean_mk_opaque_val(n.to_obj_arg(), lparams.to_obj_arg(), type.to_obj_arg(), val.to_obj_arg(), is_unsafe, all.to_obj_arg())) {
}

bool opaque_val::is_unsafe() const { return lean_opaque_val_is_unsafe(to_obj_arg()); }

extern "C" object * lean_mk_quot_val(object * n, object * lparams, object * type, uint8 k);
extern "C" uint8 lean_quot_val_kind(object * v);

quot_val::quot_val(name const & n, names const & lparams, expr const & type, quot_kind k):
    object_ref(lean_mk_quot_val(n.to_obj_arg(), lparams.to_obj_arg(), type.to_obj_arg(), static_cast<uint8>(k))) {
}

quot_kind quot_val::get_quot_kind() const { return static_cast<quot_kind>(lean_quot_val_kind(to_obj_arg())); }

recursor_rule::recursor_rule(name const & cnstr, unsigned nfields, expr const & rhs):
    object_ref(mk_cnstr(0, cnstr, nat(nfields), rhs)) {
}

extern "C" object * lean_mk_inductive_val(object * n, object * lparams, object * type, object * nparams, object * nindices,
                                          object * all, object * cnstrs, object * nnested, uint8 rec, uint8 unsafe, uint8 is_refl);
extern "C" uint8 lean_inductive_val_is_rec(object * v);
extern "C" uint8 lean_inductive_val_is_unsafe(object * v);
extern "C" uint8 lean_inductive_val_is_reflexive(object * v);

inductive_val::inductive_val(name const & n, names const & lparams, expr const & type, unsigned nparams,
                             unsigned nindices, names const & all, names const & cnstrs, unsigned nnested,
                             bool rec, bool unsafe, bool is_refl):
    object_ref(lean_mk_inductive_val(n.to_obj_arg(), lparams.to_obj_arg(), type.to_obj_arg(), nat(nparams).to_obj_arg(),
                                     nat(nindices).to_obj_arg(), all.to_obj_arg(), cnstrs.to_obj_arg(),
                                     nat(nnested).to_obj_arg(), rec, unsafe, is_refl)) {
}

bool inductive_val::is_rec() const { return lean_inductive_val_is_rec(to_obj_arg()); }
bool inductive_val::is_unsafe() const { return lean_inductive_val_is_unsafe(to_obj_arg()); }
bool inductive_val::is_reflexive() const { return lean_inductive_val_is_reflexive(to_obj_arg()); }

extern "C" object * lean_mk_constructor_val(object * n, object * lparams, object * type, object * induct,
                                            object * cidx, object * nparams, object * nfields, uint8 unsafe);
extern "C" uint8 lean_constructor_val_is_unsafe(object * v);

constructor_val::constructor_val(name const & n, names const & lparams, expr const & type, name const & induct, unsigned cidx, unsigned nparams, unsigned
                                 nfields, bool is_unsafe):
    object_ref(lean_mk_constructor_val(n.to_obj_arg(), lparams.to_obj_arg(), type.to_obj_arg(), induct.to_obj_arg(),
                                       nat(cidx).to_obj_arg(), nat(nparams).to_obj_arg(), nat(nfields).to_obj_arg(), is_unsafe)) {
}
bool constructor_val::is_unsafe() const { return lean_constructor_val_is_unsafe(to_obj_arg()); }

extern "C" object * lean_mk_recursor_val(object * n, object * lparams, object * type, object * all,
                                         object * nparams, object * nindices, object * nmotives, object * nminors,
                                         object * rules, uint8 k, uint8 unsafe);
extern "C" uint8 lean_recursor_k(object * v);
extern "C" uint8 lean_recursor_is_unsafe(object * v);

recursor_val::recursor_val(name const & n, names const & lparams, expr const & type,
                           names const & all, unsigned nparams, unsigned nindices, unsigned nmotives,
                           unsigned nminors, recursor_rules const & rules, bool k, bool is_unsafe):
    object_ref(lean_mk_recursor_val(n.to_obj_arg(), lparams.to_obj_arg(), type.to_obj_arg(), all.to_obj_arg(),
                                    nat(nparams).to_obj_arg(), nat(nindices).to_obj_arg(), nat(nmotives).to_obj_arg(),
                                    nat(nminors).to_obj_arg(), rules.to_obj_arg(), k, is_unsafe)) {
}

name const & recursor_val::get_major_induct() const {
    unsigned int n = get_major_idx();
    expr const * t = &(to_constant_val().get_type());
    for (unsigned int i = 0; i < n; i++) {
        t = &(binding_body(*t));
    }
    t = &(binding_domain(*t));
    t = &(get_app_fn(*t));
    return const_name(*t);
}


bool recursor_val::is_k() const { return lean_recursor_k(to_obj_arg()); }
bool recursor_val::is_unsafe() const { return lean_recursor_is_unsafe(to_obj_arg()); }

bool declaration::is_unsafe() const {
    switch (kind()) {
    case declaration_kind::Definition:       return to_definition_val().get_safety() == definition_safety::unsafe;
    case declaration_kind::Axiom:            return to_axiom_val().is_unsafe();
    case declaration_kind::Theorem:          return false;
    case declaration_kind::Opaque:           return to_opaque_val().is_unsafe();
    case declaration_kind::Inductive:        return inductive_decl(*this).is_unsafe();
    case declaration_kind::Quot:             return false;
    case declaration_kind::MutualDefinition: return true;
    }
    lean_unreachable();
}

bool use_unsafe(environment const & env, expr const & e) {
    bool found = false;
    for_each(e, [&](expr const & e) {
            if (found) return false;
            if (is_constant(e)) {
                if (auto info = env.find(const_name(e))) {
                    if (info->is_unsafe()) {
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

static unsigned get_max_height(environment const & env, expr const & v) {
    unsigned h = 0;
    for_each(v, [&](expr const & e) {
            if (is_constant(e)) {
                auto d = env.find(const_name(e));
                if (d && d->get_hints().get_height() > h)
                    h = d->get_hints().get_height();
            }
            return true;
        });
    return h;
}

definition_val mk_definition_val(environment const & env, name const & n, names const & params, expr const & t, expr const & v, definition_safety s) {
    unsigned h = get_max_height(env, v);
    return definition_val(n, params, t, v, reducibility_hints::mk_regular(h+1), s, names(n));
}

declaration mk_definition(name const & n, names const & params, expr const & t, expr const & v,
                          reducibility_hints const & h, definition_safety safety) {
    return declaration(mk_cnstr(static_cast<unsigned>(declaration_kind::Definition), definition_val(n, params, t, v, h, safety, names(n))));
}

declaration mk_definition(environment const & env, name const & n, names const & params, expr const & t,
                          expr const & v, definition_safety safety) {
    return declaration(mk_cnstr(static_cast<unsigned>(declaration_kind::Definition), mk_definition_val(env, n, params, t, v, safety)));
}

declaration mk_theorem(name const & n, names const & lparams, expr const & type, expr const & val) {
    return declaration(mk_cnstr(static_cast<unsigned>(declaration_kind::Theorem), theorem_val(n, lparams, type, val, names(n))));
}

declaration mk_opaque(name const & n, names const & params, expr const & t, expr const & v, bool is_unsafe) {
    return declaration(mk_cnstr(static_cast<unsigned>(declaration_kind::Opaque), opaque_val(n, params, t, v, is_unsafe, names(n))));
}

declaration mk_axiom(name const & n, names const & params, expr const & t, bool unsafe) {
    return declaration(mk_cnstr(static_cast<unsigned>(declaration_kind::Axiom), axiom_val(n, params, t, unsafe)));
}

static definition_safety to_safety(bool unsafe) {
    return unsafe ? definition_safety::unsafe : definition_safety::safe;
}

declaration mk_definition_inferring_unsafe(environment const & env, name const & n, names const & params,
                                            expr const & t, expr const & v, reducibility_hints const & hints) {
    bool unsafe = use_unsafe(env, t) || use_unsafe(env, v);
    return mk_definition(n, params, t, v, hints, to_safety(unsafe));
}

declaration mk_definition_inferring_unsafe(environment const & env, name const & n, names const & params,
                                         expr const & t, expr const & v) {
    bool unsafe  = use_unsafe(env, t) && use_unsafe(env, v);
    unsigned h = get_max_height(env, v);
    return mk_definition(n, params, t, v, reducibility_hints::mk_regular(h+1), to_safety(unsafe));
}

inductive_type::inductive_type(name const & id, expr const & type, constructors const & cnstrs):
    object_ref(mk_cnstr(0, id, type, cnstrs)) {
}

extern "C" object * lean_mk_inductive_decl(object * lparams, object * nparams, object * types, uint8 unsafe);
extern "C" uint8 lean_is_unsafe_inductive_decl(object * d);

declaration mk_inductive_decl(names const & lparams, nat const & nparams, inductive_types const & types, bool is_unsafe) {
    return declaration(lean_mk_inductive_decl(lparams.to_obj_arg(), nparams.to_obj_arg(), types.to_obj_arg(), is_unsafe));
}

bool inductive_decl::is_unsafe() const { return lean_is_unsafe_inductive_decl(to_obj_arg()); }

// =======================================
// Constant info
constant_info::constant_info():constant_info(*g_dummy) {}

constant_info::constant_info(declaration const & d):object_ref(d.raw()) {
    lean_assert(d.is_definition() || d.is_theorem() || d.is_axiom() || d.is_opaque());
    inc_ref(d.raw());
}

constant_info::constant_info(definition_val const & v):
    object_ref(mk_cnstr(static_cast<unsigned>(constant_info_kind::Definition), v)) {
}

constant_info::constant_info(quot_val const & v):
    object_ref(mk_cnstr(static_cast<unsigned>(constant_info_kind::Quot), v)) {
}

constant_info::constant_info(inductive_val const & v):
    object_ref(mk_cnstr(static_cast<unsigned>(constant_info_kind::Inductive), v)) {
}

constant_info::constant_info(constructor_val const & v):
    object_ref(mk_cnstr(static_cast<unsigned>(constant_info_kind::Constructor), v)) {
}

constant_info::constant_info(recursor_val const & v):
    object_ref(mk_cnstr(static_cast<unsigned>(constant_info_kind::Recursor), v)) {
}

static reducibility_hints * g_opaque = nullptr;

reducibility_hints const & constant_info::get_hints() const {
    if (is_definition())
        return static_cast<reducibility_hints const &>(cnstr_get_ref(to_val(), 2));
    else
        return *g_opaque;
}

bool constant_info::is_unsafe() const {
    switch (kind()) {
    case constant_info_kind::Axiom:       return to_axiom_val().is_unsafe();
    case constant_info_kind::Definition:  return to_definition_val().get_safety() == definition_safety::unsafe;
    case constant_info_kind::Theorem:     return false;
    case constant_info_kind::Opaque:      return to_opaque_val().is_unsafe();
    case constant_info_kind::Quot:        return false;
    case constant_info_kind::Inductive:   return to_inductive_val().is_unsafe();
    case constant_info_kind::Constructor: return to_constructor_val().is_unsafe();
    case constant_info_kind::Recursor:    return to_recursor_val().is_unsafe();
    }
    lean_unreachable();
}

void initialize_declaration() {
    g_opaque = new reducibility_hints(reducibility_hints::mk_opaque());
    mark_persistent(g_opaque->raw());
    g_dummy  = new declaration(mk_axiom(name(), names(), expr()));
    mark_persistent(g_dummy->raw());
}

void finalize_declaration() {
    delete g_dummy;
    delete g_opaque;
}
}
