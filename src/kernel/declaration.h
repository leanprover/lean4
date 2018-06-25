/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <string>
#include <limits>
#include "util/rc.h"
#include "kernel/expr.h"

namespace lean {
/**
inductive reducibility_hints
| opaque  : reducibility_hints
| abbrev  : reducibility_hints
| regular : nat → reducibility_hints

Reducibility hints are used in the convertibility checker (aka is_def_eq predicate),
whenever checking a constraint such as

           (f ...) =?= (g ...)

where f and g are definitions, and the checker has to decide which one will be unfolded.
If f (g) is Opaque,             then g (f) is unfolded if it is also not marked as Opaque.
Else if f (g) is Abbreviation,  then f (g) is unfolded if g (f) is also not marked as Abbreviation.
Else if f and g are Regular,    then we unfold the one with the biggest definitional height.
Otherwise unfold both.

The definitional height is by default computed by the kernel. It only takes into account
other Regular definitions used in a definition.

Remark: the hint only affects performance. */
enum class reducibility_hints_kind { Opaque, Abbreviation, Regular };
class reducibility_hints : public object_ref {
    explicit reducibility_hints(object * r):object_ref(r) {}
public:
    static reducibility_hints mk_opaque() { return reducibility_hints(box(static_cast<unsigned>(reducibility_hints_kind::Opaque))); }
    static reducibility_hints mk_abbreviation() { return reducibility_hints(box(static_cast<unsigned>(reducibility_hints_kind::Abbreviation))); }
    static reducibility_hints mk_regular(unsigned h) {
        object * r = alloc_cnstr(static_cast<unsigned>(reducibility_hints_kind::Regular), 0, sizeof(unsigned));
        cnstr_set_scalar<unsigned>(r, 0, h);
        return reducibility_hints(r);
    }
    reducibility_hints_kind kind() const { return static_cast<reducibility_hints_kind>(obj_tag(raw())); }
    bool is_regular() const { return kind() == reducibility_hints_kind::Regular; }
    unsigned get_height() const { return is_regular() ? cnstr_scalar<unsigned>(raw(), 0) : 0; }
    void serialize(serializer & s) const { s.write_object(raw()); }
    static reducibility_hints deserialize(deserializer & d) { object * o = d.read_object(); inc(o); return reducibility_hints(o); }
};

inline serializer & operator<<(serializer & s, reducibility_hints const & l) { l.serialize(s); return s; }
inline reducibility_hints read_reducibility_hints(deserializer & d) { return reducibility_hints::deserialize(d); }
inline deserializer & operator>>(deserializer & d, reducibility_hints & l) { l = read_reducibility_hints(d); return d; }

/** Given h1 and h2 the hints for definitions f1 and f2, then
    result is
    <  0 If f1 should be unfolded
    == 0 If f1 and f2 should be unfolded
    >  0 If f2 should be unfolded */
int compare(reducibility_hints const & h1, reducibility_hints const & h2);


/**

inductive declaration
| const_decl  (val : constant_val)
| defn_decl   (val : definition_val)
| axiom_decl  (val : axiom_val)
| thm_decl    (val : theorem_val)
| induct_decl (val : inductive_val)
| cnstr_decl  (val : constructor_val)
| rec_decl    (val : recursor_val)

*/
enum class declaration_kind { Constant, Definition, Axiom, Theorem, Inductive, Constructor, Recursor };
class declaration : public object_ref {
    explicit declaration(object * o):object_ref(o) {}
    explicit declaration(object_ref const & o):object_ref(o) {}
    static object * mk_declaration_val(name const & n, level_param_names const & params, expr const & t);
    static object * mk_constant_val(name const & n, level_param_names const & params, expr const & t, bool meta);
    static object * mk_definition_val(name const & n, level_param_names const & params, expr const & t, expr const & v, reducibility_hints const & h, bool meta);
    static object * mk_axiom_val(name const & n, level_param_names const & params, expr const & t);
    static object * mk_theorem_val(name const & n, level_param_names const & params, expr const & t, expr const & v);
    object * get_val_obj() const { return cnstr_obj(raw(), 0); }
    object_ref const & get_val() const { return cnstr_obj_ref(*this, 0); }
    object_ref const & get_declaration_val() const { return (kind() == declaration_kind::Axiom) ? get_val() : cnstr_obj_ref(get_val(), 0); }
public:
    declaration();
    declaration(declaration const & other):object_ref(other) {}
    declaration(declaration && other):object_ref(other) {}
    declaration_kind kind() const { return static_cast<declaration_kind>(cnstr_tag(raw())); }

    declaration & operator=(declaration const & other) { object_ref::operator=(other); return *this; }
    declaration & operator=(declaration && other) { object_ref::operator=(other); return *this; }

    friend bool is_eqp(declaration const & d1, declaration const & d2) { return d1.raw() == d2.raw(); }

    bool is_constant_assumption() const { return kind() == declaration_kind::Constant; }
    bool is_definition() const { return kind() == declaration_kind::Definition; }
    bool is_axiom() const { return kind() == declaration_kind::Axiom; }
    bool is_theorem() const { return kind() == declaration_kind::Theorem; }
    bool is_meta() const;
    bool has_value() const { return is_theorem() || is_definition(); }

    name const & get_name() const { return static_cast<name const &>(cnstr_obj_ref(get_declaration_val(), 0)); }
    level_param_names const & get_univ_params() const { return static_cast<level_param_names const &>(cnstr_obj_ref(get_declaration_val(), 1)); }
    unsigned get_num_univ_params() const { return length(get_univ_params()); }
    expr const & get_type() const { return static_cast<expr const &>(cnstr_obj_ref(get_declaration_val(), 2)); }
    expr const & get_value() const { lean_assert(has_value()); return static_cast<expr const &>(cnstr_obj_ref(get_val(), 1)); }
    reducibility_hints const & get_hints() const;

    friend declaration mk_definition(name const & n, level_param_names const & params, expr const & t, expr const & v,
                                     reducibility_hints const & hints, bool meta);
    friend declaration mk_definition(environment const & env, name const & n, level_param_names const & params, expr const & t,
                                     expr const & v, bool meta);
    friend declaration mk_theorem(name const &, level_param_names const &, expr const &, expr const &);
    friend declaration mk_axiom(name const & n, level_param_names const & params, expr const & t);
    friend declaration mk_constant_assumption(name const & n, level_param_names const & params, expr const & t, bool meta);

    void serialize(serializer & s) const { s.write_object(raw()); }
    static declaration deserialize(deserializer & d) { object * o = d.read_object(); inc(o); return declaration(o); }
};

inline serializer & operator<<(serializer & s, declaration const & l) { l.serialize(s); return s; }
inline declaration read_declaration(deserializer & d) { return declaration::deserialize(d); }
inline deserializer & operator>>(deserializer & d, declaration & l) { l = read_declaration(d); return d; }

inline optional<declaration> none_declaration() { return optional<declaration>(); }
inline optional<declaration> some_declaration(declaration const & o) { return optional<declaration>(o); }
inline optional<declaration> some_declaration(declaration && o) { return optional<declaration>(std::forward<declaration>(o)); }

declaration mk_definition(name const & n, level_param_names const & params, expr const & t, expr const & v,
                          reducibility_hints const & hints, bool meta = false);
declaration mk_definition(environment const & env, name const & n, level_param_names const & params, expr const & t, expr const & v,
                          bool meta = false);
declaration mk_theorem(name const & n, level_param_names const & params, expr const & t, expr const & v);
declaration mk_theorem(name const & n, level_param_names const & params, expr const & t, expr const & v);
declaration mk_axiom(name const & n, level_param_names const & params, expr const & t);
declaration mk_constant_assumption(name const & n, level_param_names const & params, expr const & t, bool meta = false);

/** \brief Return true iff \c e depends on meta-declarations */
bool use_meta(environment const & env, expr const & e);

/** \brief Similar to mk_definition but infer the value of meta flag.
    That is, set it to true if \c t or \c v contains a meta declaration. */
declaration mk_definition_inferring_meta(environment const & env, name const & n, level_param_names const & params,
                                         expr const & t, expr const & v, reducibility_hints const & hints);
declaration mk_definition_inferring_meta(environment const & env, name const & n, level_param_names const & params,
                                         expr const & t, expr const & v);
/** \brief Similar to mk_constant_assumption but infer the value of meta flag.
    That is, set it to true if \c t or \c v contains a meta declaration. */
declaration mk_constant_assumption_inferring_meta(environment const & env, name const & n,
                                                  level_param_names const & params, expr const & t);

void initialize_declaration();
void finalize_declaration();
}
