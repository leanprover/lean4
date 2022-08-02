/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <string>
#include <limits>
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
    reducibility_hints(b_obj_arg o, bool b):object_ref(o, b) {}
    explicit reducibility_hints(object * r):object_ref(r) {}
public:
    static reducibility_hints mk_opaque() { return reducibility_hints(box(static_cast<unsigned>(reducibility_hints_kind::Opaque))); }
    static reducibility_hints mk_abbreviation() { return reducibility_hints(box(static_cast<unsigned>(reducibility_hints_kind::Abbreviation))); }
    static reducibility_hints mk_regular(unsigned h);
    reducibility_hints_kind kind() const { return static_cast<reducibility_hints_kind>(obj_tag(raw())); }
    bool is_regular() const { return kind() == reducibility_hints_kind::Regular; }
    bool is_abbrev() const { return kind() == reducibility_hints_kind::Abbreviation; }
    unsigned get_height() const;
};

/** Given h1 and h2 the hints for definitions f1 and f2, then
    result is
    <  0 If f1 should be unfolded
    == 0 If f1 and f2 should be unfolded
    >  0 If f2 should be unfolded */
int compare(reducibility_hints const & h1, reducibility_hints const & h2);

/*
structure constant_val :=
(id : name) (lparams : list name) (type : expr)
*/
class constant_val : public object_ref {
public:
    constant_val(name const & n, names const & lparams, expr const & type);
    constant_val(constant_val const & other):object_ref(other) {}
    constant_val(constant_val && other):object_ref(other) {}
    constant_val & operator=(constant_val const & other) { object_ref::operator=(other); return *this; }
    constant_val & operator=(constant_val && other) { object_ref::operator=(other); return *this; }
    name const & get_name() const { return static_cast<name const &>(cnstr_get_ref(*this, 0)); }
    names const & get_lparams() const { return static_cast<names const &>(cnstr_get_ref(*this, 1)); }
    expr const & get_type() const { return static_cast<expr const &>(cnstr_get_ref(*this, 2)); }
};

/*
structure axiom_val extends constant_val :=
(is_unsafe : bool)
*/
class axiom_val : public object_ref {
public:
    axiom_val(name const & n, names const & lparams, expr const & type, bool is_unsafe);
    axiom_val(axiom_val const & other):object_ref(other) {}
    axiom_val(axiom_val && other):object_ref(other) {}
    axiom_val & operator=(axiom_val const & other) { object_ref::operator=(other); return *this; }
    axiom_val & operator=(axiom_val && other) { object_ref::operator=(other); return *this; }
    constant_val const & to_constant_val() const { return static_cast<constant_val const &>(cnstr_get_ref(*this, 0)); }
    name const & get_name() const { return to_constant_val().get_name(); }
    names const & get_lparams() const { return to_constant_val().get_lparams(); }
    expr const & get_type() const { return to_constant_val().get_type(); }
    bool is_unsafe() const;
};

enum class definition_safety { unsafe, safe, partial };

/*
structure definition_val extends constant_val :=
(value : expr) (hints : reducibility_hints) (is_unsafe : bool)
*/
class definition_val : public object_ref {
public:
    definition_val(name const & n, names const & lparams, expr const & type, expr const & val, reducibility_hints const & hints, definition_safety safety, names const & all);
    definition_val(definition_val const & other):object_ref(other) {}
    definition_val(definition_val && other):object_ref(other) {}
    definition_val & operator=(definition_val const & other) { object_ref::operator=(other); return *this; }
    definition_val & operator=(definition_val && other) { object_ref::operator=(other); return *this; }
    constant_val const & to_constant_val() const { return static_cast<constant_val const &>(cnstr_get_ref(*this, 0)); }
    name const & get_name() const { return to_constant_val().get_name(); }
    names const & get_lparams() const { return to_constant_val().get_lparams(); }
    expr const & get_type() const { return to_constant_val().get_type(); }
    expr const & get_value() const { return static_cast<expr const &>(cnstr_get_ref(*this, 1)); }
    reducibility_hints const & get_hints() const { return static_cast<reducibility_hints const &>(cnstr_get_ref(*this, 2)); }
    definition_safety get_safety() const;
    bool is_unsafe() const { return get_safety() == definition_safety::unsafe; }
};
typedef list_ref<definition_val> definition_vals;

/*
structure theorem_val extends constant_val :=
(value : task expr)
*/
class theorem_val : public object_ref {
public:
    theorem_val(name const & n, names const & lparams, expr const & type, expr const & val);
    theorem_val(theorem_val const & other):object_ref(other) {}
    theorem_val(theorem_val && other):object_ref(other) {}
    theorem_val & operator=(theorem_val const & other) { object_ref::operator=(other); return *this; }
    theorem_val & operator=(theorem_val && other) { object_ref::operator=(other); return *this; }
    constant_val const & to_constant_val() const { return static_cast<constant_val const &>(cnstr_get_ref(*this, 0)); }
    name const & get_name() const { return to_constant_val().get_name(); }
    names const & get_lparams() const { return to_constant_val().get_lparams(); }
    expr const & get_type() const { return to_constant_val().get_type(); }
    expr const & get_value() const { return static_cast<expr const &>(cnstr_get_ref(*this, 1)); }
};

/*
structure opaque_val extends constant_val :=
(value : expr)
*/
class opaque_val : public object_ref {
public:
    opaque_val(name const & n, names const & lparams, expr const & type, expr const & val, bool is_unsafe, names const & all);
    opaque_val(opaque_val const & other):object_ref(other) {}
    opaque_val(opaque_val && other):object_ref(other) {}
    opaque_val & operator=(opaque_val const & other) { object_ref::operator=(other); return *this; }
    opaque_val & operator=(opaque_val && other) { object_ref::operator=(other); return *this; }
    constant_val const & to_constant_val() const { return static_cast<constant_val const &>(cnstr_get_ref(*this, 0)); }
    name const & get_name() const { return to_constant_val().get_name(); }
    names const & get_lparams() const { return to_constant_val().get_lparams(); }
    expr const & get_type() const { return to_constant_val().get_type(); }
    expr const & get_value() const { return static_cast<expr const &>(cnstr_get_ref(*this, 1)); }
    bool is_unsafe() const;
};

/*
structure constructor :=
(id : name) (type : expr)
*/
typedef pair_ref<name, expr> constructor;
inline name const & constructor_name(constructor const & c) { return c.fst(); }
inline expr const & constructor_type(constructor const & c) { return c.snd(); }
typedef list_ref<constructor> constructors;

/**
structure inductive_type where
(id : name) (type : expr) (cnstrs : list constructor)
*/
class inductive_type : public object_ref {
public:
    inductive_type(name const & id, expr const & type, constructors const & cnstrs);
    inductive_type(inductive_type const & other):object_ref(other) {}
    inductive_type(inductive_type && other):object_ref(other) {}
    inductive_type & operator=(inductive_type const & other) { object_ref::operator=(other); return *this; }
    inductive_type & operator=(inductive_type && other) { object_ref::operator=(other); return *this; }
    name const & get_name() const { return static_cast<name const &>(cnstr_get_ref(*this, 0)); }
    expr const & get_type() const { return static_cast<expr const &>(cnstr_get_ref(*this, 1)); }
    constructors const & get_cnstrs() const { return static_cast<constructors const &>(cnstr_get_ref(*this, 2)); }
};
typedef list_ref<inductive_type> inductive_types;

/*
inductive declaration
| axiom_decl       (val : axiom_val)
| defn_decl        (val : definition_val)
| thm_decl         (val : theorem_val)
| opaque_decl      (val : opaque_val)
| quot_decl        (id : name)
| mutual_defn_decl (defns : list definition_val) -- All definitions must be marked as `unsafe`
| induct_decl      (lparams : list name) (nparams : nat) (types : list inductive_type) (is_unsafe : bool)
*/
enum class declaration_kind { Axiom, Definition, Theorem, Opaque, Quot, MutualDefinition, Inductive };
class declaration : public object_ref {
    object * get_val_obj() const { return cnstr_get(raw(), 0); }
    object_ref const & to_val() const { return cnstr_get_ref(*this, 0); }
public:
    declaration();
    declaration(declaration const & other):object_ref(other) {}
    declaration(declaration && other):object_ref(other) {}
    /* low-level constructors */
    explicit declaration(object * o):object_ref(o) {}
    explicit declaration(b_obj_arg o, bool b):object_ref(o, b) {}
    explicit declaration(object_ref const & o):object_ref(o) {}
    declaration_kind kind() const { return static_cast<declaration_kind>(obj_tag(raw())); }

    declaration & operator=(declaration const & other) { object_ref::operator=(other); return *this; }
    declaration & operator=(declaration && other) { object_ref::operator=(other); return *this; }

    friend bool is_eqp(declaration const & d1, declaration const & d2) { return d1.raw() == d2.raw(); }

    bool is_definition() const { return kind() == declaration_kind::Definition; }
    bool is_axiom() const { return kind() == declaration_kind::Axiom; }
    bool is_theorem() const { return kind() == declaration_kind::Theorem; }
    bool is_opaque() const { return kind() == declaration_kind::Opaque; }
    bool is_mutual() const { return kind() == declaration_kind::MutualDefinition; }
    bool is_inductive() const { return kind() == declaration_kind::Inductive; }
    bool is_unsafe() const;
    bool has_value() const { return is_theorem() || is_definition(); }

    axiom_val const & to_axiom_val() const { lean_assert(is_axiom()); return static_cast<axiom_val const &>(cnstr_get_ref(raw(), 0)); }
    definition_val const & to_definition_val() const { lean_assert(is_definition()); return static_cast<definition_val const &>(cnstr_get_ref(raw(), 0)); }
    theorem_val const & to_theorem_val() const { lean_assert(is_theorem()); return static_cast<theorem_val const &>(cnstr_get_ref(raw(), 0)); }
    opaque_val const & to_opaque_val() const { lean_assert(is_opaque()); return static_cast<opaque_val const &>(cnstr_get_ref(raw(), 0)); }
    definition_vals const & to_definition_vals() const { lean_assert(is_mutual()); return static_cast<definition_vals const &>(cnstr_get_ref(raw(), 0)); }
};

inline optional<declaration> none_declaration() { return optional<declaration>(); }
inline optional<declaration> some_declaration(declaration const & o) { return optional<declaration>(o); }
inline optional<declaration> some_declaration(declaration && o) { return optional<declaration>(std::forward<declaration>(o)); }

declaration mk_definition(name const & n, names const & lparams, expr const & t, expr const & v,
                          reducibility_hints const & hints, definition_safety safety = definition_safety::safe);
declaration mk_definition(environment const & env, name const & n, names const & lparams, expr const & t, expr const & v,
                          definition_safety safety = definition_safety::safe);
declaration mk_opaque(name const & n, names const & lparams, expr const & t, expr const & v, bool unsafe);
declaration mk_axiom(name const & n, names const & lparams, expr const & t, bool unsafe = false);
declaration mk_inductive_decl(names const & lparams, nat const & nparams, inductive_types const & types, bool is_unsafe);

/** \brief Similar to mk_definition but infer the value of unsafe flag.
    That is, set it to true if \c t or \c v contains a unsafe declaration. */
declaration mk_definition_inferring_unsafe(environment const & env, name const & n, names const & lparams,
                                         expr const & t, expr const & v, reducibility_hints const & hints);
declaration mk_definition_inferring_unsafe(environment const & env, name const & n, names const & lparams,
                                         expr const & t, expr const & v);
/** \brief Similar to mk_axiom but infer the value of unsafe flag.
    That is, set it to true if \c t or \c v contains a unsafe declaration. */
declaration mk_axiom_inferring_unsafe(environment const & env, name const & n,
                                    names const & lparams, expr const & t);

/** \brief View for manipulating declaration.induct_decl constructor.
    | induct_decl      (lparams : list name) (nparams : nat) (types : list inductive_type) (is_unsafe : bool) */
class inductive_decl : public object_ref {
public:
    inductive_decl(inductive_decl const & other):object_ref(other) {}
    inductive_decl(inductive_decl && other):object_ref(other) {}
    inductive_decl(declaration const & d):object_ref(d) { lean_assert(d.is_inductive()); }
    inductive_decl & operator=(inductive_decl const & other) { object_ref::operator=(other); return *this; }
    inductive_decl & operator=(inductive_decl && other) { object_ref::operator=(other); return *this; }
    names const & get_lparams() const { return static_cast<names const &>(cnstr_get_ref(raw(), 0)); }
    nat const & get_nparams() const { return static_cast<nat const &>(cnstr_get_ref(raw(), 1)); }
    inductive_types const & get_types() const { return static_cast<inductive_types const &>(cnstr_get_ref(raw(), 2)); }
    bool is_unsafe() const;
};

/*
structure inductive_val extends constant_val where
(nparams : nat)       -- Number of parameters
(nindices : nat)      -- Number of indices
(all : list name)     -- List of all (including this one) inductive datatypes in the mutual declaration containing this one
(cnstrs : list name)  -- List of all constructors for this inductive datatype
(is_rec : bool)       -- `tt` iff it is recursive
(is_unsafe : bool)
(is_reflexive : bool)
*/
class inductive_val : public object_ref {
public:
    inductive_val(name const & n, names const & lparams, expr const & type, unsigned nparams,
                  unsigned nindices, names const & all, names const & cnstrs, bool is_rec, bool is_unsafe, bool is_reflexive, bool is_nested);
    inductive_val(inductive_val const & other):object_ref(other) {}
    inductive_val(inductive_val && other):object_ref(other) {}
    inductive_val & operator=(inductive_val const & other) { object_ref::operator=(other); return *this; }
    inductive_val & operator=(inductive_val && other) { object_ref::operator=(other); return *this; }
    constant_val const & to_constant_val() const { return static_cast<constant_val const &>(cnstr_get_ref(*this, 0)); }
    unsigned get_nparams() const { return static_cast<nat const &>(cnstr_get_ref(*this, 1)).get_small_value(); }
    unsigned get_nindices() const { return static_cast<nat const &>(cnstr_get_ref(*this, 2)).get_small_value(); }
    names const & get_all() const { return static_cast<names const &>(cnstr_get_ref(*this, 3)); }
    names const & get_cnstrs() const { return static_cast<names const &>(cnstr_get_ref(*this, 4)); }
    unsigned get_ncnstrs() const { return length(get_cnstrs()); }
    bool is_rec() const;
    bool is_unsafe() const;
    bool is_reflexive() const;
    bool is_nested() const;
};

/*
structure constructor_val extends constant_val :=
(induct  : name)  -- Inductive type this constructor is a member of
(cidx    : nat)   -- Constructor index (i.e., position in the inductive declaration)
(nparams : nat)   -- Number of parameters in inductive datatype `induct`
(nfields : nat)   -- Number of fields (i.e., arity - nparams)
(is_unsafe : bool)
*/
class constructor_val : public object_ref {
public:
    constructor_val(name const & n, names const & lparams, expr const & type, name const & induct, unsigned cidx, unsigned nparams, unsigned nfields, bool is_unsafe);
    constructor_val(constructor_val const & other):object_ref(other) {}
    constructor_val(constructor_val && other):object_ref(other) {}
    constructor_val & operator=(constructor_val const & other) { object_ref::operator=(other); return *this; }
    constructor_val & operator=(constructor_val && other) { object_ref::operator=(other); return *this; }
    constant_val const & to_constant_val() const { return static_cast<constant_val const &>(cnstr_get_ref(*this, 0)); }
    name const & get_induct() const { return static_cast<name const &>(cnstr_get_ref(*this, 1)); }
    unsigned get_cidx() const { return static_cast<nat const &>(cnstr_get_ref(*this, 2)).get_small_value(); }
    unsigned get_nparams() const { return static_cast<nat const &>(cnstr_get_ref(*this, 3)).get_small_value(); }
    unsigned get_nfields() const { return static_cast<nat const &>(cnstr_get_ref(*this, 4)).get_small_value(); }
    bool is_unsafe() const;
};

/*
structure recursor_rule :=
(cnstr : name)  -- Reduction rule for this constructor
(nfields : nat) -- Number of fields (i.e., without counting inductive datatype parameters)
(rhs : expr)    -- Right hand side of the reduction rule
*/
class recursor_rule : public object_ref {
public:
    recursor_rule(name const & cnstr, unsigned nfields, expr const & rhs);
    recursor_rule(recursor_rule const & other):object_ref(other) {}
    recursor_rule(recursor_rule && other):object_ref(other) {}
    recursor_rule & operator=(recursor_rule const & other) { object_ref::operator=(other); return *this; }
    recursor_rule & operator=(recursor_rule && other) { object_ref::operator=(other); return *this; }
    name const & get_cnstr() const { return static_cast<name const &>(cnstr_get_ref(*this, 0)); }
    unsigned get_nfields() const { return static_cast<nat const &>(cnstr_get_ref(*this, 1)).get_small_value(); }
    expr const & get_rhs() const { return static_cast<expr const &>(cnstr_get_ref(*this, 2)); }
};

typedef list_ref<recursor_rule> recursor_rules;

/*
structure recursor_val extends constant_val :=
(all : list name)            -- List of all inductive datatypes in the mutual declaration that generated this recursor
(nparams : nat)              -- Number of parameters
(nindices : nat)             -- Number of indices
(nmotives : nat)             -- Number of motives
(nminors : nat)              -- Number of minor premises
(rules : list recursor_rule) -- A reduction for each constructor
(k : bool)                   -- It supports K-like reduction
(is_unsafe : bool)
*/
class recursor_val : public object_ref {
public:
    recursor_val(name const & n, names const & lparams, expr const & type,
                 names const & all, unsigned nparams, unsigned nindices, unsigned nmotives,
                 unsigned nminors, recursor_rules const & rules, bool k, bool is_unsafe);
    recursor_val(recursor_val const & other):object_ref(other) {}
    recursor_val(recursor_val && other):object_ref(other) {}
    recursor_val & operator=(recursor_val const & other) { object_ref::operator=(other); return *this; }
    recursor_val & operator=(recursor_val && other) { object_ref::operator=(other); return *this; }
    constant_val const & to_constant_val() const { return static_cast<constant_val const &>(cnstr_get_ref(*this, 0)); }
    name const & get_name() const { return to_constant_val().get_name(); }
    name const & get_induct() const { return get_name().get_prefix(); }
    names const & get_all() const { return static_cast<names const &>(cnstr_get_ref(*this, 1)); }
    unsigned get_nparams() const { return static_cast<nat const &>(cnstr_get_ref(*this, 2)).get_small_value(); }
    unsigned get_nindices() const { return static_cast<nat const &>(cnstr_get_ref(*this, 3)).get_small_value(); }
    unsigned get_nmotives() const { return static_cast<nat const &>(cnstr_get_ref(*this, 4)).get_small_value(); }
    unsigned get_nminors() const { return static_cast<nat const &>(cnstr_get_ref(*this, 5)).get_small_value(); }
    unsigned get_major_idx() const { return get_nparams() + get_nmotives() + get_nminors() + get_nindices(); }
    recursor_rules const & get_rules() const { return static_cast<recursor_rules const &>(cnstr_get_ref(*this, 6)); }
    bool is_k() const;
    bool is_unsafe() const;
};

enum class quot_kind { Type, Mk, Lift, Ind };

/*
inductive quot_kind
| type  -- `quot`
| cnstr -- `quot.mk`
| lift  -- `quot.lift`
| ind   -- `quot.ind`

structure quot_val extends constant_val :=
(kind : quot_kind)
*/
class quot_val : public object_ref {
public:
    quot_val(name const & n, names const & lparams, expr const & type, quot_kind k);
    quot_val(quot_val const & other):object_ref(other) {}
    quot_val(quot_val && other):object_ref(other) {}
    quot_val & operator=(quot_val const & other) { object_ref::operator=(other); return *this; }
    quot_val & operator=(quot_val && other) { object_ref::operator=(other); return *this; }
    constant_val const & to_constant_val() const { return static_cast<constant_val const &>(cnstr_get_ref(*this, 0)); }
    name const & get_name() const { return to_constant_val().get_name(); }
    names const & get_lparams() const { return to_constant_val().get_lparams(); }
    expr const & get_type() const { return to_constant_val().get_type(); }
    quot_kind get_quot_kind() const;
};

/*
/-- Information associated with constant declarations. -/
inductive constant_info
| axiom_info    (val : axiom_val)
| defn_info     (val : definition_val)
| thm_info      (val : theorem_val)
| opaque_info   (val : opaque_val)
| quot_info     (val : quot_val)
| induct_info   (val : inductive_val)
| cnstr_info    (val : constructor_val)
| rec_info      (val : recursor_val)
*/
enum class constant_info_kind { Axiom, Definition, Theorem, Opaque, Quot, Inductive, Constructor, Recursor };
class constant_info : public object_ref {
    object * get_val_obj() const { return cnstr_get(raw(), 0); }
    object_ref const & to_val() const { return cnstr_get_ref(*this, 0); }
    constant_val const & to_constant_val() const { return static_cast<constant_val const &>(cnstr_get_ref(to_val(), 0)); }
public:
    constant_info();
    constant_info(declaration const & d);
    constant_info(definition_val const & v);
    constant_info(quot_val const & v);
    constant_info(inductive_val const & v);
    constant_info(constructor_val const & v);
    constant_info(recursor_val const & v);
    constant_info(constant_info const & other):object_ref(other) {}
    constant_info(constant_info && other):object_ref(other) {}
    explicit constant_info(b_obj_arg o, bool b):object_ref(o, b) {}
    explicit constant_info(obj_arg o):object_ref(o) {}

    constant_info_kind kind() const { return static_cast<constant_info_kind>(cnstr_tag(raw())); }

    constant_info & operator=(constant_info const & other) { object_ref::operator=(other); return *this; }
    constant_info & operator=(constant_info && other) { object_ref::operator=(other); return *this; }

    friend bool is_eqp(constant_info const & d1, constant_info const & d2) { return d1.raw() == d2.raw(); }

    bool is_unsafe() const;

    bool is_definition() const { return kind() == constant_info_kind::Definition; }
    bool is_axiom() const { return kind() == constant_info_kind::Axiom; }
    bool is_theorem() const { return kind() == constant_info_kind::Theorem; }
    bool is_opaque() const { return kind() == constant_info_kind::Opaque; }
    bool is_inductive() const { return kind() == constant_info_kind::Inductive; }
    bool is_constructor() const { return kind() == constant_info_kind::Constructor; }
    bool is_recursor() const { return kind() == constant_info_kind::Recursor; }
    bool is_quot() const { return kind() == constant_info_kind::Quot; }

    name const & get_name() const { return to_constant_val().get_name(); }
    names const & get_lparams() const { return to_constant_val().get_lparams(); }
    unsigned get_num_lparams() const { return length(get_lparams()); }
    expr const & get_type() const { return to_constant_val().get_type(); }
    bool has_value(bool allow_opaque = false) const {
        return is_theorem() || is_definition() || (allow_opaque && is_opaque());
    }
    reducibility_hints const & get_hints() const;

    axiom_val const & to_axiom_val() const { lean_assert(is_axiom()); return static_cast<axiom_val const &>(to_val()); }
    definition_val const & to_definition_val() const { lean_assert(is_definition()); return static_cast<definition_val const &>(to_val()); }
    theorem_val const & to_theorem_val() const { lean_assert(is_theorem()); return static_cast<theorem_val const &>(to_val()); }
    opaque_val const & to_opaque_val() const { lean_assert(is_opaque()); return static_cast<opaque_val const &>(to_val()); }
    inductive_val const & to_inductive_val() const { lean_assert(is_inductive()); return static_cast<inductive_val const &>(to_val()); }
    constructor_val const & to_constructor_val() const { lean_assert(is_constructor()); return static_cast<constructor_val const &>(to_val()); }
    recursor_val const & to_recursor_val() const { lean_assert(is_recursor()); return static_cast<recursor_val const &>(to_val()); }
    quot_val const & to_quot_val() const { lean_assert(is_quot()); return static_cast<quot_val const &>(to_val()); }

    expr get_value(bool DEBUG_CODE(allow_opaque)) const {
        lean_assert(has_value(allow_opaque));
        if (is_theorem())
            return to_theorem_val().get_value();
        else
            return static_cast<expr const &>(cnstr_get_ref(to_val(), 1));
    }
    expr get_value() const { return get_value(false); }
};

inline optional<constant_info> none_constant_info() { return optional<constant_info>(); }
inline optional<constant_info> some_constant_info(constant_info const & o) { return optional<constant_info>(o); }
inline optional<constant_info> some_constant_info(constant_info && o) { return optional<constant_info>(std::forward<constant_info>(o)); }

static_assert(static_cast<unsigned>(declaration_kind::Axiom) == static_cast<unsigned>(constant_info_kind::Axiom), "declaration vs constant_info tag mismatch");
static_assert(static_cast<unsigned>(declaration_kind::Definition) == static_cast<unsigned>(constant_info_kind::Definition), "declaration vs constant_info tag mismatch");
static_assert(static_cast<unsigned>(declaration_kind::Theorem) == static_cast<unsigned>(constant_info_kind::Theorem), "declaration vs constant_info tag mismatch");

void initialize_declaration();
void finalize_declaration();
}
