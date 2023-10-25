/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <algorithm>
#include <utility>
#include "runtime/optional.h"
#include "runtime/list_ref.h"
#include "util/name.h"
#include "util/options.h"

namespace lean {
class environment;
struct level_cell;
/**
inductive level
| zero   : level
| succ   : level → level
| max    : level → level → level
| imax   : level → level → level
| param  : name → level
| mvar   : name → level

We level.imax to handle Pi-types.
*/
enum class level_kind { Zero, Succ, Max, IMax, Param, MVar };

/** \brief Universe level. */
class level : public object_ref {
    friend level mk_succ(level const & l);
    friend level mk_max_core(level const & l1, level const & l2);
    friend level mk_imax_core(level const & l1, level const & l2);
    friend level mk_univ_param(name const & n);
    friend level mk_univ_mvar(name const & n);
    explicit level(object_ref && o):object_ref(o) {}
public:
    /** \brief Universe zero */
    level();
    explicit level(obj_arg o):object_ref(o) {}
    explicit level(b_obj_arg o, bool b):object_ref(o, b) {}
    level(level const & other):object_ref(other) {}
    level(level && other):object_ref(other) {}
    level_kind kind() const {
      return lean_is_scalar(raw()) ? level_kind::Zero : static_cast<level_kind>(lean_ptr_tag(raw()));
    }
    unsigned hash() const;

    level & operator=(level const & other) { object_ref::operator=(other); return *this; }
    level & operator=(level && other) { object_ref::operator=(other); return *this; }

    friend bool is_eqp(level const & l1, level const & l2) { return l1.raw() == l2.raw(); }

    bool is_zero() const { return kind() == level_kind::Zero; }
    bool is_succ() const { return kind() == level_kind::Succ; }
    bool is_max() const { return kind() == level_kind::Max; }
    bool is_imax() const { return kind() == level_kind::IMax; }
    bool is_param() const { return kind() == level_kind::Param; }
    bool is_mvar() const { return kind() == level_kind::MVar; }

    friend inline level const & max_lhs(level const & l) { lean_assert(l.is_max()); return static_cast<level const &>(cnstr_get_ref(l, 0)); }
    friend inline level const & max_rhs(level const & l) { lean_assert(l.is_max()); return static_cast<level const &>(cnstr_get_ref(l, 1)); }
    friend inline level const & imax_lhs(level const & l) { lean_assert(l.is_imax()); return static_cast<level const &>(cnstr_get_ref(l, 0)); }
    friend inline level const & imax_rhs(level const & l) { lean_assert(l.is_imax()); return static_cast<level const &>(cnstr_get_ref(l, 1)); }
    friend inline level const & level_lhs(level const & l) { lean_assert(l.is_max() || l.is_imax()); return static_cast<level const &>(cnstr_get_ref(l, 0)); }
    friend inline level const & level_rhs(level const & l) { lean_assert(l.is_max() || l.is_imax()); return static_cast<level const &>(cnstr_get_ref(l, 1)); }
    friend inline level const & succ_of(level const & l) { lean_assert(l.is_succ()); return static_cast<level const &>(cnstr_get_ref(l, 0)); }
    friend inline name const & param_id(level const & l) { lean_assert(l.is_param()); return static_cast<name const &>(cnstr_get_ref(l, 0)); }
    friend inline name const & mvar_id(level const & l)  { lean_assert(l.is_mvar()); return static_cast<name const &>(cnstr_get_ref(l, 0)); }
    friend inline name const & level_id(level const & l) { lean_assert(l.is_param() || l.is_mvar()); return static_cast<name const &>(cnstr_get_ref(l, 0)); }
};

typedef list_ref<level> levels;
typedef pair<level, level> level_pair;

bool operator==(level const & l1, level const & l2);
inline bool operator!=(level const & l1, level const & l2) { return !operator==(l1, l2); }

struct level_hash { unsigned operator()(level const & n) const { return n.hash(); } };
struct level_eq { bool operator()(level const & n1, level const & n2) const { return n1 == n2; } };

inline optional<level> none_level() { return optional<level>(); }
inline optional<level> some_level(level const & e) { return optional<level>(e); }
inline optional<level> some_level(level && e) { return optional<level>(std::forward<level>(e)); }

level const & mk_level_zero();
level const & mk_level_one();
level mk_max_core(level const & l1, level const & l2);
level mk_imax_core(level const & l1, level const & l2);
level mk_max(level const & l1, level const & l2);
level mk_imax(level const & l1, level const & l2);
level mk_succ(level const & l);
level mk_univ_param(name const & n);
level mk_univ_mvar(name const & n);

/** \brief Convert (succ^k l) into (l, k). If l is not a succ, then return (l, 0) */
pair<level, unsigned> to_offset(level l);

inline unsigned hash(level const & l) { return l.hash(); }
inline level_kind kind(level const & l) { return l.kind(); }
inline bool is_zero(level const & l)   { return l.is_zero(); }
inline bool is_param(level const & l)  { return l.is_param(); }
inline bool is_mvar(level const & l)   { return l.is_mvar(); }
inline bool is_succ(level const & l)   { return l.is_succ(); }
inline bool is_max(level const & l)    { return l.is_max(); }
inline bool is_imax(level const & l)   { return l.is_imax(); }
bool is_one(level const & l);

unsigned get_depth(level const & l);

/** \brief Return true iff \c l is an explicit level.
    We say a level l is explicit iff
    1) l is zero OR
    2) l = succ(l') and l' is explicit */
bool is_explicit(level const & l);
/** \brief Convert an explicit universe into a unsigned integer.
    \pre is_explicit(l) */
unsigned to_explicit(level const & l);
/** \brief Return true iff \c l contains placeholder (aka meta parameters). */
bool has_mvar(level const & l);
/** \brief Return true iff \c l contains parameters */
bool has_param(level const & l);

/** \brief Return a new level expression based on <tt>l == succ(arg)</tt>, where \c arg is replaced with
    \c new_arg.
    \pre is_succ(l) */
level update_succ(level const & l, level const & new_arg);
/** \brief Return a new level expression based on <tt>l == max(lhs, rhs)</tt>, where \c lhs is replaced with
    \c new_lhs and \c rhs is replaced with \c new_rhs.

    \pre is_max(l) || is_imax(l) */
level update_max(level const & l, level const & new_lhs, level const & new_rhs);

/** \brief Return true if lhs and rhs denote the same level.
    The check is done by normalization. */
bool is_equivalent(level const & lhs, level const & rhs);
/** \brief Return the given level expression normal form */
level normalize(level const & l);

/** \brief If the result is true, then forall assignments \c A that assigns all parameters and metavariables occurring
    in \c l1 and \l2, we have that the universe level l1[A] is bigger or equal to l2[A].

    \remark This function assumes l1 and l2 are normalized */
bool is_geq_core(level l1, level l2);

bool is_geq(level const & l1, level const & l2);

bool levels_has_mvar(object * ls);
bool has_mvar(levels const & ls);
bool levels_has_param(object * ls);
bool has_param(levels const & ls);

/** \brief An arbitrary (monotonic) total order on universe level terms. */
bool is_lt(level const & l1, level const & l2, bool use_hash);
bool is_lt(levels const & as, levels const & bs, bool use_hash);
struct level_quick_cmp { int operator()(level const & l1, level const & l2) const { return is_lt(l1, l2, true) ? -1 : (l1 == l2 ? 0 : 1); } };

/** \brief Functional for applying <tt>F</tt> to each level expressions. */
class for_each_level_fn {
    std::function<bool(level const &)>  m_f; // NOLINT
    void apply(level const & l);
public:
    template<typename F> for_each_level_fn(F const & f):m_f(f) {}
    void operator()(level const & l) { return apply(l); }
};
template<typename F> void for_each(level const & l, F const & f) { return for_each_level_fn(f)(l); }

/** \brief Functional for applying <tt>F</tt> to the level expressions. */
class replace_level_fn {
    std::function<optional<level>(level const &)>  m_f;
    level apply(level const & l);
public:
    template<typename F> replace_level_fn(F const & f):m_f(f) {}
    level operator()(level const & l) { return apply(l); }
};
template<typename F> level replace(level const & l, F const & f) { return replace_level_fn(f)(l); }

/** \brief Return true if \c u occurs in \c l */
bool occurs(level const & u, level const & l);

/** \brief If \c l contains a parameter that is not in \c ps, then return it. Otherwise, return none. */
optional<name> get_undef_param(level const & l, names const & lparams);

/** \brief Instantiate the universe level parameters \c ps occurring in \c l with the levels \c ls.
    \pre length(ps) == length(ls) */
level instantiate(level const & l, names const & ps, levels const & ls);

/** \brief Printer for debugging purposes */
std::ostream & operator<<(std::ostream & out, level const & l);

/** \brief If the result is true, then forall assignments \c A that assigns all parameters and metavariables occurring
    in \c l, l[A] != zero. */
bool is_not_zero(level const & l);

/** \brief Convert a list of universe level parameter names into a list of levels. */
levels lparams_to_levels(names const & ps);

void initialize_level();
void finalize_level();
}
void print(lean::level const & l);
