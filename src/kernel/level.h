/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <algorithm>
#include <utility>
#include "util/name.h"
#include "util/optional.h"
#include "util/list.h"
#include "util/sexpr/format.h"
#include "util/sexpr/options.h"

namespace lean {
class environment;
struct level_cell;
/**
   \brief Universe level kinds.

   - Zero         : It is also Prop level if env.impredicative() is true
   - Succ(l)      : successor level
   - Max(l1, l2)  : maximum of two levels
   - IMax(l1, l2) : IMax(x, zero)    = zero             for all x
                    IMax(x, succ(y)) = Max(x, succ(y))  for all x, y

                    We use IMax to handle Pi-types, and Max for Sigma-types.
                    Their definitions "mirror" the typing rules for Pi and Sigma.

   - Param(n)     : A parameter. In Lean, we have universe polymorphic definitions.
   - Meta(n)      : Placeholder. It is the equivalent of a metavariable for universe levels.
                    The elaborator is responsible for replacing Meta with level expressions
                    that do not contain Meta.
*/
enum class level_kind { Zero, Succ, Max, IMax, Param, Meta };

/**
   \brief Universe level.
*/
class level {
    friend class environment;
    level_cell * m_ptr;
    friend level_cell const & to_cell(level const & l);
    friend class optional<level>;
public:
    /** \brief Universe zero */
    level();
    level(level_cell * ptr);
    level(level const & l);
    level(level&& s);
    ~level();

    level_kind kind() const;
    unsigned hash() const;

    level & operator=(level const & l);
    level & operator=(level&& l);

    friend bool is_eqp(level const & l1, level const & l2) { return l1.m_ptr == l2.m_ptr; }

    friend void swap(level & l1, level & l2) { std::swap(l1, l2); }

    struct ptr_hash { unsigned operator()(level const & n) const { return std::hash<level_cell*>()(n.m_ptr); } };
    struct ptr_eq { bool operator()(level const & n1, level const & n2) const { return n1.m_ptr == n2.m_ptr; } };
};

bool operator==(level const & l1, level const & l2);
inline bool operator!=(level const & l1, level const & l2) { return !operator==(l1, l2); }

struct level_hash { unsigned operator()(level const & n) const { return n.hash(); } };
struct level_eq { bool operator()(level const & n1, level const & n2) const { return n1 == n2; } };

SPECIALIZE_OPTIONAL_FOR_SMART_PTR(level)

inline optional<level> none_level() { return optional<level>(); }
inline optional<level> some_level(level const & e) { return optional<level>(e); }
inline optional<level> some_level(level && e) { return optional<level>(std::forward<level>(e)); }

bool enable_level_caching(bool f);
level cache(level const & l);
bool is_cached(level const & l);
void flush_level_cache();

level const & mk_level_zero();
level const & mk_level_one();
level mk_max(level const & l1, level const & l2);
level mk_imax(level const & l1, level const & l2);
level mk_succ(level const & l);
level mk_param_univ(name const & n);
level mk_meta_univ(name const & n);

/** \brief Convert (succ^k l) into (l, k). If l is not a succ, then return (l, 0) */
pair<level, unsigned> to_offset(level l);

inline unsigned hash(level const & l) { return l.hash(); }
inline level_kind kind(level const & l) { return l.kind(); }
inline bool is_zero(level const & l)   { return kind(l) == level_kind::Zero; }
inline bool is_param(level const & l)  { return kind(l) == level_kind::Param; }
inline bool is_meta(level const & l)   { return kind(l) == level_kind::Meta; }
inline bool is_succ(level const & l)   { return kind(l) == level_kind::Succ; }
inline bool is_max(level const & l)    { return kind(l) == level_kind::Max; }
inline bool is_imax(level const & l)   { return kind(l) == level_kind::IMax; }
bool is_one(level const & l);

unsigned get_depth(level const & l);

level const & max_lhs(level const & l);
level const & max_rhs(level const & l);
level const & imax_lhs(level const & l);
level const & imax_rhs(level const & l);
level const & succ_of(level const & l);
name const & param_id(level const & l);
name const & meta_id(level const & l);
name const & level_id(level const & l);
/**
   \brief Return true iff \c l is an explicit level.
   We say a level l is explicit iff
   1) l is zero OR
   2) l = succ(l') and l' is explicit
*/
bool is_explicit(level const & l);
/** \brief Convert an explicit universe into a unsigned integer.
    \pre is_explicit(l)
*/
unsigned to_explicit(level const & l);
/** \brief Return true iff \c l contains placeholder (aka meta parameters). */
bool has_meta(level const & l);
/** \brief Return true iff \c l contains parameters */
bool has_param(level const & l);

/**
   \brief Return a new level expression based on <tt>l == succ(arg)</tt>, where \c arg is replaced with
   \c new_arg.

   \pre is_succ(l)
*/
level update_succ(level const & l, level const & new_arg);
/**
   \brief Return a new level expression based on <tt>l == max(lhs, rhs)</tt>, where \c lhs is replaced with
   \c new_lhs and \c rhs is replaced with \c new_rhs.

   \pre is_max(l) || is_imax(l)
*/
level update_max(level const & l, level const & new_lhs, level const & new_rhs);

/**
   \brief Return true if lhs and rhs denote the same level.
   The check is done by normalization.
*/
bool is_equivalent(level const & lhs, level const & rhs);
/** \brief Return the given level expression normal form */
level normalize(level const & l);

/**
   \brief If the result is true, then forall assignments \c A that assigns all parameters and metavariables occuring
   in \c l1 and \l2, we have that the universe level l1[A] is bigger or equal to l2[A].

   \remark This function assumes l1 and l2 are normalized
*/
bool is_geq_core(level l1, level l2);

bool is_geq(level const & l1, level const & l2);


typedef list<level> levels;

bool has_meta(levels const & ls);
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

typedef list<name> level_param_names;

/** \brief If \c l contains a parameter that is not in \c ps, then return it. Otherwise, return none. */
optional<name> get_undef_param(level const & l, level_param_names const & ps);

/**
    \brief Instantiate the universe level parameters \c ps occurring in \c l with the levels \c ls.
    \pre length(ps) == length(ls)
*/
level instantiate(level const & l, level_param_names const & ps, levels const & ls);

/** \brief Printer for debugging purposes */
std::ostream & operator<<(std::ostream & out, level const & l);

/**
   \brief If the result is true, then forall assignments \c A that assigns all parameters and metavariables occuring
   in \c l, l[A] != zero.
*/
bool is_not_zero(level const & l);

/** \brief Pretty print the given level expression, unicode characters are used if \c unicode is \c true. */
format pp(level l, bool unicode, unsigned indent);
/** \brief Pretty print the given level expression using the given configuration options. */
format pp(level const & l, options const & opts = options());

/** \brief Pretty print lhs <= rhs, unicode characters are used if \c unicode is \c true. */
format pp(level const & lhs, level const & rhs, bool unicode, unsigned indent);
/** \brief Pretty print lhs <= rhs using the given configuration options. */
format pp(level const & lhs, level const & rhs, options const & opts = options());
/** \brief Convert a list of universe level parameter names into a list of levels. */
levels param_names_to_levels(level_param_names const & ps);

void initialize_level();
void finalize_level();
}
void print(lean::level const & l);
