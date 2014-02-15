/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <algorithm>
#include "util/name.h"
#include "util/optional.h"
#include "util/serializer.h"
#include "util/sexpr/format.h"
#include "util/sexpr/options.h"

namespace lean {
class environment;
struct level_cell;
/**
   \brief Universe level kinds.

   - Zero         : Bool/Prop level. In Lean, Bool == (Type zero)
   - Succ(l)      : successor level
   - Max(l1, l2)  : maximum of two levels
   - IMax(l1, l2) : IMax(x, zero)    = zero             for all x
                    IMax(x, succ(y)) = Max(x, succ(y))  for all x, y

                    We use IMax to handle Pi-types, and Max for Sigma-types.
                    Their definitions "mirror" the typing rules for Pi and Sigma.

   - Param(i)     : A parameter. In Lean, we have universe polymorphic definitions.
   - Meta(i)      : Placeholder. It is the equivalent of a metavariable for universe levels.
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
public:
    /** \brief Universe zero */
    level();
    level(level_cell * ptr);
    level(level const & l);
    level(level&& s);
    ~level();

    level & operator=(level const & l);
    level & operator=(level&& l);

    friend bool is_eqp(level const & l1, level const & l2) { return l1.m_ptr == l2.m_ptr; }

    friend void swap(level & l1, level & l2) { std::swap(l1, l2); }

    struct ptr_hash { unsigned operator()(level const & n) const { return std::hash<level_cell*>()(n.m_ptr); } };
    struct ptr_eq { bool operator()(level const & n1, level const & n2) const { return n1.m_ptr == n2.m_ptr; } };
};

level const & mk_level_zero();
level const & mk_level_one();
level mk_max(level const & l1, level const & l2);
level mk_imax(level const & l1, level const & l2);
level mk_succ(level const & l);
level mk_param_univ(unsigned i);
level mk_meta_univ(unsigned i);

bool operator==(level const & l1, level const & l2);
inline bool operator!=(level const & l1, level const & l2) { return !operator==(l1, l2); }

/**
   \brief An arbitrary (monotonic) total order on universe level terms.
*/
bool is_lt(level const & l1, level const & l2);

unsigned hash(level const & l);
level_kind kind(level const & l);
inline bool is_zero(level const & l)  { return kind(l) == level_kind::Zero; }
inline bool is_param(level const & l) { return kind(l) == level_kind::Param; }
inline bool is_meta(level const & l)  { return kind(l) == level_kind::Meta; }
inline bool is_succ(level const & l)  { return kind(l) == level_kind::Succ; }
inline bool is_max(level const & l)   { return kind(l) == level_kind::Max; }
inline bool is_imax(level const & l)  { return kind(l) == level_kind::IMax; }

unsigned get_depth(level const & l);
unsigned get_param_range(level const & l);
unsigned get_meta_range(level const & l);

level const & max_lhs(level const & l);
level const & max_rhs(level const & l);
level const & imax_lhs(level const & l);
level const & imax_rhs(level const & l);
level const & succ_of(level const & l);
unsigned param_id(level const & l);
unsigned meta_id(level const & l);
/**
   \brief Return true iff \c l is an explicit level.
   We say a level l is explicit iff
   1) l is zero OR
   2) l = succ(l') and l' is explicit
*/
bool is_explicit(level const & l);

/**
   \brief Return true iff \c l contains placeholder (aka meta parameters).
*/
inline bool has_meta(level const & l) { return get_meta_range(l) > 0; }

/**
   \brief Printer for debugging purposes
*/
std::ostream & operator<<(std::ostream & out, level const & l);

/**
   \brief If the result is true, then forall assignments \c A that assigns all parameters and metavariables occuring
   in \c l, eval(A, l) != zero.
*/
bool is_not_zero(level const & l);

serializer & operator<<(serializer & s, level const & l);
level read_level(deserializer & d);
inline deserializer & operator>>(deserializer & d, level & l) { l = read_level(d); return d; }

/** \brief Pretty print the given level expression, unicode characters are used if \c unicode is \c true. */
format pp(level l, bool unicode, unsigned indent);
/** \brief Pretty print the given level expression using the given configuration options. */
format pp(level const & l, options const & opts = options());

/**
   \brief Auxiliary class used to manage universe constraints.
*/
class universe_context {
    struct imp;
    std::unique_ptr<imp> m_ptr;
public:
    universe_context();
    universe_context(universe_context const & s);
    ~universe_context();

    /**
       \brief Add the universe level constraint l1 <= l2.
    */
    void add_le(level const & l1, level const & l2);

    /**
       \brief Quick check wether l1 <= l2. No backtracking search is performed.
       If the result is true, then l1 <= l2 is implied. The result is false,
       if we could not establish that.
    */
    bool is_implied_cheap(level const & l1, level const & l2) const;

    /**
       \brief Expensive l1 <= l2 test. It performs a backtracking search.
    */
    bool is_implied(level const & l1, level const & l2);

    /**
       \brief Create a backtracking point.
    */
    void push();

    /**
       \brief Backtrack.
    */
    void pop(unsigned num_scopes);
};
}
void print(lean::level const & l);
