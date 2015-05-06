/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <utility>
#include <memory>
#include <string>
#include "util/lazy_list.h"
#include "library/io_state.h"
#include "library/generic_exception.h"
#include "library/tactic/proof_state.h"

namespace lean {
/** \brief Throw an exception is \c v contains local constants, \c e is only used for position information. */
void check_has_no_local(expr const & v, expr const & e, char const * tac_name);

class tactic_exception : public generic_exception {
    optional<proof_state> m_ps;
public:
    tactic_exception(char const * msg, optional<expr> const & m, pp_fn const & fn);
    tactic_exception(char const * msg, optional<expr> const & m, proof_state const & ps, pp_fn const & fn);
    tactic_exception(expr const & e, std::string const & msg);
    tactic_exception(expr const & e, char const * msg);
    tactic_exception(expr const & e, sstream const & strm);
    tactic_exception(expr const & e, pp_fn const & fn);
    tactic_exception(std::string const & msg);
    tactic_exception(char const * msg);
    tactic_exception(sstream const & strm);
    tactic_exception(pp_fn const & fn);
    optional<proof_state> const & get_proof_state() const { return m_ps; }
};

#define throw_tactic_exception_if_enabled(ps, msg)  if (ps.report_failure()) throw tactic_exception(msg);
void throw_no_goal_if_enabled(proof_state const & ps);

typedef lazy_list<proof_state> proof_state_seq;

typedef std::function<proof_state_seq(environment const &, io_state const &, proof_state const &)> tactic;

inline optional<tactic> none_tactic() { return optional<tactic>(); }
inline optional<tactic> some_tactic(tactic const & t) { return optional<tactic>(t); }
inline optional<tactic> some_tactic(tactic && t) { return optional<tactic>(std::forward<tactic>(t)); }

template<typename F> inline proof_state_seq mk_proof_state_seq(F && f) { return mk_lazy_list<proof_state>(std::forward<F>(f)); }

tactic tactic01(std::function<optional<proof_state>(environment const &, io_state const & ios, proof_state const &)> f);
tactic tactic1(std::function<proof_state(environment const &, io_state const & ios, proof_state const &)> f);

/** \brief Return a "do nothing" tactic (aka skip). */
tactic id_tactic();
/** \brief Return a tactic the always fails. */
tactic fail_tactic();
/** \brief Return a tactic that fails if there are unsolved goals. */
tactic now_tactic();
/** \brief Return a tactic that performs \c t1 followed by \c t2. */
tactic then(tactic const & t1, tactic const & t2);
inline tactic operator<<(tactic const & t1, tactic const & t2) { return then(t1, t2); }
/** \brief Return a tactic that applies \c t1, and if \c t1 returns the empty sequence of states, then applies \c t2. */
tactic orelse(tactic const & t1, tactic const & t2);
inline tactic operator||(tactic const & t1, tactic const & t2) { return orelse(t1, t2); }
inline tactic try_tactic(tactic const & t) { return orelse(t, id_tactic()); }
/** \brief Return a tactic that appies \c t, but using the additional set of options \c opts. */
tactic using_params(tactic const & t, options const & opts);
/**
   \brief Return a tactic that tries the tactic \c t for at most \c ms milliseconds.
   If the tactic does not terminate in \c ms milliseconds, then the empty
   sequence is returned.

   \remark the tactic \c t is executed in a separate execution thread.

   \remark \c check_ms is how often the main thread checks whether the child
   thread finished.
*/
tactic try_for(tactic const & t, unsigned ms, unsigned check_ms = 1);
/**
   \brief Execute both tactics and and combines their results.
   The results produced by tactic \c t1 are listed before the ones
   from tactic \c t2.
*/
tactic append(tactic const & t1, tactic const & t2);

/** \brief Return a tactic that rotate goals to the left n steps */
tactic rotate_left(unsigned n);
/** \brief Return a tactic that rotate goals to the right n steps */
tactic rotate_right(unsigned n);

inline tactic operator+(tactic const & t1, tactic const & t2) { return append(t1, t2); }
/**
   \brief Execute both tactics and and combines their results.
   The results produced by tactics \c t1 and \c t2 are interleaved
   to guarantee fairness.
*/
tactic interleave(tactic const & t1, tactic const & t2);
/**
   \brief Return a tactic that executes \c t1 and \c t2 in parallel.
   This is similar to \c append and \c interleave. The order of
   the elements in the output sequence is not deterministic.
   It depends on how fast \c t1 and \c t2 produce their output.

   \remark \c check_ms is how often the main thread checks whether the children
   threads finished.
*/
tactic par(tactic const & t1, tactic const & t2, unsigned check_ms);
inline tactic par(tactic const & t1, tactic const & t2) { return par(t1, t2, 1); }
/**
   \brief Return a tactic that keeps applying \c t until it fails.
*/
tactic repeat(tactic const & t);
/**
   \brief Similar to \c repeat, but execute \c t at most \c k times.

   \remark The value \c k is the depth of the recursion.
   For example, if tactic \c t always produce a sequence of size 2,
   then tactic \c t will be applied 2^k times.
*/
tactic repeat_at_most(tactic const & t, unsigned k);
/**
   \brief Return a tactic that applies \c t, but takes at most \c
   \c k elements from the sequence produced by \c t.
*/
tactic take(tactic const & t, unsigned k);
/**
   \brief Return a tactic that applies \c t, but discards the first
   \c k elements from the sequence produced by \c t.
*/
tactic discard(tactic const & t, unsigned k);

/** \brief Return a tactic that renames hypothesis \c from into \c to in the current goal. */
tactic rename_tactic(name const & from, name const & to);

typedef std::function<bool(environment const & env, io_state const & ios, proof_state const & s)> proof_state_pred; // NOLINT
/**
    \brief Return a tactic that applies the predicate \c p to the input state.
    If \c p returns true, then applies \c t1. Otherwise, applies \c t2.
*/
tactic cond(proof_state_pred p, tactic const & t1, tactic const & t2);
/** \brief Syntax-sugar for cond(p, t, id_tactic()) */
inline tactic when(proof_state_pred p, tactic const & t) { return cond(p, t, id_tactic()); }
/**
   \brief Return a tactic that applies \c t only to the i-th goal.
   The tactic fails if the input state does have at least i goals.
*/
tactic focus(tactic const & t, unsigned i);
inline tactic focus(tactic const & t) { return focus(t, 0); }
/** \brief Return a tactic that applies beta-reduction. */
tactic beta_tactic();
/** \brief Apply \c t to all goals in the proof state */
tactic all_goals(tactic const & t);

UDATA_DEFS_CORE(proof_state_seq)
UDATA_DEFS_CORE(tactic);
void open_tactic(lua_State * L);
}
