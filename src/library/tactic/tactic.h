/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include <utility>
#include <memory>
#include <mutex>
#include <string>
#include "util/lazy_list.h"
#include "library/io_state.h"
#include "library/tactic/proof_state.h"

namespace lean {
typedef lazy_list<proof_state> proof_state_seq;

class tactic_cell {
    void dealloc() { delete this; }
    MK_LEAN_RC();
public:
    tactic_cell():m_rc(0) {}
    virtual ~tactic_cell() {}
    virtual proof_state_seq operator()(environment const & env, io_state const & io, proof_state const & s) const = 0;
};

class tactic {
protected:
    tactic_cell * m_ptr;
public:
    explicit tactic(tactic_cell * ptr):m_ptr(ptr) { if (m_ptr) m_ptr->inc_ref(); }
    tactic(tactic const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    tactic(tactic && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~tactic() { if (m_ptr) m_ptr->dec_ref(); }
    friend void swap(tactic & a, tactic & b) { std::swap(a.m_ptr, b.m_ptr); }
    tactic & operator=(tactic const & s);
    tactic & operator=(tactic && s);

    proof_state_seq operator()(environment const & env, io_state const & io, proof_state const & s) const { return m_ptr->operator()(env, io, s); }

    expr solve(environment const & env, io_state const & io, proof_state const & s);
    expr solve(environment const & env, io_state const & io, context const & ctx, expr const & t);
};

template<typename F>
class simple_tactic_cell : public tactic_cell {
    F m_f;
public:
    simple_tactic_cell(F && f):m_f(f) {}
    virtual proof_state_seq operator()(environment const & env, io_state const & io, proof_state const & s) const {
        return m_f(env, io, s);
    }
};

/**
   \brief Create a tactic using the given functor.
   The functor must contain the operator:

   <code>
   proof_state_seq operator()(environment const & env, io_state const & io, proof_state const & s)
   </code>
*/
template<typename F>
tactic mk_tactic(F && f) { return tactic(new simple_tactic_cell<F>(std::forward<F>(f))); }

template<typename F>
inline proof_state_seq mk_proof_state_seq(F && f) {
    return mk_lazy_list<proof_state>(std::forward<F>(f));
}

/**
   \brief Create a tactic that produces exactly one output state.

   The functor f must contain the method:
   <code>
   proof_state operator()(environment const & env, io_state const & io, proof_state const & s)
   </code>

   \remark The functor is invoked on demand.
*/
template<typename F>
tactic mk_tactic1(F && f) {
    return
        mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) {
                return mk_proof_state_seq([=]() { return some(mk_pair(f(env, io, s), proof_state_seq())); });
            });
}

/**
   \brief Create a tactic that produces at most one output state.

   The functor f must contain the method:
   <code>
   optional<proof_state> operator()(environment const & env, io_state const & io, proof_state const & s)
   </code>

   \remark The functor is invoked on demand.
*/
template<typename F>
tactic mk_tactic01(F && f) {
    return
        mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) {
                return mk_proof_state_seq([=]() {
                        auto r = f(env, io, s);
                        if (r)
                            return some(mk_pair(*r, proof_state_seq()));
                        else
                            return proof_state_seq::maybe_pair();
                    });
            });
}

inline proof_state_seq to_proof_state_seq(proof_state const & s) {
    return mk_proof_state_seq([=]() { return some(mk_pair(s, proof_state_seq())); });
}

inline proof_state_seq to_proof_state_seq(proof_state_seq::maybe_pair const & p) {
    lean_assert(p);
    return mk_proof_state_seq([=]() { return some(mk_pair(p->first, p->second)); });
}

inline proof_state_seq to_proof_state_seq(proof_state const & s, proof_state_seq const & t) {
    return mk_proof_state_seq([=]() { return some(mk_pair(s, t)); });
}

/**
   \brief Return a "do nothing" tactic (aka skip).
*/
tactic id_tactic();
/**
   \brief Return a tactic the always fails.
*/
tactic fail_tactic();
/**
   \brief Return a tactic that fails if there are unsolved goals.
*/
tactic now_tactic();
/**
   \brief Return a tactic that solves any goal of the form  <tt>..., H : A, ... |- A</tt>.
*/
tactic assumption_tactic();
/**
   \brief Return a tactic that just returns the input state, and display the given message in the diagnostic channel.
*/
tactic trace_tactic(char const * msg);
class sstream;
tactic trace_tactic(sstream const & msg);
tactic trace_tactic(std::string const & msg);
/**
   \brief Return a tactic that just displays the input state in the diagnostic channel.
*/
tactic trace_state_tactic();
/**
   \brief Create a tactic that applies \c t, but suppressing diagnostic messages.
*/
tactic suppress_trace(tactic const & t);

/**
   \brief Return a tactic that performs \c t1 followed by \c t2.
*/
tactic then(tactic const & t1, tactic const & t2);
inline tactic operator<<(tactic const & t1, tactic const & t2) { return then(t1, t2); }
/**
   \brief Return a tactic that applies \c t1, and if \c t1 returns the empty sequence of states,
   then applies \c t2.
*/
tactic orelse(tactic const & t1, tactic const & t2);
inline tactic operator||(tactic const & t1, tactic const & t2) { return orelse(t1, t2); }
/**
   \brief Return a tactic that appies \c t, but using the additional set of options
   \c opts.
*/
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
tactic par(tactic const & t1, tactic const & t2, unsigned check_ms = 1);
/**
   \brief Return a tactic that keeps applying \c t until it fails.
*/
tactic repeat(tactic const & t);
/**
   \brief Similar to \c repeat, but applies \c t at least once.
*/
inline tactic repeat1(tactic const & t) { return then(t, repeat(t)); }
/**
   \brief Similar to \c repeat, but execute \c t at most \c k times.

   \remark The value \c k is the depth of the recursion.
   For example, if tactic \c t always produce a sequence of size 2,
   then tactic \c t will be applied 2^k times.
*/
tactic repeat_at_most(tactic const & t, unsigned k);
/**
   \brief Return a tactic that applies \c t, but takes at most \c
   k elements from the sequence produced by \c t.
*/
tactic take(tactic const & t, unsigned k);
/**
   \brief Syntax sugar for take(t, 1)
*/
inline tactic determ(tactic const & t) { return take(t, 1); }
/**
   \brief Return a tactic that applies the predicate \c p to the input state.
   If \c p returns true, then applies \c t1. Otherwise, applies \c t2.
*/
template<typename P>
tactic cond(P && p, tactic const & t1, tactic const & t2) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return mk_proof_state_seq([=]() {
                    if (p(env, io, s)) {
                        return t1(env, io, s).pull();
                    } else {
                        return t2(env, io, s).pull();
                    }
                });
        });
}
/**
   \brief Syntax-sugar for cond(p, t, id_tactic())
*/
template<typename P>
tactic when(P && p, tactic const & t) { return cond(std::forward<P>(p), t, id_tactic()); }
}
