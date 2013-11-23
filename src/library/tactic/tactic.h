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
    virtual proof_state_seq operator()(environment const & env, io_state const & io, proof_state const & s) = 0;
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

    proof_state_seq operator()(environment const & env, io_state const & io, proof_state const & s) { return m_ptr->operator()(env, io, s); }

    expr solve(environment const & env, io_state const & io, proof_state const & s);
    expr solve(environment const & env, io_state const & io, context const & ctx, expr const & t);
};

template<typename F>
class simple_tactic_cell : public tactic_cell {
    F m_f;
public:
    simple_tactic_cell(F && f):m_f(f) {}
    virtual proof_state_seq operator()(environment const & env, io_state const & io, proof_state const & s) {
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

/**
   \brief Create a tactic using the given functor.

   <code>
   proof_state operator()(environment const & env, io_state const & io, proof_state const & s)
   </code>

   \remark The functor is invoked on demand.
*/
template<typename F>
tactic mk_simple_tactic(F && f) {
    return
        mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) {
                return proof_state_seq([=]() { return some(mk_pair(f(env, io, s), proof_state_seq())); });
            });
}

inline proof_state_seq to_proof_state_seq(proof_state const & s) {
    return proof_state_seq([=]() { return some(mk_pair(s, proof_state_seq())); });
}

inline proof_state_seq to_proof_state_seq(proof_state_seq::maybe_pair const & p) {
    lean_assert(p);
    return proof_state_seq([=]() { return some(mk_pair(p->first, p->second)); });
}

inline proof_state_seq to_proof_state_seq(proof_state const & s, proof_state_seq const & t) {
    return proof_state_seq([=]() { return some(mk_pair(s, t)); });
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
   \brief Return a tactic that performs \c t1 followed by \c t2.
*/
tactic then(tactic t1, tactic t2);
inline tactic operator<<(tactic t1, tactic t2) { return then(t1, t2); }
/**
   \brief Return a tactic that applies \c t1, and if \c t1 returns the empty sequence of states,
   then applies \c t2.
*/
tactic orelse(tactic t1, tactic t2);
inline tactic operator||(tactic t1, tactic t2) { return orelse(t1, t2); }
/**
   \brief Return a tactic that tries the tactic \c t for at most \c ms milliseconds.
   If the tactic does not terminate in \c ms milliseconds, then the empty
   sequence is returned.

   \remark the tactic \c t is executed in a separate execution thread.

   \remark \c check_ms is how often the main thread checks whether the child
   thread finished.
*/
tactic try_for(tactic t, unsigned ms, unsigned check_ms = 1);
/**
   \brief Execute both tactics and and combines their results.
   The results produced by tactic \c t1 are listed before the ones
   from tactic \c t2.
*/
tactic append(tactic t1, tactic t2);
inline tactic operator+(tactic t1, tactic t2) { return append(t1, t2); }
/**
   \brief Execute both tactics and and combines their results.
   The results produced by tactics \c t1 and \c t2 are interleaved
   to guarantee fairness.
*/
tactic interleave(tactic t1, tactic t2);
/**
   \brief Return a tactic that executs \c t1 and \c t2 in parallel.
   It returns the sequence produced by the first to terminate.

   \remark \c check_ms is how often the main thread checks whether the children
   threads finished.
*/
tactic par(tactic t1, tactic t2, unsigned check_ms = 1);
/**
   \brief Return a tactic that keeps applying \c t until it fails.
*/
tactic repeat(tactic t);
/**
   \brief Similar to \c repeat, but execute \c t at most \c k times.

   \remark The value \c k is the depth of the recursion.
   For example, if tactic \c t always produce a sequence of size 2,
   then tactic \c t will be applied 2^k times.
*/
tactic repeat_at_most(tactic t, unsigned k);
/**
   \brief Return a tactic that applies \c t, but takes at most \c
   k elements from the sequence produced by \c t.
*/
tactic take(tactic t, unsigned k);
/**
   \brief Return a tactic that forces \c t to produce all
   the elements in the resultant sequence.

   \remark proof_state_seq is a lazy-list, that is, their
   elements are produced on demand. This tactic forces
   all the elements in the sequence to be computed eagerly.

   \remark The sequence may be infinite. So, consider
   combining this tactical with \c take if the sequence
   may be infinite or too big.
*/
tactic force(tactic t);
}
