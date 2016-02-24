/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <chrono>
#include <string>
#include "util/sstream.h"
#include "util/interrupt.h"
#include "util/lazy_list_fn.h"
#include "util/list_fn.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "library/normalize.h"
#include "library/util.h"
#include "library/tactic/tactic.h"
#include "library/io_state_stream.h"

namespace lean {
/** \brief Throw an exception is \c v contains local constants, \c e is only used for position information. */
void check_has_no_local(expr const & v, expr const & e, char const * tac_name) {
    if (has_local(v)) {
        for_each(v, [&](expr const & l, unsigned) {
                if (is_local(l))
                    throw tactic_exception(e, sstream() << "tactic '" << tac_name << "' contains reference to local '" << local_pp_name(l)
                                           << "' which is not visible by this tactic "
                                           << "possible causes: it was not marked as [visible]; it was destructued");
                return has_local(l);
            });
    }
}

tactic_exception::tactic_exception(char const * msg, optional<expr> const & m, pp_fn const & fn):
    generic_exception(msg, m, fn) {}
tactic_exception::tactic_exception(char const * msg, optional<expr> const & m, proof_state const & ps, pp_fn const & fn):
    generic_exception(msg, m, fn), m_ps(ps) {}
tactic_exception::tactic_exception(expr const & e, std::string const & msg):
    generic_exception(msg.c_str(), some_expr(e), [=](formatter const &) { return format(msg); }) {}
tactic_exception::tactic_exception(std::string const & msg):
    generic_exception(msg.c_str(), none_expr(), [=](formatter const &) { return format(msg); }) {}
tactic_exception::tactic_exception(char const * msg):tactic_exception(std::string(msg)) {}
tactic_exception::tactic_exception(sstream const & strm):tactic_exception(strm.str()) {}
tactic_exception::tactic_exception(expr const & e, char const * msg):tactic_exception(e, std::string(msg)) {}
tactic_exception::tactic_exception(expr const & e, sstream const & strm):tactic_exception(e, strm.str()) {}
tactic_exception::tactic_exception(expr const & e, pp_fn const & fn):generic_exception("tactic exception", some_expr(e), fn) {}
tactic_exception::tactic_exception(pp_fn const & fn):generic_exception("tactic exception", none_expr(), fn) {}

void throw_no_goal_if_enabled(proof_state const & ps) {
    throw_tactic_exception_if_enabled(ps, "invalid tactic, there are no goals to be solved");
}

tactic tactic01(std::function<optional<proof_state>(environment const &, io_state const & ios, proof_state const &)> f) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) {
            return mk_proof_state_seq([=]() {
                    auto r = f(env, ios, s);
                    if (r)
                        return some(mk_pair(*r, proof_state_seq()));
                    else
                        return proof_state_seq::maybe_pair();
                });
        });
}

tactic tactic1(std::function<proof_state(environment const &, io_state const & ios, proof_state const &)> f) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) {
            return mk_proof_state_seq([=]() {
                    auto r = f(env, ios, s);
                    return some(mk_pair(r, proof_state_seq()));
                });
        });
}

tactic id_tactic() {
    return tactic1([](environment const &, io_state const &, proof_state const & s) -> proof_state { return s; });
}

tactic fail_tactic() {
    return tactic([](environment const &, io_state const &, proof_state const &) -> proof_state_seq { return proof_state_seq(); });
}

tactic now_tactic() {
    return tactic01([](environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            if (!empty(s.get_goals()))
                return none_proof_state();
            else
                return some(s);
        });
}

tactic cond(proof_state_pred p, tactic const & t1, tactic const & t2) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
            return mk_proof_state_seq([=]() {
                    if (p(env, ios, s)) {
                        return t1(env, ios, s).pull();
                    } else {
                        return t2(env, ios, s).pull();
                    }
                });
        });
}

tactic then(tactic const & t1, tactic const & t2) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s1) -> proof_state_seq {
            return map_append(t1(env, ios, s1), [=](proof_state const & s2) {
                    check_interrupted();
                    bool has_meta = false;
                    goals const & gs = s2.get_goals();
                    for (goal const & g : gs) {
                        if (has_expr_metavar_relaxed(g.get_type())) {
                            has_meta = true;
                            break;
                        }
                    }
                    if (has_meta) {
                        buffer<goal> gs;
                        substitution subst = s2.get_subst();
                        to_buffer(s2.get_goals(), gs);
                        for (unsigned i = 0; i < gs.size(); i++) {
                            gs[i] = gs[i].instantiate(subst);
                        }
                        proof_state new_s2(s2, to_list(gs));
                        return t2(env, ios, new_s2);
                    } else {
                        return t2(env, ios, s2);
                    }
                }, "THEN tactical");
        });
}

tactic orelse(tactic const & t1, tactic const & t2) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & _s) -> proof_state_seq {
            proof_state s = _s.update_report_failure(false);
            return orelse(t1(env, ios, s), t2(env, ios, s), "ORELSE tactical");
        });
}

tactic using_params(tactic const & t, options const & opts) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
            io_state new_ios(ios);
            new_ios.set_options(join(opts, ios.get_options()));
            return t(env, new_ios, s);
        });
}

proof_state rotate_left(proof_state const & s, unsigned n) {
    buffer<goal> gs;
    to_buffer(s.get_goals(), gs);
    unsigned sz = gs.size();
    if (sz == 0)
        return s;
    n = n%sz;
    std::rotate(gs.begin(), gs.begin() + n, gs.end());
    return proof_state(s, to_list(gs.begin(), gs.end()));
}

tactic rotate_left(unsigned n) {
    return tactic1([=](environment const &, io_state const &, proof_state const & s) -> proof_state {
            return rotate_left(s, n);
        });
}

tactic rotate_right(unsigned n) {
    return tactic1([=](environment const &, io_state const &, proof_state const & s) -> proof_state {
            unsigned ngoals = length(s.get_goals());
            if (ngoals == 0)
                return s;
            return rotate_left(s, ngoals - n%ngoals);
        });
}

tactic try_for(tactic const & t, unsigned ms, unsigned check_ms) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & _s) -> proof_state_seq {
            proof_state s = _s.update_report_failure(false);
            return timeout(t(env, ios, s), ms, check_ms);
        });
}

tactic par(tactic const & t1, tactic const & t2, unsigned check_ms) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & _s) -> proof_state_seq {
            proof_state s = _s.update_report_failure(false);
            return par(t1(env, ios, s), t2(env, ios, s), check_ms);
        });
}

tactic repeat(tactic const & t) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & _s1) -> proof_state_seq {
            proof_state s1 = _s1.update_report_failure(false);
            return repeat(s1, [=](proof_state const & s2) {
                    return t(env, ios, s2);
                }, "REPEAT tactical");
        });
}

tactic repeat_at_most(tactic const & t, unsigned k) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & _s1) -> proof_state_seq {
            proof_state s1 = _s1.update_report_failure(false);
            return repeat_at_most(s1, [=](proof_state const & s2) {
                    return t(env, ios, s2);
                }, k, "REPEAT_AT_MOST tactical");
        });
}

tactic take(tactic const & t, unsigned k) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & _s) -> proof_state_seq {
            proof_state s = _s.update_report_failure(false);
            return take(k, t(env, ios, s));
        });
}

tactic discard(tactic const & t, unsigned k) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & _s) -> proof_state_seq {
            proof_state s = _s.update_report_failure(false);
            auto r = t(env, ios, s);
            for (unsigned i = 0; i < k; i++) {
                auto m = r.pull();
                if (!m)
                    return proof_state_seq();
                r = m->second;
            }
            return r;
        });
}

tactic beta_tactic() {
    return tactic01([=](environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            bool reduced = false;
            goals new_gs = map_goals(s, [&](goal const & g) -> optional<goal> {
                    expr new_meta = beta_reduce(g.get_meta());
                    expr new_type = beta_reduce(g.get_type());
                    if (new_meta != g.get_meta() || new_type != g.get_type())
                        reduced = true;
                    return some(goal(new_meta, new_type));
                });
            return reduced ? some(proof_state(s, new_gs)) : none_proof_state();
        });
}

proof_state_seq focus_core(tactic const & t, unsigned i, environment const & env, io_state const & ios, proof_state const & s) {
    goals gs = s.get_goals();
    if (i >= length(gs))
        return proof_state_seq();
    goal const & g    = get_ith(gs, i);
    proof_state new_s(s, goals(g)); // singleton goal
    return map(t(env, ios, new_s), [=](proof_state const & s2) {
            // we have to put back the goals that were not selected
            buffer<goal> tmp;
            to_buffer(gs, tmp);
            buffer<goal> new_gs;
            new_gs.append(i, tmp.data());
            for (auto g : s2.get_goals())
                new_gs.push_back(g);
            new_gs.append(tmp.size()-i-1, tmp.data()+i+1);
            return proof_state(s2, to_list(new_gs.begin(), new_gs.end()));
        });
}

tactic focus(tactic const & t, unsigned i) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
            return focus_core(t, i, env, ios, s);
        });
}

tactic all_goals(tactic const & t) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
            tactic r   = id_tactic();
            unsigned i = length(s.get_goals());
            while (i > 0) {
                --i;
                r = then(r, focus(t, i));
            }
            return r(env, ios, s);
        });
}
}
