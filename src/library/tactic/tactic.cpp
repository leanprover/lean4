/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <chrono>
#include <string>
#include "util/luaref.h"
#include "util/script_state.h"
#include "util/sstream.h"
#include "util/interrupt.h"
#include "util/lazy_list_fn.h"
#include "library/io_state_stream.h"
#include "kernel/replace_visitor.h"
#include "kernel/instantiate.h"
#include "kernel/update_expr.h"
#include "kernel/builtin.h"
#include "library/kernel_bindings.h"
#include "library/tactic/tactic.h"

namespace lean {
solve_result::solve_result(expr const & pr):m_kind(solve_result_kind::Proof) { new (&m_proof) expr(pr); }
solve_result::solve_result(counterexample const & cex):m_kind(solve_result_kind::Counterexample) { new (&m_cex) counterexample(cex); }
solve_result::solve_result(list<proof_state> const & fs):m_kind(solve_result_kind::Failure) { new (&m_failures) list<proof_state>(fs); }
void solve_result::init(solve_result const & r) {
    m_kind = r.m_kind;
    switch (m_kind) {
    case solve_result_kind::None:           break;
    case solve_result_kind::Proof:          new (&m_proof) expr(r.m_proof); break;
    case solve_result_kind::Counterexample: new (&m_cex) counterexample(r.m_cex); break;
    case solve_result_kind::Failure:        new (&m_failures) list<proof_state>(r.m_failures); break;
    }
}
void solve_result::destroy() {
    switch (m_kind) {
    case solve_result_kind::None:           break;
    case solve_result_kind::Proof:          m_proof.~expr(); break;
    case solve_result_kind::Counterexample: m_cex.~counterexample(); break;
    case solve_result_kind::Failure:        m_failures.~list<proof_state>(); break;
    }
}
solve_result::solve_result(solve_result const & r) {
    init(r);
}
solve_result::~solve_result() {
    destroy();
}
solve_result & solve_result::operator=(solve_result & other) {
    if (this == &other)
        return *this;
    destroy();
    init(other);
    return *this;
}
solve_result & solve_result::operator=(solve_result && other) {
    lean_assert(this != &other);
    destroy();
    init(other);
    return *this;
}

tactic & tactic::operator=(tactic const & s) {
    LEAN_COPY_REF(s);
}

tactic & tactic::operator=(tactic && s) {
    LEAN_MOVE_REF(s);
}

/**
   \brief Try to extract a proof from the given proof state
*/
optional<expr> to_proof(proof_state const & s) {
    if (s.is_proof_final_state()) {
        try {
            assignment a(s.get_menv().copy());
            proof_map  m;
            return some_expr(s.get_proof_builder()(m, a));
        } catch (...) {
        }
    }
    return none_expr();
}

/**
   \brief Try to extract a counterexample from the given proof state.
*/
optional<counterexample> to_counterexample(proof_state const & s) {
    if (s.is_cex_final_state()) {
        assignment a(s.get_menv().copy());
        name goal_name(head(s.get_goals()).first);
        try {
            return some(s.get_cex_builder()(goal_name, optional<counterexample>(), a));
        } catch (...) {
        }
    }
    return optional<counterexample>();
}

solve_result tactic::solve(ro_environment const & env, io_state const & io, proof_state const & s1) {
    proof_state_seq r   = operator()(env, io, s1);
    list<proof_state> failures;
    while (true) {
        check_interrupted();
        auto p = r.pull();
        if (!p) {
            return solve_result(failures);
        } else {
            proof_state s2 = p->first;
            r              = p->second;
            optional<expr> pr = to_proof(s2);
            if (pr)
                return solve_result(*pr);
            optional<counterexample> cex = to_counterexample(s2);
            if (cex)
                return solve_result(*cex);
            failures = cons(s2, failures);
        }
    }
}

solve_result tactic::solve(ro_environment const & env, io_state const & io, context const & ctx, expr const & t) {
    proof_state s = to_proof_state(env, ctx, t);
    return solve(env, io, s);
}

tactic id_tactic() {
    return mk_tactic1([](ro_environment const &, io_state const &, proof_state const & s) -> proof_state {
            return s;
        });
}

tactic fail_tactic() {
    return mk_tactic([](ro_environment const &, io_state const &, proof_state const &) -> proof_state_seq {
            return proof_state_seq();
        });
}

tactic now_tactic() {
    return mk_tactic01([](ro_environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            if (!empty(s.get_goals()))
                return none_proof_state();
            else
                return some(s);
        });
}

tactic trace_tactic(std::string const & msg) {
    return mk_tactic1([=](ro_environment const &, io_state const & io, proof_state const & s) -> proof_state {
            io.get_diagnostic_channel() << msg << "\n";
            io.get_diagnostic_channel().get_stream().flush();
            return s;
        });
}

tactic trace_tactic(sstream const & msg) {
    return trace_tactic(msg.str());
}

tactic trace_tactic(char const * msg) {
    return trace_tactic(std::string(msg));
}

tactic trace_state_tactic() {
    return mk_tactic1([=](ro_environment const &, io_state const & io, proof_state const & s) -> proof_state {
            options opts = io.get_options();
            format fmt   = s.pp(io.get_formatter(), opts);
            io.get_diagnostic_channel() << "Proof state:\n" << mk_pair(fmt, opts) << "\n";
            io.get_diagnostic_channel().get_stream().flush();
            return s;
        });
}

tactic suppress_trace(tactic const & t) {
    return mk_tactic([=](ro_environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            io_state new_io(io);
            std::shared_ptr<output_channel> out(std::make_shared<string_output_channel>());
            new_io.set_diagnostic_channel(out);
            return t(env, new_io, s);
        });
}

tactic assumption_tactic() {
    return mk_tactic01([](ro_environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            list<std::pair<name, expr>> proofs;
            goals new_gs = map_goals(s, [&](name const & gname, goal const & g) -> optional<goal> {
                    expr const & c  = g.get_conclusion();
                    optional<expr> pr;
                    for (auto const & p : g.get_hypotheses()) {
                        check_interrupted();
                        if (p.second == c) {
                            pr = mk_constant(p.first, p.second);
                            break;
                        }
                    }
                    if (pr) {
                        proofs.emplace_front(gname, *pr);
                        return optional<goal>();
                    } else {
                        return some(g);
                    }
                });
            if (empty(proofs))
                return none_proof_state();
            proof_builder new_pb = add_proofs(s.get_proof_builder(), proofs);
            return some(proof_state(s, new_gs, new_pb));
        });
}

tactic trivial_tactic() {
    return mk_tactic01([](ro_environment const & env, io_state const &, proof_state const & s) -> optional<proof_state> {
            list<std::pair<name, expr>> proofs;
            goals new_gs = map_goals(s, [&](name const & gname, goal const & g) -> optional<goal> {
                    expr const & c  = env->normalize(g.get_conclusion(), context(), true);
                    if (c == True) {
                        proofs.emplace_front(gname, Trivial);
                        return optional<goal>();
                    } else {
                        return some(g);
                    }
                });
            if (empty(proofs))
                return none_proof_state();
            proof_builder new_pb = add_proofs(s.get_proof_builder(), proofs);
            return some(proof_state(s, new_gs, new_pb));
        });
}

tactic then(tactic const & t1, tactic const & t2) {
    return mk_tactic([=](ro_environment const & env, io_state const & io, proof_state const & s1) -> proof_state_seq {
            return map_append(t1(env, io, s1), [=](proof_state const & s2) {
                    check_interrupted();
                    return t2(env, io, s2);
                }, "THEN tactical");
        });
}

tactic orelse(tactic const & t1, tactic const & t2) {
    return mk_tactic([=](ro_environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return orelse(t1(env, io, s), t2(env, io, s), "ORELSE tactical");
        });
}

tactic using_params(tactic const & t, options const & opts) {
    return mk_tactic([=](ro_environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            io_state new_io(io);
            new_io.set_options(join(opts, io.get_options()));
            return t(env, new_io, s);
        });
}

tactic try_for(tactic const & t, unsigned ms, unsigned check_ms) {
    return mk_tactic([=](ro_environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return timeout(t(env, io, s), ms, check_ms);
        });
}

tactic append(tactic const & t1, tactic const & t2) {
    return mk_tactic([=](ro_environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return append(t1(env, io, s), t2(env, io, s), "APPEND tactical");
        });
}

tactic interleave(tactic const & t1, tactic const & t2) {
    return mk_tactic([=](ro_environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return interleave(t1(env, io, s), t2(env, io, s), "INTERLEAVE tactical");
        });
}

tactic par(tactic const & t1, tactic const & t2, unsigned check_ms) {
    return mk_tactic([=](ro_environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return par(t1(env, io, s), t2(env, io, s), check_ms);
        });
}

tactic repeat(tactic const & t) {
    return mk_tactic([=](ro_environment const & env, io_state const & io, proof_state const & s1) -> proof_state_seq {
            return repeat(s1, [=](proof_state const & s2) {
                    return t(env, io, s2);
                }, "REPEAT tactical");
        });
}

tactic repeat_at_most(tactic const & t, unsigned k) {
    return mk_tactic([=](ro_environment const & env, io_state const & io, proof_state const & s1) -> proof_state_seq {
            return repeat_at_most(s1, [=](proof_state const & s2) {
                    return t(env, io, s2);
                }, k, "REPEAT_AT_MOST tactical");
        });
}

tactic take(tactic const & t, unsigned k) {
    return mk_tactic([=](ro_environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return take(k, t(env, io, s));
        });
}

proof_state_seq focus_core(tactic const & t, name const & gname, ro_environment const & env, io_state const & io, proof_state const & s) {
    for (auto const & p : s.get_goals()) {
        if (p.first == gname) {
            proof_builder pb = mk_proof_builder(
                [=](proof_map const & m, assignment const &) -> expr {
                    return find(m, gname);
                });
            cex_builder cb = mk_cex_builder_for(gname);
            proof_state new_s(s, goals(p), pb, cb); // new state with singleton goal
            return map(t(env, io, new_s), [=](proof_state const & s2) {
                    // we have to put back the goals that were not selected
                    list<std::pair<name, name>> renamed_goals;
                    goals new_gs = map_append(s.get_goals(), [&](std::pair<name, goal> const & p) {
                            if (p.first == gname) {
                                name_set used_names;
                                s.get_goal_names(used_names);
                                used_names.erase(gname);
                                return map(s2.get_goals(), [&](std::pair<name, goal> const & p2) -> std::pair<name, goal> {
                                        name uname = mk_unique(used_names, p2.first);
                                        used_names.insert(uname);
                                        renamed_goals.emplace_front(p2.first, uname);
                                        return mk_pair(uname, p2.second);
                                    });
                            } else {
                                return goals(p);
                            }
                        });
                    proof_builder pb1 = s.get_proof_builder();
                    proof_builder pb2 = s2.get_proof_builder();
                    proof_builder new_pb = mk_proof_builder(
                        [=](proof_map const & m, assignment const & a) -> expr {
                            proof_map m1(m); // map for pb1
                            proof_map m2; // map for pb2
                            for (auto p : renamed_goals) {
                                m2.insert(p.first, find(m, p.second));
                                m1.erase(p.first);
                            }
                            m1.insert(gname, pb2(m2, a));
                            return pb1(m1, a);
                        });
                    cex_builder cb1 = s.get_cex_builder();
                    cex_builder cb2 = s2.get_cex_builder();
                    cex_builder new_cb = mk_cex_builder(
                        [=](name const & n, optional<counterexample> const & cex, assignment const & a) -> counterexample {
                            for (auto p : renamed_goals) {
                                if (p.second == n)
                                    return cb2(p.first, cex, a);
                            }
                            return cb1(n, cex, a);
                        });
                    return proof_state(s2, new_gs, new_pb, new_cb);
                });
        }
    }
    return proof_state_seq(); // tactic is not applicable
}

tactic focus(tactic const & t, name const & gname) {
    return mk_tactic([=](ro_environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return focus_core(t, gname, env, io, s);
        });
}

tactic focus(tactic const & t, int i) {
    return mk_tactic([=](ro_environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            if (optional<name> n = s.get_ith_goal_name(i))
                return focus_core(t, *n, env, io, s);
            else
                return proof_state_seq();
        });
}

class unfold_core_fn : public replace_visitor {
protected:
    bool m_unfolded;

    virtual expr visit_app(expr const & e, context const & ctx) {
        expr const & f = arg(e, 0);
        if (is_constant(f)) {
            buffer<expr> new_args;
            for (unsigned i = 0; i < num_args(e); i++)
                new_args.push_back(visit(arg(e, i), ctx));
            if (is_lambda(new_args[0]))
                return apply_beta(new_args[0], new_args.size() - 1, new_args.data() + 1);
            else
                return update_app(e, new_args);
        } else {
            return replace_visitor::visit_app(e, ctx);
        }
    }
public:
    unfold_core_fn():m_unfolded(false) {}
    bool unfolded() const { return m_unfolded; }
};


class unfold_fn : public unfold_core_fn {
protected:
    name const & m_name;
    expr const & m_def;

    virtual expr visit_constant(expr const & c, context const &) {
        if (const_name(c) == m_name) {
            m_unfolded = true;
            return m_def;
        } else {
            return c;
        }
    }

public:
    unfold_fn(name const & n, expr const & d):m_name(n), m_def(d) {}
};

class unfold_all_fn : public unfold_core_fn {
protected:
    ro_environment m_env;

    virtual expr visit_constant(expr const & c, context const &) {
        optional<object> obj = m_env->find_object(const_name(c));
        if (should_unfold(obj)) {
            m_unfolded = true;
            return obj->get_value();
        } else {
            return c;
        }
    }

public:
    unfold_all_fn(ro_environment const & env):m_env(env) {}
};

optional<proof_state> unfold_tactic_core(unfold_core_fn & fn, proof_state const & s) {
    goals new_gs = map_goals(s, [&](name const &, goal const & g) -> optional<goal> {
            hypotheses new_hs = map(g.get_hypotheses(), [&](hypothesis const & h) { return hypothesis(h.first, fn(h.second)); });
            expr       new_c  = fn(g.get_conclusion());
            return some(goal(new_hs, new_c));
        });
    if (fn.unfolded()) {
        return some(proof_state(s, new_gs));
    } else {
        return none_proof_state();
    }
}

tactic unfold_tactic(name const & n) {
    return mk_tactic01([=](ro_environment const & env, io_state const &, proof_state const & s) -> optional<proof_state> {
            optional<object> obj = env->find_object(n);
            if (!obj || !obj->is_definition())
                return none_proof_state(); // tactic failed
            unfold_fn fn(n, obj->get_value());
            return unfold_tactic_core(fn, s);
        });
}

tactic unfold_tactic() {
    return mk_tactic01([=](ro_environment const & env, io_state const &, proof_state const & s) -> optional<proof_state> {
            unfold_all_fn fn(env);
            return unfold_tactic_core(fn, s);
        });
}

class beta_fn : public replace_visitor {
protected:
    bool m_reduced;

    virtual expr visit_app(expr const & e, context const & ctx) {
        expr const & f = arg(e, 0);
        if (is_lambda(f)) {
            m_reduced = true;
            buffer<expr> new_args;
            for (unsigned i = 0; i < num_args(e); i++)
                new_args.push_back(visit(arg(e, i), ctx));
            lean_assert(is_lambda(new_args[0]));
            return apply_beta(new_args[0], new_args.size() - 1, new_args.data() + 1);
        } else {
            return replace_visitor::visit_app(e, ctx);
        }
    }
public:
    beta_fn():m_reduced(false) {}
    bool reduced() const { return m_reduced; }
};

tactic beta_tactic() {
    return mk_tactic01([=](ro_environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            beta_fn fn;
            goals new_gs = map_goals(s, [&](name const &, goal const & g) -> optional<goal> {
                    hypotheses new_hs = map(g.get_hypotheses(), [&](hypothesis const & h) { return hypothesis(h.first, fn(h.second)); });
                    expr       new_c  = fn(g.get_conclusion());
                    return some(goal(new_hs, new_c));
                });
            return fn.reduced() ? some(proof_state(s, new_gs)) : none_proof_state();
        });
}

tactic normalize_tactic(bool unfold_opaque, bool all) {
    return mk_tactic01([=](ro_environment const & env, io_state const &, proof_state const & s) -> optional<proof_state> {
            bool applied = false;
            goals new_gs = map_goals(s, [&](name const &, goal const & g) -> optional<goal> {
                    if (!applied || all) {
                        applied = true;
                        expr new_c  = env->normalize(g.get_conclusion(), context(), unfold_opaque);
                        return some(goal(g.get_hypotheses(), new_c));
                    } else {
                        return some(g);
                    }
                });
            return applied ? some(proof_state(s, new_gs)) : none_proof_state();
        });
}

DECL_UDATA(proof_state_seq)

static const struct luaL_Reg proof_state_seq_m[] = {
    {"__gc",            proof_state_seq_gc}, // never throws
    {0, 0}
};

static int proof_state_seq_next(lua_State * L) {
    proof_state_seq seq = to_proof_state_seq(L, lua_upvalueindex(1));
    script_state S      = to_script_state(L);
    proof_state_seq::maybe_pair p;
    S.exec_unprotected([&]() {
            p = seq.pull();
        });
    if (p) {
        push_proof_state_seq(L, p->second);
        lua_replace(L, lua_upvalueindex(1));
        push_proof_state(L, p->first);
    } else {
        lua_pushnil(L);
    }
    return 1;
}

static int push_proof_state_seq_it(lua_State * L, proof_state_seq const & seq) {
    push_proof_state_seq(L, seq);
    lua_pushcclosure(L, &safe_function<proof_state_seq_next>, 1); // create closure with 1 upvalue
    return 1;
}

DECL_UDATA(tactic)

[[ noreturn ]] void throw_tactic_expected(int i) {
    throw exception(sstream() << "arg #" << i << " must be a tactic or a function that returns a tactic");
}

static void check_ios(io_state * ios) {
    if (!ios)
        throw exception("failed to invoke tactic, io_state is not available");
}

static int tactic_call_core(lua_State * L, tactic t, ro_environment env, io_state ios, proof_state s) {
    script_state S = to_script_state(L);
    proof_state_seq seq;
    S.exec_unprotected([&]() {
            seq = t(env, ios, s);
        });
    return push_proof_state_seq_it(L, seq);
}

static int tactic_call(lua_State * L) {
    int nargs = lua_gettop(L);
    tactic t = to_tactic(L, 1);
    ro_shared_environment env(L, 2);
    if (nargs == 3) {
        io_state * ios = get_io_state(L);
        check_ios(ios);
        return tactic_call_core(L, t, env, *ios, to_proof_state(L, 3));
    } else {
        return tactic_call_core(L, t, env, to_io_state(L, 3), to_proof_state(L, 4));
    }
}

typedef tactic (*binary_tactic_fn)(tactic const &, tactic const &);

template<binary_tactic_fn F>
static int nary_tactic(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs < 2)
        throw exception("tactical expects at least two arguments");
    tactic r = F(to_tactic(L, 1), to_tactic(L, 2));
    for (int i = 3; i <= nargs; i++)
        r = F(r, to_tactic(L, i));
    return push_tactic(L, r);
}

static int tactic_then(lua_State * L)           {  return push_tactic(L, then(to_tactic(L, 1), to_tactic(L, 2)));   }
static int tactic_orelse(lua_State * L)         {  return push_tactic(L, orelse(to_tactic(L, 1), to_tactic(L, 2))); }
static int tactic_append(lua_State * L)         {  return push_tactic(L, append(to_tactic(L, 1), to_tactic(L, 2))); }
static int tactic_interleave(lua_State * L)     {  return push_tactic(L, interleave(to_tactic(L, 1), to_tactic(L, 2))); }
static int tactic_par(lua_State * L)            {  return push_tactic(L, par(to_tactic(L, 1), to_tactic(L, 2))); }

static int tactic_repeat(lua_State * L)         {  return push_tactic(L, repeat(to_tactic(L, 1))); }
static int tactic_repeat1(lua_State * L)        {  return push_tactic(L, repeat1(to_tactic(L, 1))); }
static int tactic_repeat_at_most(lua_State * L) {  return push_tactic(L, repeat_at_most(to_tactic(L, 1), luaL_checkinteger(L, 2))); }
static int tactic_take(lua_State * L)           {  return push_tactic(L, take(to_tactic(L, 1), luaL_checkinteger(L, 2))); }
static int tactic_determ(lua_State * L)         {  return push_tactic(L, determ(to_tactic(L, 1))); }
static int tactic_suppress_trace(lua_State * L) {  return push_tactic(L, suppress_trace(to_tactic(L, 1))); }
static int tactic_try_for(lua_State * L)        {  return push_tactic(L, try_for(to_tactic(L, 1), luaL_checkinteger(L, 2))); }
static int tactic_using_params(lua_State * L)   {  return push_tactic(L, using_params(to_tactic(L, 1), to_options(L, 2))); }
static int tactic_try(lua_State * L)            {  return push_tactic(L, orelse(to_tactic(L, 1), id_tactic())); }

static int tactic_focus(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 1)
        return push_tactic(L, focus(to_tactic(L, 1)));
    else if (lua_isnumber(L, 2))
        return push_tactic(L, focus(to_tactic(L, 1), lua_tointeger(L, 2)));
    else
        return push_tactic(L, focus(to_tactic(L, 1), to_name_ext(L, 2)));
}

static int push_solve_result(lua_State * L, solve_result const & r) {
    switch (r.kind()) {
    case solve_result_kind::None:           lua_pushnil(L); break;
    case solve_result_kind::Proof:          push_expr(L, r.get_proof()); break;
    case solve_result_kind::Counterexample: push_environment(L, r.get_cex()); break;
    case solve_result_kind::Failure:
        lua_newtable(L);
        int i = 1;
        for (auto s : r.get_failures()) {
            push_proof_state(L, s);
            lua_rawseti(L, -2, i);
            i++;
        }
    }
    return 1;
}

static int tactic_solve_core(lua_State * L, tactic t, ro_environment env, io_state ios, proof_state s) {
    script_state S = to_script_state(L);
    solve_result result;
    S.exec_unprotected([&]() {
            result = t.solve(env, ios, s);;
        });
    return push_solve_result(L, result);
}

static int tactic_solve_core(lua_State * L, tactic t, ro_environment env, io_state ios, context ctx, expr e) {
    script_state S = to_script_state(L);
    solve_result result;
    S.exec_unprotected([&]() {
            result = t.solve(env, ios, ctx, e);
        });
    return push_solve_result(L, result);
}

static int tactic_solve(lua_State * L) {
    int nargs = lua_gettop(L);
    tactic t = to_tactic(L, 1);
    ro_shared_environment env(L, 2);
    if (nargs == 3) {
        io_state * ios = get_io_state(L);
        check_ios(ios);
        return tactic_solve_core(L, t, env, *ios, to_proof_state(L, 3));
    } else if (nargs == 4) {
        if (is_io_state(L, 3)) {
            return tactic_solve_core(L, t, env, to_io_state(L, 3), to_proof_state(L, 4));
        } else {
            io_state * ios = get_io_state(L);
            check_ios(ios);
            return tactic_solve_core(L, t, env, *ios, to_context(L, 3), to_expr(L, 4));
        }
    } else {
        return tactic_solve_core(L, t, env, to_io_state(L, 3), to_context(L, 4), to_expr(L, 5));
    }
}

static int mk_lua_tactic01(lua_State * L) {
    luaL_checktype(L, 1, LUA_TFUNCTION); // user-fun
    script_state::weak_ref S = to_script_state(L).to_weak_ref();
    luaref ref(L, 1);
    return push_tactic(L,
                       mk_tactic01([=](ro_environment const & env, io_state const & ios, proof_state const & s) -> optional<proof_state> {
                               script_state S_copy(S);
                               optional<proof_state> r;
                               luaref coref; // Remark: we have to release the reference in a protected block.
                               try {
                                   bool done    = false;
                                   lua_State * co;
                                   S_copy.exec_protected([&]() {
                                           co = lua_newthread(L); // create a coroutine for executing user-fun
                                           coref = luaref(L, -1);    // make sure co-routine in not deleted
                                           lua_pop(L, 1);
                                           ref.push();               // push user-fun on the stack
                                           push_environment(L, env); // push args...
                                           push_io_state(L, ios);
                                           push_proof_state(L, s);
                                           lua_xmove(L, co, 4);      // move function and arguments to co
                                           done = resume(co, 3);
                                       });
                                   while (!done) {
                                       check_interrupted();
                                       this_thread::yield(); // give another thread a chance to execute
                                       S_copy.exec_protected([&]() {
                                               done = resume(co, 0);
                                           });
                                   }
                                   S_copy.exec_protected([&]() {
                                           if (is_proof_state(co, -1)) {
                                               r = to_proof_state(co, -1);
                                           }
                                           coref.release();
                                       });
                                   return r;
                               } catch (...) {
                                   S_copy.exec_protected([&]() { coref.release(); });
                                   throw;
                               }
                           }));
}

static int mk_lua_cond_tactic(lua_State * L, tactic t1, tactic t2) {
    luaL_checktype(L, 1, LUA_TFUNCTION); // user-fun
    script_state::weak_ref S = to_script_state(L).to_weak_ref();
    luaref ref(L, 1);
    return push_tactic(L,
                       mk_tactic([=](ro_environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
                               return mk_proof_state_seq([=]() {
                                       script_state S_copy(S);
                                       bool cond = false;
                                       S_copy.exec_protected([&]() {
                                               ref.push();               // push user-fun on the stack
                                               push_environment(L, env); // push args...
                                               push_io_state(L, ios);
                                               push_proof_state(L, s);
                                               pcall(L, 3, 1, 0);
                                               cond = lua_toboolean(L, -1);
                                           });
                                       if (cond) {
                                           return t1(env, ios, s).pull();
                                       } else {
                                           return t2(env, ios, s).pull();
                                       }
                                   });
                           }));
}

static int mk_lua_cond_tactic(lua_State * L) {
    return mk_lua_cond_tactic(L, to_tactic(L, 2), to_tactic(L, 3));
}

static int mk_lua_when_tactic(lua_State * L) {
    return mk_lua_cond_tactic(L, to_tactic(L, 2), id_tactic());
}

static int mk_id_tactic(lua_State * L)          {  return push_tactic(L, id_tactic()); }
static int mk_now_tactic(lua_State * L)         {  return push_tactic(L, now_tactic()); }
static int mk_fail_tactic(lua_State * L)        {  return push_tactic(L, fail_tactic()); }
static int mk_trace_tactic(lua_State * L)       {  return push_tactic(L, trace_tactic(luaL_checkstring(L, 1))); }
static int mk_assumption_tactic(lua_State * L)  {  return push_tactic(L, assumption_tactic()); }
static int mk_trivial_tactic(lua_State * L)     {  return push_tactic(L, trivial_tactic()); }
static int mk_trace_state_tactic(lua_State * L) {  return push_tactic(L, trace_state_tactic()); }
static int mk_unfold_tactic(lua_State * L)      {
    int nargs = lua_gettop(L);
    if (nargs == 0)
        return push_tactic(L, unfold_tactic());
    else
        return push_tactic(L, unfold_tactic(to_name_ext(L, 1)));
}
static int mk_beta_tactic(lua_State * L) {  return push_tactic(L, beta_tactic()); }
static int mk_normalize_tactic(lua_State * L) {
    int nargs = lua_gettop(L);
    return push_tactic(L, normalize_tactic(nargs == 0 ? false : lua_toboolean(L, 1),
                                           nargs <= 1 ? true  : lua_toboolean(L, 2)));
}
static int mk_eval_tactic(lua_State * L) {
    int nargs = lua_gettop(L);
    return push_tactic(L, normalize_tactic(true, nargs == 0 ? true : lua_toboolean(L, 1)));
}

static const struct luaL_Reg tactic_m[] = {
    {"__gc",            tactic_gc}, // never throws
    {"__call",          safe_function<tactic_call>},
    {"__concat",        safe_function<tactic_then>},
    {"__pow",           safe_function<tactic_orelse>},
    {"__add",           safe_function<tactic_append>},
    {"then",            safe_function<tactic_then>},
    {"orelse",          safe_function<tactic_orelse>},
    {"append",          safe_function<tactic_append>},
    {"interleave",      safe_function<tactic_interleave>},
    {"solve",           safe_function<tactic_solve>},
    {"par",             safe_function<tactic_par>},
    {"determ",          safe_function<tactic_determ>},
    {"repeat",          safe_function<tactic_repeat>},
    {"repeat1",         safe_function<tactic_repeat1>},
    {"repeat_at_most",  safe_function<tactic_repeat_at_most>},
    {"take",            safe_function<tactic_take>},
    {"suppress_trace",  safe_function<tactic_suppress_trace>},
    {"try_for",         safe_function<tactic_try_for>},
    {"using_params",    safe_function<tactic_using_params>},
    {"using",           safe_function<tactic_using_params>},
    {"focus",           safe_function<tactic_focus>},
    {0, 0}
};

static void tactic_migrate(lua_State * src, int i, lua_State * tgt) {
    push_tactic(tgt, to_tactic(src, i));
}

void open_tactic(lua_State * L) {
    luaL_newmetatable(L, proof_state_seq_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, proof_state_seq_m, 0);
    SET_GLOBAL_FUN(proof_state_seq_pred, "is_proof_state_seq");

    luaL_newmetatable(L, tactic_mt);
    set_migrate_fn_field(L, -1, tactic_migrate);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, tactic_m, 0);

    SET_GLOBAL_FUN(tactic_pred,           "is_tactic");
    SET_GLOBAL_FUN(mk_trace_tactic,       "trace_tac");
    SET_GLOBAL_FUN(mk_id_tactic,          "id_tac");
    SET_GLOBAL_FUN(mk_now_tactic,         "now_tac");
    SET_GLOBAL_FUN(mk_fail_tactic,        "fail_tac");
    SET_GLOBAL_FUN(mk_trace_state_tactic, "show_tac");
    SET_GLOBAL_FUN(mk_assumption_tactic,  "assumption_tac");
    SET_GLOBAL_FUN(mk_trivial_tactic,     "trivial_tac");
    SET_GLOBAL_FUN(mk_unfold_tactic,      "unfold_tac");
    SET_GLOBAL_FUN(mk_beta_tactic,        "beta_tac");
    SET_GLOBAL_FUN(mk_normalize_tactic,   "normalize_tac");
    SET_GLOBAL_FUN(mk_eval_tactic,        "eval_tac");
    SET_GLOBAL_FUN(mk_lua_tactic01,       "tactic");

    // HOL-like tactic names
    SET_GLOBAL_FUN(nary_tactic<then>,       "Then");
    SET_GLOBAL_FUN(nary_tactic<orelse>,     "OrElse");
    SET_GLOBAL_FUN(nary_tactic<interleave>, "Interleave");
    SET_GLOBAL_FUN(nary_tactic<append>,     "Append");
    SET_GLOBAL_FUN(nary_tactic<par>,        "Par");
    SET_GLOBAL_FUN(tactic_repeat,           "Repeat");
    SET_GLOBAL_FUN(tactic_repeat_at_most,   "RepeatAtMost");
    SET_GLOBAL_FUN(tactic_repeat1,          "Repeat1");
    SET_GLOBAL_FUN(mk_lua_cond_tactic,      "Cond");
    SET_GLOBAL_FUN(mk_lua_when_tactic,      "When");
    SET_GLOBAL_FUN(tactic_try,              "Try");
    SET_GLOBAL_FUN(tactic_try_for,          "TryFor");
    SET_GLOBAL_FUN(tactic_take,             "Take");
    SET_GLOBAL_FUN(tactic_using_params,     "Using");
    SET_GLOBAL_FUN(tactic_using_params,     "UsingParams");
    SET_GLOBAL_FUN(tactic_determ,           "Determ");
    SET_GLOBAL_FUN(tactic_focus,            "Focus");
}
}
