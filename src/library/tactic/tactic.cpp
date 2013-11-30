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
    LEAN_COPY_REF(tactic, s);
}

tactic & tactic::operator=(tactic && s) {
    LEAN_MOVE_REF(tactic, s);
}

/**
   \brief Try to extract a proof from the given proof state
*/
optional<expr> to_proof(proof_state const & s) {
    if (s.is_proof_final_state()) {
        try {
            assignment a(s.get_menv());
            proof_map  m;
            return some(s.get_proof_builder()(m, a));
        } catch (...) {
        }
    }
    return optional<expr>();
}

/**
   \brief Try to extract a counterexample from the given proof state.
*/
optional<counterexample> to_counterexample(proof_state const & s) {
    if (s.is_cex_final_state()) {
        assignment a(s.get_menv());
        name goal_name(head(s.get_goals()).first);
        try {
            return some(s.get_cex_builder()(goal_name, optional<counterexample>(), a));
        } catch (...) {
        }
    }
    return optional<counterexample>();
}

solve_result tactic::solve(environment const & env, io_state const & io, proof_state const & s1) {
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

solve_result tactic::solve(environment const & env, io_state const & io, context const & ctx, expr const & t) {
    proof_state s = to_proof_state(env, ctx, t);
    return solve(env, io, s);
}

tactic id_tactic() {
    return mk_tactic1([](environment const &, io_state const &, proof_state const & s) -> proof_state {
            return s;
        });
}

tactic fail_tactic() {
    return mk_tactic([](environment const &, io_state const &, proof_state const &) -> proof_state_seq {
            return proof_state_seq();
        });
}

tactic now_tactic() {
    return mk_tactic01([](environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            if (!empty(s.get_goals()))
                return none_proof_state();
            else
                return some(s);
        });
}

tactic trace_tactic(std::string const & msg) {
    return mk_tactic1([=](environment const &, io_state const & io, proof_state const & s) -> proof_state {
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
    return mk_tactic1([=](environment const &, io_state const & io, proof_state const & s) -> proof_state {
            options opts = io.get_options();
            format fmt   = s.pp(io.get_formatter(), opts);
            io.get_diagnostic_channel() << "Proof state:\n" << mk_pair(fmt, opts) << "\n";
            io.get_diagnostic_channel().get_stream().flush();
            return s;
        });
}

tactic suppress_trace(tactic const & t) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            io_state new_io(io);
            std::shared_ptr<output_channel> out(new string_output_channel());
            new_io.set_diagnostic_channel(out);
            return t(env, new_io, s);
        });
}

tactic assumption_tactic() {
    return mk_tactic01([](environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            list<std::pair<name, expr>> proofs;
            bool found = false;
            goals new_goals = map_goals(s, [&](name const & ng, goal const & g) -> goal {
                    expr const & c  = g.get_conclusion();
                    expr pr;
                    for (auto const & p : g.get_hypotheses()) {
                        check_interrupted();
                        if (p.second == c) {
                            pr = mk_constant(p.first, p.second);
                            break;
                        }
                    }
                    if (pr) {
                        proofs.emplace_front(ng, pr);
                        found = true;
                        return goal();
                    } else {
                        return g;
                    }
                });
            proof_builder pr_builder     = s.get_proof_builder();
            proof_builder new_pr_builder = mk_proof_builder([=](proof_map const & m, assignment const & a) -> expr {
                    proof_map new_m(m);
                    for (auto const & np : proofs) {
                        new_m.insert(np.first, np.second);
                    }
                    return pr_builder(new_m, a);
                });
            if (found)
                return some(proof_state(s, new_goals, new_pr_builder));
            else
                return none_proof_state();
        });
}

tactic then(tactic const & t1, tactic const & t2) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s1) -> proof_state_seq {
            return map_append(t1(env, io, s1), [=](proof_state const & s2) {
                    check_interrupted();
                    return t2(env, io, s2);
                });
        });
}

tactic orelse(tactic const & t1, tactic const & t2) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return orelse(t1(env, io, s), t2(env, io, s));
        });
}

tactic using_params(tactic const & t, options const & opts) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            io_state new_io(io);
            new_io.set_options(join(opts, io.get_options()));
            return t(env, new_io, s);
        });
}

tactic try_for(tactic const & t, unsigned ms, unsigned check_ms) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return timeout(t(env, io, s), ms, check_ms);
        });
}

tactic append(tactic const & t1, tactic const & t2) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return append(t1(env, io, s), t2(env, io, s));
        });
}

tactic interleave(tactic const & t1, tactic const & t2) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return interleave(t1(env, io, s), t2(env, io, s));
        });
}

tactic par(tactic const & t1, tactic const & t2, unsigned check_ms) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return par(t1(env, io, s), t2(env, io, s), check_ms);
        });
}

tactic repeat(tactic const & t) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s1) -> proof_state_seq {
            return repeat(s1, [=](proof_state const & s2) {
                    return t(env, io, s2);
                });
        });
}

tactic repeat_at_most(tactic const & t, unsigned k) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s1) -> proof_state_seq {
            return repeat_at_most(s1, [=](proof_state const & s2) {
                    return t(env, io, s2);
                }, k);
        });
}

tactic take(tactic const & t, unsigned k) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return take(k, t(env, io, s));
        });
}

proof_state_seq focus_core(tactic const & t, name const & gname, environment const & env, io_state const & io, proof_state const & s) {
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
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            return focus_core(t, gname, env, io, s);
        });
}

tactic focus(tactic const & t, int i) {
    return mk_tactic([=](environment const & env, io_state const & io, proof_state const & s) -> proof_state_seq {
            int j = 1;
            for (auto const & p : s.get_goals()) {
                if (i == j)
                    return focus_core(t, p.first, env, io, s);
                j++;
            }
            return proof_state_seq();
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

/**
   \brief We allow functions (that return tactics) to be used where a tactic
   is expected. The idea is to be able to write
          ORELSE(assumption_tactic, conj_tactic)
   instead of
          ORELSE(assumption_tactic(), conj_tactic())
*/
tactic to_tactic_ext(lua_State * L, int i) {
    tactic t;
    if (is_tactic(L, i)) {
        t = to_tactic(L, i);
    } else if (lua_isfunction(L, i)) {
        try {
            lua_pushvalue(L, i);
            pcall(L, 0, 1, 0);
        } catch (...) {
            throw_tactic_expected(i);
        }
        if (is_tactic(L, -1)) {
            t = to_tactic(L, -1);
            lua_pop(L, 1);
        } else {
            throw_tactic_expected(i);
        }
    } else {
        throw_tactic_expected(i);
    }
    if (!t)
        throw exception(sstream() << "arg #" << i << " must be a nonnull tactic");
    return t;
}

static void check_ios(io_state * ios) {
    if (!ios)
        throw exception("failed to invoke tactic, io_state is not available");
}

static int tactic_call_core(lua_State * L, tactic t, environment env, io_state ios, proof_state s) {
    script_state S = to_script_state(L);
    proof_state_seq seq;
    S.exec_unprotected([&]() {
            seq = t(env, ios, s);
        });
    return push_proof_state_seq_it(L, seq);
}

static int tactic_call(lua_State * L) {
    int nargs = lua_gettop(L);
    tactic t = to_tactic_ext(L, 1);
    ro_environment env(L, 2);
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
    tactic r = F(to_tactic_ext(L, 1), to_tactic_ext(L, 2));
    for (int i = 3; i <= nargs; i++)
        r = F(r, to_tactic_ext(L, i));
    return push_tactic(L, r);
}

static int tactic_then(lua_State * L)           {  return push_tactic(L, then(to_tactic_ext(L, 1), to_tactic_ext(L, 2)));   }
static int tactic_orelse(lua_State * L)         {  return push_tactic(L, orelse(to_tactic_ext(L, 1), to_tactic_ext(L, 2))); }
static int tactic_append(lua_State * L)         {  return push_tactic(L, append(to_tactic_ext(L, 1), to_tactic_ext(L, 2))); }
static int tactic_interleave(lua_State * L)     {  return push_tactic(L, interleave(to_tactic_ext(L, 1), to_tactic_ext(L, 2))); }
static int tactic_par(lua_State * L)            {  return push_tactic(L, par(to_tactic_ext(L, 1), to_tactic_ext(L, 2))); }

static int tactic_repeat(lua_State * L)         {  return push_tactic(L, repeat(to_tactic_ext(L, 1))); }
static int tactic_repeat1(lua_State * L)        {  return push_tactic(L, repeat1(to_tactic_ext(L, 1))); }
static int tactic_repeat_at_most(lua_State * L) {  return push_tactic(L, repeat_at_most(to_tactic_ext(L, 1), luaL_checkinteger(L, 2))); }
static int tactic_take(lua_State * L)           {  return push_tactic(L, take(to_tactic_ext(L, 1), luaL_checkinteger(L, 2))); }
static int tactic_determ(lua_State * L)         {  return push_tactic(L, determ(to_tactic_ext(L, 1))); }
static int tactic_suppress_trace(lua_State * L) {  return push_tactic(L, suppress_trace(to_tactic_ext(L, 1))); }
static int tactic_try_for(lua_State * L)        {  return push_tactic(L, try_for(to_tactic_ext(L, 1), luaL_checkinteger(L, 2))); }
static int tactic_using_params(lua_State * L)   {  return push_tactic(L, using_params(to_tactic_ext(L, 1), to_options(L, 2))); }
static int tactic_try(lua_State * L)            {  return push_tactic(L, orelse(to_tactic_ext(L, 1), id_tactic())); }

static int tactic_focus(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 1)
        return push_tactic(L, focus(to_tactic_ext(L, 1)));
    else if (lua_isnumber(L, 2))
        return push_tactic(L, focus(to_tactic_ext(L, 1), lua_tointeger(L, 2)));
    else
        return push_tactic(L, focus(to_tactic_ext(L, 1), to_name_ext(L, 2)));
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

static int tactic_solve_core(lua_State * L, tactic t, environment env, io_state ios, proof_state s) {
    script_state S = to_script_state(L);
    solve_result result;
    S.exec_unprotected([&]() {
            result = t.solve(env, ios, s);;
        });
    return push_solve_result(L, result);
}

static int tactic_solve_core(lua_State * L, tactic t, environment env, io_state ios, context ctx, expr e) {
    script_state S = to_script_state(L);
    solve_result result;
    S.exec_unprotected([&]() {
            result = t.solve(env, ios, ctx, e);
        });
    return push_solve_result(L, result);
}

static int tactic_solve(lua_State * L) {
    int nargs = lua_gettop(L);
    tactic t = to_tactic_ext(L, 1);
    ro_environment env(L, 2);
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
                       mk_tactic01([=](environment const & env, io_state const & ios, proof_state const & s) -> optional<proof_state> {
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
                                       std::this_thread::yield(); // give another thread a chance to execute
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
                       mk_tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
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
    return mk_lua_cond_tactic(L, to_tactic_ext(L, 2), to_tactic_ext(L, 3));
}

static int mk_lua_when_tactic(lua_State * L) {
    return mk_lua_cond_tactic(L, to_tactic_ext(L, 2), id_tactic());
}

static int mk_id_tactic(lua_State * L)          {  return push_tactic(L, id_tactic()); }
static int mk_now_tactic(lua_State * L)         {  return push_tactic(L, now_tactic()); }
static int mk_fail_tactic(lua_State * L)        {  return push_tactic(L, fail_tactic()); }
static int mk_trace_tactic(lua_State * L)       {  return push_tactic(L, trace_tactic(luaL_checkstring(L, 1))); }
static int mk_assumption_tactic(lua_State * L)  {  return push_tactic(L, assumption_tactic()); }
static int mk_trace_state_tactic(lua_State * L) {  return push_tactic(L, trace_state_tactic()); }

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
    SET_GLOBAL_FUN(mk_trace_tactic,       "trace_tactic");
    SET_GLOBAL_FUN(mk_id_tactic,          "id_tactic");
    SET_GLOBAL_FUN(mk_now_tactic,         "now_tactic");
    SET_GLOBAL_FUN(mk_fail_tactic,        "fail_tactic");
    SET_GLOBAL_FUN(mk_trace_state_tactic, "show_tactic");
    SET_GLOBAL_FUN(mk_assumption_tactic,  "assumption_tactic");
    SET_GLOBAL_FUN(mk_assumption_tactic,  "assump_tactic");
    SET_GLOBAL_FUN(mk_lua_tactic01,       "tactic");

    // HOL-like tactic names
    SET_GLOBAL_FUN(nary_tactic<then>,       "THEN");
    SET_GLOBAL_FUN(nary_tactic<orelse>,     "ORELSE");
    SET_GLOBAL_FUN(nary_tactic<interleave>, "INTERLEAVE");
    SET_GLOBAL_FUN(nary_tactic<append>,     "APPEND");
    SET_GLOBAL_FUN(nary_tactic<par>,        "PAR");
    SET_GLOBAL_FUN(tactic_repeat,           "REPEAT");
    SET_GLOBAL_FUN(tactic_repeat_at_most,   "REPEAT_AT_MOST");
    SET_GLOBAL_FUN(tactic_repeat1,          "REPEAT1");
    SET_GLOBAL_FUN(mk_lua_cond_tactic,      "COND");
    SET_GLOBAL_FUN(mk_lua_when_tactic,      "WHEN");
    SET_GLOBAL_FUN(tactic_try,              "TRY");
    SET_GLOBAL_FUN(tactic_try_for,          "TRY_FOR");
    SET_GLOBAL_FUN(tactic_take,             "TAKE");
    SET_GLOBAL_FUN(tactic_using_params,     "USING");
    SET_GLOBAL_FUN(tactic_using_params,     "USING_PARAMS");
    SET_GLOBAL_FUN(tactic_determ,           "DETERM");
    SET_GLOBAL_FUN(tactic_focus,            "FOCUS");
}
}
