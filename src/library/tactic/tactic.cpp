/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <chrono>
#include <string>
#include "util/luaref.h"
#include "util/sstream.h"
#include "util/interrupt.h"
#include "util/lazy_list_fn.h"
#include "kernel/instantiate.h"
#include "kernel/replace_visitor.h"
#include "library/kernel_bindings.h"
#include "library/tactic/tactic.h"
#include "library/io_state_stream.h"

namespace lean {
tactic tactic01(std::function<optional<proof_state>(environment const &, io_state const & ios, proof_state const &)> const & f) {
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

tactic tactic1(std::function<proof_state(environment const &, io_state const & ios, proof_state const &)> const & f) {
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

tactic cond(proof_state_pred const & p, tactic const & t1, tactic const & t2) {
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

tactic trace_tactic(std::string const & msg) {
    return tactic1([=](environment const &, io_state const & ios, proof_state const & s) -> proof_state {
            ios.get_diagnostic_channel() << msg << "\n";
            ios.get_diagnostic_channel().get_stream().flush();
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
    return tactic1([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state {
            diagnostic(env, ios) << s;
            ios.get_diagnostic_channel().get_stream().flush();
            return s;
        });
}

tactic suppress_trace(tactic const & t) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
            io_state new_ios(ios);
            std::shared_ptr<output_channel> out(std::make_shared<string_output_channel>());
            new_ios.set_diagnostic_channel(out);
            return t(env, new_ios, s);
        });
}

tactic then(tactic const & t1, tactic const & t2) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s1) -> proof_state_seq {
            return map_append(t1(env, ios, s1), [=](proof_state const & s2) {
                    check_interrupted();
                    return t2(env, ios, s2);
                }, "THEN tactical");
        });
}

tactic orelse(tactic const & t1, tactic const & t2) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
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

tactic try_for(tactic const & t, unsigned ms, unsigned check_ms) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
            return timeout(t(env, ios, s), ms, check_ms);
        });
}

tactic append(tactic const & t1, tactic const & t2) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
            return append(t1(env, ios, s), t2(env, ios, s), "APPEND tactical");
        });
}

tactic interleave(tactic const & t1, tactic const & t2) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
            return interleave(t1(env, ios, s), t2(env, ios, s), "INTERLEAVE tactical");
        });
}

tactic par(tactic const & t1, tactic const & t2, unsigned check_ms) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
            return par(t1(env, ios, s), t2(env, ios, s), check_ms);
        });
}

tactic repeat(tactic const & t) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s1) -> proof_state_seq {
            return repeat(s1, [=](proof_state const & s2) {
                    return t(env, ios, s2);
                }, "REPEAT tactical");
        });
}

tactic repeat_at_most(tactic const & t, unsigned k) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s1) -> proof_state_seq {
            return repeat_at_most(s1, [=](proof_state const & s2) {
                    return t(env, ios, s2);
                }, k, "REPEAT_AT_MOST tactical");
        });
}

tactic take(tactic const & t, unsigned k) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
            return take(k, t(env, ios, s));
        });
}

tactic assumption_tactic() {
    return tactic01([](environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            list<std::pair<name, expr>> proofs;
            goals new_gs = map_goals(s, [&](name const & gname, goal const & g) -> optional<goal> {
                    expr const & c  = g.get_conclusion();
                    optional<expr> pr;
                    for (auto const & p : g.get_hypotheses()) {
                        check_interrupted();
                        if (mlocal_type(p.first) == c) {
                            pr = p.first;
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
            return some(proof_state(s, new_gs, add_proofs(s.get_pb(), proofs)));
        });
}

tactic beta_tactic() {
    return tactic01([=](environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            bool reduced = false;
            goals new_gs = map_goals(s, [&](name const &, goal const & g) -> optional<goal> {
                    hypotheses new_hs = map(g.get_hypotheses(), [&](hypothesis const & h) {
                            expr new_h = update_mlocal(h.first, beta_reduce(mlocal_type(h.first)));
                            if (new_h != h.first)
                                reduced = true;
                            return hypothesis(new_h, h.second);
                        });
                    expr const & c = g.get_conclusion();
                    expr new_c     = beta_reduce(c);
                    if (new_c != c)
                        reduced = true;
                    return some(goal(new_hs, new_c));
                });
            return reduced ? some(proof_state(s, new_gs)) : none_proof_state();
        });
}

proof_state_seq focus_core(tactic const & t, name const & gname, environment const & env, io_state const & ios, proof_state const & s) {
    for (auto const & p : s.get_goals()) {
        if (p.first == gname) {
            proof_builder_fn pb = proof_builder_fn([=](proof_map const & m, substitution const &) -> expr { return find(m, gname); });
            cex_builder_fn cb = mk_cex_builder_for(gname);
            proof_state new_s(s, goals(p), pb, cb); // new state with singleton goal
            return map(t(env, ios, new_s), [=](proof_state const & s2) {
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
                    proof_builder_fn pb1 = s.get_pb();
                    proof_builder_fn pb2 = s2.get_pb();
                    proof_builder_fn new_pb = proof_builder_fn(
                        [=](proof_map const & m, substitution const & a) -> expr {
                            proof_map m1(m); // map for pb1
                            proof_map m2; // map for pb2
                            for (auto p : renamed_goals) {
                                m2.insert(p.first, find(m, p.second));
                                m1.erase(p.first);
                            }
                            m1.insert(gname, pb2(m2, a));
                            return pb1(m1, a);
                        });
                    cex_builder_fn cb1 = s.get_cb();
                    cex_builder_fn cb2 = s2.get_cb();
                    cex_builder_fn new_cb = cex_builder_fn(
                        [=](name const & n, optional<counterexample> const & cex, substitution const & a) -> counterexample {
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
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
            return focus_core(t, gname, env, ios, s);
        });
}

tactic focus(tactic const & t, int i) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
            if (optional<name> n = s.get_ith_goal_name(i))
                return focus_core(t, *n, env, ios, s);
            else
                return proof_state_seq();
        });
}

class unfold_core_fn : public replace_visitor {
protected:
    bool m_unfolded;

    virtual expr visit_app(expr const & e) {
        expr const & f = get_app_fn(e);
        if (is_constant(f)) {
            expr new_f = visit(f);
            bool modified = new_f != f;
            buffer<expr> new_args;
            get_app_args(e, new_args);
            for (unsigned i = 0; i < new_args.size(); i++) {
                expr arg    = new_args[i];
                new_args[i] = visit(arg);
                if (!modified && new_args[i] != arg)
                    modified = true;
            }
            if (is_lambda(f))
                return apply_beta(f, new_args.size(), new_args.data());
            else if (modified)
                return mk_app(f, new_args);
            else
                return e;
        } else {
            return replace_visitor::visit_app(e);
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

    virtual expr visit_constant(expr const & c) {
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
    environment m_env;

    virtual expr visit_constant(expr const & c) {
        optional<declaration> d = m_env.find(const_name(c));
        if (d && d->is_definition() && (!d->is_opaque() || d->get_module_idx() == 0)) {
            m_unfolded = true;
            return d->get_value();
        } else {
            return c;
        }
    }

public:
    unfold_all_fn(environment const & env):m_env(env) {}
};

optional<proof_state> unfold_tactic_core(unfold_core_fn & fn, proof_state const & s) {
    goals new_gs = map_goals(s, [&](name const &, goal const & g) -> optional<goal> {
            hypotheses new_hs = map(g.get_hypotheses(), [&](hypothesis const & h) {
                    expr l = update_mlocal(h.first, fn(mlocal_type(h.first)));
                    return hypothesis(l, h.second);
                });
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
    return tactic01([=](environment const & env, io_state const &, proof_state const & s) -> optional<proof_state> {
            optional<declaration> d = env.find(n);
            if (!d || !d->is_definition() || (d->is_opaque() && d->get_module_idx() != 0))
                return none_proof_state(); // tactic failed
            unfold_fn fn(n, d->get_value());
            return unfold_tactic_core(fn, s);
        });
}

tactic unfold_tactic() {
    return tactic01([=](environment const & env, io_state const &, proof_state const & s) -> optional<proof_state> {
            unfold_all_fn fn(env);
            return unfold_tactic_core(fn, s);
        });
}

DECL_UDATA(proof_state_seq)
static const struct luaL_Reg proof_state_seq_m[] = {
    {"__gc",            proof_state_seq_gc}, // never throws
    {0, 0}
};

static int proof_state_seq_next(lua_State * L) {
    proof_state_seq seq = to_proof_state_seq(L, lua_upvalueindex(1));
    auto p = seq.pull();
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

static int tactic_call_core(lua_State * L, tactic t, environment env, io_state ios, proof_state s) {
    return push_proof_state_seq_it(L, t(env, ios, s));
}

static int tactic_call(lua_State * L) {
    int nargs = lua_gettop(L);
    tactic t = to_tactic(L, 1);
    environment env = to_environment(L, 2);
    if (nargs == 3)
        return tactic_call_core(L, t, env, get_io_state(L), to_proof_state(L, 3));
    else
        return tactic_call_core(L, t, env, to_io_state(L, 3), to_proof_state(L, 4));
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
static int mk_lua_tactic01(lua_State * L) {
    luaL_checktype(L, 1, LUA_TFUNCTION); // user-fun
    luaref ref(L, 1);
    tactic t = tactic01([=](environment const & env, io_state const & ios, proof_state const & s) -> optional<proof_state> {
            ref.push();               // push user-fun on the stack
            push_environment(L, env); // push args...
            push_io_state(L, ios);
            push_proof_state(L, s);
            pcall(L, 3, 1, 0);
            optional<proof_state> r;
            if (is_proof_state(L, -1))
                r = to_proof_state(L, -1);
            lua_pop(L, 1);
            return r;
        });
    return push_tactic(L, t);
}

static int mk_lua_cond_tactic(lua_State * L, tactic t1, tactic t2) {
    luaL_checktype(L, 1, LUA_TFUNCTION); // user-fun
    luaref ref(L, 1);
    tactic t = tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
            return mk_proof_state_seq([=]() {
                    ref.push();               // push user-fun on the stack
                    push_environment(L, env); // push args...
                    push_io_state(L, ios);
                    push_proof_state(L, s);
                    pcall(L, 3, 1, 0);
                    bool cond = lua_toboolean(L, -1);
                    lua_pop(L, 1);
                    if (cond) {
                        return t1(env, ios, s).pull();
                    } else {
                        return t2(env, ios, s).pull();
                    }
                });
        });
    return push_tactic(L, t);
}

static int mk_lua_cond_tactic(lua_State * L) { return mk_lua_cond_tactic(L, to_tactic(L, 2), to_tactic(L, 3)); }
static int mk_lua_when_tactic(lua_State * L) { return mk_lua_cond_tactic(L, to_tactic(L, 2), id_tactic()); }
static int mk_id_tactic(lua_State * L)          {  return push_tactic(L, id_tactic()); }
static int mk_now_tactic(lua_State * L)         {  return push_tactic(L, now_tactic()); }
static int mk_fail_tactic(lua_State * L)        {  return push_tactic(L, fail_tactic()); }
static int mk_trace_tactic(lua_State * L)       {  return push_tactic(L, trace_tactic(luaL_checkstring(L, 1))); }
static int mk_assumption_tactic(lua_State * L)  {  return push_tactic(L, assumption_tactic()); }
static int mk_trace_state_tactic(lua_State * L) {  return push_tactic(L, trace_state_tactic()); }
static int mk_unfold_tactic(lua_State * L)      {
    int nargs = lua_gettop(L);
    if (nargs == 0)
        return push_tactic(L, unfold_tactic());
    else
        return push_tactic(L, unfold_tactic(to_name_ext(L, 1)));
}
static int mk_beta_tactic(lua_State * L) {  return push_tactic(L, beta_tactic()); }
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

void open_tactic(lua_State * L) {
    luaL_newmetatable(L, proof_state_seq_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, proof_state_seq_m, 0);
    SET_GLOBAL_FUN(proof_state_seq_pred, "is_proof_state_seq");

    luaL_newmetatable(L, tactic_mt);
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
    SET_GLOBAL_FUN(mk_unfold_tactic,      "unfold_tac");
    SET_GLOBAL_FUN(mk_beta_tactic,        "beta_tac");
    SET_GLOBAL_FUN(mk_lua_tactic01,       "tactic01");

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
