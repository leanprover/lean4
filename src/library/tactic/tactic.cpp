/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
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
#include "util/list_fn.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "library/kernel_bindings.h"
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
                    return t2(env, ios, s2);
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

tactic append(tactic const & t1, tactic const & t2) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & _s) -> proof_state_seq {
            proof_state s = _s.update_report_failure(false);
            return append(t1(env, ios, s), t2(env, ios, s), "APPEND tactical");
        });
}

tactic interleave(tactic const & t1, tactic const & t2) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & _s) -> proof_state_seq {
            proof_state s = _s.update_report_failure(false);
            return interleave(t1(env, ios, s), t2(env, ios, s), "INTERLEAVE tactical");
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

tactic assumption_tactic() {
    return tactic01([](environment const &, io_state const &, proof_state const & s) -> optional<proof_state> {
            substitution subst = s.get_subst();
            bool solved = false;
            goals new_gs = map_goals(s, [&](goal const & g) -> optional<goal> {
                    expr const & t  = g.get_type();
                    optional<expr> h;
                    buffer<expr> hyps;
                    g.get_hyps(hyps);
                    for (auto const & l : hyps) {
                        if (mlocal_type(l) == t) {
                            h = l;
                            break;
                        }
                    }
                    if (h) {
                        assign(subst, g, *h);
                        solved = true;
                        return optional<goal>();
                    } else {
                        return some(g);
                    }
                });
            if (solved)
                return some(proof_state(s, new_gs, subst));
            else
                return none_proof_state();
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
static int tactic_repeat_at_most(lua_State * L) {  return push_tactic(L, repeat_at_most(to_tactic(L, 1), luaL_checkinteger(L, 2))); }
static int tactic_take(lua_State * L)           {  return push_tactic(L, take(to_tactic(L, 1), luaL_checkinteger(L, 2))); }
static int tactic_try_for(lua_State * L)        {  return push_tactic(L, try_for(to_tactic(L, 1), luaL_checkinteger(L, 2))); }
static int tactic_using_params(lua_State * L)   {  return push_tactic(L, using_params(to_tactic(L, 1), to_options(L, 2))); }
static int tactic_focus(lua_State * L) {
    int nargs = lua_gettop(L);
    if (nargs == 1)
        return push_tactic(L, focus(to_tactic(L, 1)));
    else
        return push_tactic(L, focus(to_tactic(L, 1), lua_tointeger(L, 2)));
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
static int mk_assumption_tactic(lua_State * L)  {  return push_tactic(L, assumption_tactic()); }
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
    {"repeat",          safe_function<tactic_repeat>},
    {"repeat_at_most",  safe_function<tactic_repeat_at_most>},
    {"take",            safe_function<tactic_take>},
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
    SET_GLOBAL_FUN(mk_id_tactic,          "id_tac");
    SET_GLOBAL_FUN(mk_now_tactic,         "now_tac");
    SET_GLOBAL_FUN(mk_fail_tactic,        "fail_tac");
    SET_GLOBAL_FUN(mk_assumption_tactic,  "assumption_tac");
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
    SET_GLOBAL_FUN(mk_lua_cond_tactic,      "Cond");
    SET_GLOBAL_FUN(mk_lua_when_tactic,      "When");
    SET_GLOBAL_FUN(tactic_try_for,          "TryFor");
    SET_GLOBAL_FUN(tactic_take,             "Take");
    SET_GLOBAL_FUN(tactic_using_params,     "Using");
    SET_GLOBAL_FUN(tactic_using_params,     "UsingParams");
    SET_GLOBAL_FUN(tactic_focus,            "Focus");
}
}
