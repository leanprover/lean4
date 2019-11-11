/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include "runtime/sstream.h"
#include "kernel/environment.h"
#include "library/metavar_context.h"
#include "library/type_context.h"

namespace lean {
class tactic_state_cell {
    MK_LEAN_RC();
    environment         m_env;
    options             m_options;
    name                m_decl_name;
    metavar_context     m_mctx;
    list<expr>          m_goals;
    expr                m_main;

    friend class tactic_state;
    void dealloc();
public:
    tactic_state_cell(environment const & env, options const & o, name const & decl_name,
                      metavar_context const & ctx, list<expr> const & gs,
                      expr const & main):
        m_rc(0), m_env(env), m_options(o), m_decl_name(decl_name),
        m_mctx(ctx), m_goals(gs), m_main(main) {}
};

class tactic_state {
private:
    tactic_state_cell * m_ptr;
    tactic_state_cell * steal_ptr() { tactic_state_cell * r = m_ptr; m_ptr = nullptr; return r; }
    friend class optional<tactic_state>;
    tactic_state():m_ptr(nullptr) {}
    explicit tactic_state(tactic_state_cell * ptr):m_ptr(ptr) { if (m_ptr) m_ptr->inc_ref(); }
    format pp_goal(formatter_factory const & fmtf, expr const & g, bool target_lhs_only = false) const;
public:
    tactic_state(environment const & env, options const & o, name const & decl_name,
                 metavar_context const & ctx, list<expr> const & gs,
                 expr const & main);
    tactic_state(tactic_state const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    tactic_state(tactic_state && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~tactic_state() { if (m_ptr) m_ptr->dec_ref(); }

    optional<expr> get_main_goal() const;
    optional<metavar_decl> get_main_goal_decl() const;
    tactic_state_cell * raw() const { return m_ptr; }
    options const & get_options() const { lean_assert(m_ptr); return m_ptr->m_options; }
    environment const & env() const { lean_assert(m_ptr); return m_ptr->m_env; }
    metavar_context const & mctx() const { lean_assert(m_ptr); return m_ptr->m_mctx; }
    list<expr> const & goals() const { lean_assert(m_ptr); return m_ptr->m_goals; }
    expr const & main() const { lean_assert(m_ptr); return m_ptr->m_main; }
    name const & decl_name() const { lean_assert(m_ptr); return m_ptr->m_decl_name; }

    tactic_state & operator=(tactic_state const & s) { LEAN_COPY_REF(s); }
    tactic_state & operator=(tactic_state && s) { LEAN_MOVE_REF(s); }

    friend void swap(tactic_state & a, tactic_state & b) { std::swap(a.m_ptr, b.m_ptr); }
    friend bool is_eqp(tactic_state const & a, tactic_state const & b) { return a.m_ptr == b.m_ptr; }

    format pp_core(formatter_factory const & fmtf, bool target_lhs_only = false) const;
    format pp_expr(formatter_factory const & fmtf, expr const & e) const;
    format pp_core(bool target_lhs_only = false) const;
    format pp() const;
    format pp_expr(expr const & e) const;
    format pp_goal(expr const & g) const;
};

inline bool operator==(tactic_state const & s1, tactic_state const & s2) { return is_eqp(s1, s2); }

SPECIALIZE_OPTIONAL_FOR_SMART_PTR(tactic_state)

inline optional<tactic_state> none_tactic_state() { return optional<tactic_state>(); }
inline optional<tactic_state> some_tactic_state(tactic_state const & e) { return optional<tactic_state>(e); }
inline optional<tactic_state> some_tactic_state(tactic_state && e) { return optional<tactic_state>(std::forward<tactic_state>(e)); }

tactic_state mk_tactic_state_for(environment const & env, options const & opts, name const & decl_name, metavar_context mctx,
                                 local_context const & lctx, expr const & type);
tactic_state mk_tactic_state_for(environment const & env, options const & opts, name const & decl_name,
                                 local_context const & lctx, expr const & type);
tactic_state mk_tactic_state_for_metavar(environment const & env, options const & opts, name const & decl_name,
                                         metavar_context const & mctx, expr const & mvar);

tactic_state set_options(tactic_state const & s, options const & o);
tactic_state set_env(tactic_state const & s, environment const & env);
tactic_state set_mctx(tactic_state const & s, metavar_context const & mctx);
tactic_state set_env_mctx(tactic_state const & s, environment const & env, metavar_context const & mctx);
tactic_state set_goals(tactic_state const & s, list<expr> const & gs);
tactic_state set_mctx_goals(tactic_state const & s, metavar_context const & mctx, list<expr> const & gs);
tactic_state set_env_mctx_goals(tactic_state const & s, environment const & env, metavar_context const & mctx, list<expr> const & gs);

/* Auxiliary function that returns an updated tactic_state such s' s.t. the metavariable context is mctx and
   the main goal is of the form

      lctx |- T

   for some type T.
   This function is particularly useful for implementing "converters" (aka "rewriters"). These
   kind of procedure doesn't care about goals, but env, options, mctx and lctx. */
tactic_state set_mctx_lctx(tactic_state const & s, metavar_context const & mctx, local_context const & lctx);

format pp_expr(tactic_state const & s, expr const & e);
format pp_indented_expr(tactic_state const & s, expr const & e);

type_context_old mk_type_context_for(tactic_state const & s, transparency_mode m = transparency_mode::Semireducible);
type_context_old mk_type_context_for(tactic_state const & s, local_context const & lctx, transparency_mode m = transparency_mode::Semireducible);
type_context_old mk_type_context_for(environment const & env, options const & o,
                                 metavar_context const & mctx, local_context const & lctx, transparency_mode m = transparency_mode::Semireducible);

type_context_old mk_cacheless_type_context_for(tactic_state const & s, transparency_mode m = transparency_mode::Semireducible);

#define lean_tactic_trace(N, S, Code) lean_trace(N, {   \
    type_context_old _ctx = mk_type_context_for(S);         \
    scope_trace_env _scope((S).env(), _ctx);            \
    Code                                                \
})

void initialize_tactic_state();
void finalize_tactic_state();
}
