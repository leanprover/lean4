/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/constants.h"
#include "library/type_context.h"
#include "library/pp_options.h"
#include "library/trace.h"
#include "library/vm/vm_environment.h"
#include "library/vm/vm_format.h"
#include "library/vm/vm_expr.h"
#include "library/tactic/tactic_state.h"

namespace lean {
void tactic_state_cell::dealloc() {
    this->~tactic_state_cell();
    get_vm_allocator().deallocate(sizeof(tactic_state_cell), this);
}

tactic_state::tactic_state(environment const & env, options const & o, metavar_context const & ctx,
                           list<expr> const & gs, expr const & main) {
    m_ptr = new (get_vm_allocator().allocate(sizeof(tactic_state_cell))) tactic_state_cell(env, o, ctx, gs, main);
}

optional<metavar_decl> tactic_state::get_main_goal() const {
    if (empty(goals()))
        return optional<metavar_decl>();
    return mctx().get_metavar_decl(head(goals()));
}

tactic_state mk_tactic_state_for(environment const & env, options const & o, local_context const & lctx, expr const & type) {
    metavar_context mctx;
    expr main = mctx.mk_metavar_decl(lctx, type);
    return tactic_state(env, o, mctx, list<expr>(main), main);
}

tactic_state set_options(tactic_state const & s, options const & o) {
    return tactic_state(s.env(), o, s.mctx(), s.goals(), s.main());
}

tactic_state set_env(tactic_state const & s, environment const & env) {
    return tactic_state(env, s.get_options(), s.mctx(), s.goals(), s.main());
}

tactic_state set_mctx(tactic_state const & s, metavar_context const & mctx) {
    return tactic_state(s.env(), s.get_options(), mctx, s.goals(), s.main());
}

tactic_state set_goals(tactic_state const & s, list<expr> const & gs) {
    return tactic_state(s.env(), s.get_options(), s.mctx(), gs, s.main());
}

tactic_state set_mctx_goals(tactic_state const & s, metavar_context const & mctx, list<expr> const & gs) {
    return tactic_state(s.env(), s.get_options(), mctx, gs, s.main());
}

format tactic_state::pp_expr(formatter_factory const & fmtf, expr const & e) const {
    list<expr> const & gs  = goals();
    local_context lctx;
    if (gs) {
        if (auto d = mctx().get_metavar_decl(head(gs))) {
            lctx = d->get_context();
        }
    }
    metavar_context mctx_tmp   = mctx();
    type_context ctx(env(), get_options(), mctx_tmp, lctx, transparency_mode::All);
    formatter fmt = fmtf(env(), get_options(), ctx);
    return fmt(e);
}

format tactic_state::pp_goal(formatter_factory const & fmtf, expr const & g) const {
    metavar_decl decl          = *mctx().get_metavar_decl(g);
    local_context const & lctx = decl.get_context();
    metavar_context mctx_tmp   = mctx();
    type_context ctx(env(), get_options(), mctx_tmp, lctx, transparency_mode::All);
    formatter fmt              = fmtf(env(), get_options(), ctx);
    format r                   = lctx.pp(fmt);
    unsigned indent            = get_pp_indent(get_options());
    bool unicode               = get_pp_unicode(get_options());
    if (!lctx.empty())
        r += line();
    format turnstile           = unicode ? format("\u22A2") /* ⊢ */ : format("|-");
    r += turnstile + space() + nest(indent, fmt(decl.get_type()));
    if (get_pp_goal_compact(get_options()))
        r = group(r);
    return r;
}

format tactic_state::pp(formatter_factory const & fmtf) const {
    format r;
    bool first = true;
    for (auto const & g : goals()) {
        if (first) first = false; else r += line() + line();
        r += pp_goal(fmtf, g);
    }
    if (first) r = format("no goals");
    return r;
}

struct vm_tactic_state : public vm_external {
    tactic_state m_val;
    vm_tactic_state(tactic_state const & v):m_val(v) {}
    virtual void dealloc() override {
        this->~vm_tactic_state(); get_vm_allocator().deallocate(sizeof(vm_tactic_state), this);
    }
};

tactic_state const & to_tactic_state(vm_obj const & o) {
    lean_assert(is_external(o));
    lean_assert(dynamic_cast<vm_tactic_state*>(to_external(o)));
    return static_cast<vm_tactic_state*>(to_external(o))->m_val;
}

vm_obj to_obj(tactic_state const & s) {
    return mk_vm_external(new (get_vm_allocator().allocate(sizeof(vm_tactic_state))) vm_tactic_state(s));
}

vm_obj tactic_state_env(vm_obj const & s) {
    return to_obj(to_tactic_state(s).env());
}

vm_obj tactic_state_to_format(vm_obj const & s) {
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    return to_obj(to_tactic_state(s).pp(fmtf));
}

vm_obj tactic_state_format_expr(vm_obj const & s, vm_obj const & e) {
    formatter_factory const & fmtf = get_global_ios().get_formatter_factory();
    return to_obj(to_tactic_state(s).pp_expr(fmtf, to_expr(e)));
}

vm_obj mk_tactic_success(vm_obj const & a, tactic_state const & s) {
    return mk_vm_constructor(0, a, to_obj(s));
}

vm_obj mk_tactic_success(tactic_state const & s) {
    return mk_tactic_success(mk_vm_unit(), s);
}

vm_obj mk_tactic_exception(vm_obj const & fn) {
    return mk_vm_constructor(1, fn);
}

vm_obj mk_tactic_exception(format const & fmt) {
    vm_state const & s = get_vm_state();
    vm_decl K = *s.get_decl(get_combinator_K_name());
    return mk_tactic_exception(mk_vm_closure(K.get_idx(), mk_vm_unit(), mk_vm_unit(), to_obj(fmt)));
}

vm_obj mk_tactic_exception(char const * msg) {
    return mk_tactic_exception(format(msg));
}

vm_obj mk_no_goals_exception() {
    return mk_tactic_exception("tactic failed, there are no goals to be solved");
}

struct type_context_cache_helper {
    typedef std::unique_ptr<type_context_cache> cache_ptr;
    cache_ptr m_cache_ptr;

    void reset(environment const & env, options const & o) {
        m_cache_ptr.reset(new type_context_cache(env, o));
    }

    bool compatible_env(environment const & env) {
        environment const & curr_env = m_cache_ptr->env();
        return env.is_descendant(curr_env) && curr_env.is_descendant(env);
    }

    void ensure_compatible(environment const & env, options const & o) {
        if (!m_cache_ptr || !compatible_env(env) || !is_eqp(o, m_cache_ptr->get_options()))
            reset(env, o);
    }
};

MK_THREAD_LOCAL_GET_DEF(type_context_cache_helper, get_tch);

type_context_cache & get_type_context_cache_for(environment const & env, options const & o) {
    get_tch().ensure_compatible(env, o);
    return *get_tch().m_cache_ptr.get();
}

type_context_cache & get_type_context_cache_for(tactic_state const & s) {
    return get_type_context_cache_for(s.env(), s.get_options());
}

void initialize_tactic_state() {
    DECLARE_VM_BUILTIN(name({"tactic_state", "env"}),         tactic_state_env);
    DECLARE_VM_BUILTIN(name({"tactic_state", "format_expr"}), tactic_state_format_expr);
    DECLARE_VM_BUILTIN(name({"tactic_state", "to_format"}),   tactic_state_to_format);
}

void finalize_tactic_state() {
}
}
