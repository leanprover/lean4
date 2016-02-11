/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <algorithm>
#include "util/buffer.h"
#include "util/sstream.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"
#include "kernel/abstract.h"
#include "kernel/type_checker.h"
#include "kernel/metavar.h"
#include "library/util.h"
#include "library/tactic/goal.h"

namespace lean {
old_local_context goal::to_local_context() const {
    buffer<expr> hyps;
    get_hyps(hyps);
    std::reverse(hyps.begin(), hyps.end());
    return old_local_context(to_list(hyps));
}

format goal::pp(formatter const & fmt) const {
    return pp(fmt, substitution());
}

format goal::pp(formatter const & fmt, substitution const & s) const {
    buffer<expr> hyps;
    get_app_args(m_meta, hyps);
    return format_goal(fmt, hyps, m_type, s);
}

expr goal::abstract(expr const & v) const {
    buffer<expr> locals;
    get_app_args(m_meta, locals);
    return Fun(locals, v);
}

expr goal::mk_meta(name const & n, expr const & type) const {
    buffer<expr> locals;
    expr this_mvar = get_app_args(m_meta, locals);
    expr mvar = copy_tag(this_mvar, mk_metavar(n, Pi(locals, type)));
    return copy_tag(m_meta, mk_app(mvar, locals));
}

goal goal::instantiate(substitution const & s) const {
    substitution s1(s);
    return goal(s1.instantiate_all(m_meta), s1.instantiate_all(m_type));
}

static bool validate_locals(expr const & r, unsigned num_locals, expr const * locals) {
    bool failed = false;
    for_each(r, [&](expr const & e, unsigned) {
            if (!has_local(e) || failed) return false;
            if (is_local(e) &&
                !std::any_of(locals, locals + num_locals,
                             [&](expr const & l) { return mlocal_name(l) == mlocal_name(e); })) {
                failed = true;
                return false;
            }
            return true;
        });
    return !failed;
}

bool goal::validate_locals() const {
    buffer<expr> locals;
    get_app_args(m_meta, locals);
    if (!::lean::validate_locals(m_type, locals.size(), locals.data()))
        return false;
    unsigned i = locals.size();
    while (i > 0) {
        --i;
        if (!::lean::validate_locals(mlocal_type(locals[i]), i, locals.data()))
            return false;
    }
    return true;
}

bool goal::validate(environment const & env) const {
    if (validate_locals()) {
        type_checker tc(env);
        return tc.is_def_eq(tc.check(m_meta).first, m_type).first;
    } else {
        return false;
    }
}

list<expr> goal::to_context() const {
    buffer<expr> locals;
    get_app_rev_args(m_meta, locals);
    return to_list(locals.begin(), locals.end());
}

template<typename F>
static optional<pair<expr, unsigned>> find_hyp_core(expr const & meta, F && pred) {
    expr const * it = &meta;
    unsigned i = 0;
    while (is_app(*it)) {
        expr const & h = app_arg(*it);
        if (pred(h))
            return some(mk_pair(h, i));
        i++;
        it = &app_fn(*it);
    }
    return optional<pair<expr, unsigned>>();
}

optional<pair<expr, unsigned>> goal::find_hyp(name const & uname) const {
    return find_hyp_core(m_meta, [&](expr const & h) { return local_pp_name(h) == uname; });
}

optional<pair<expr, unsigned>> goal::find_hyp_from_internal_name(name const & n) const {
    return find_hyp_core(m_meta, [&](expr const & h) { return mlocal_name(h) == n; });
}

void goal::get_hyps(buffer<expr> & r) const {
    get_app_args(m_meta, r);
}

void assign(substitution & s, goal const & g, expr const & v) {
    buffer<expr> hyps;
    expr const & mvar = get_app_args(g.get_meta(), hyps);
    s.assign(mvar, hyps, v);
}

static bool uses_name(name const & n, buffer<expr> const & locals) {
    for (expr const & local : locals) {
        if (is_local(local) && local_pp_name(local) == n)
            return true;
    }
    return false;
}

name get_unused_name(name const & prefix, unsigned & idx, buffer<expr> const & locals) {
    while (true) {
        name curr = prefix.append_after(idx);
        idx++;
        if (!uses_name(curr, locals))
            return curr;
    }
}

name get_unused_name(name const & prefix, buffer<expr> const & locals) {
    if (!uses_name(prefix, locals))
        return prefix;
    unsigned idx = 1;
    return get_unused_name(prefix, idx, locals);
}

name get_unused_name(name const & prefix, unsigned & idx, expr const & meta) {
    buffer<expr> locals;
    get_app_rev_args(meta, locals);
    return get_unused_name(prefix, idx, locals);
}

name get_unused_name(name const & prefix, expr const & meta) {
    buffer<expr> locals;
    get_app_rev_args(meta, locals);
    return get_unused_name(prefix, locals);
}

name goal::get_unused_name(name const & prefix, unsigned & idx) const {
    return ::lean::get_unused_name(prefix, idx, m_meta);
}

name goal::get_unused_name(name const & prefix) const {
    return ::lean::get_unused_name(prefix, m_meta);
}

io_state_stream const & operator<<(io_state_stream const & out, goal const & g) {
    options const & opts = out.get_options();
    out.get_stream() << mk_pair(g.pp(out.get_formatter()), opts);
    return out;
}
}
