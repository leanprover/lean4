/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "library/pos_info_provider.h"
#include "kernel/replace_fn.h"
#include "kernel/find_fn.h"

namespace lean {
const name * g_column_name = nullptr;
const name * g_row_name = nullptr;

expr unwrap_pos(expr const & e) {
    if (get_pos(e)) {
        auto const & e2 = mdata_expr(e);
        return unwrap_pos(e2);
    }
    return e;
}

expr save_pos(expr const & e, pos_info const & pos) {
    if (is_app(e))
        return e;
    kvmap m;
    m = set_nat(m, *g_row_name, pos.first);
    m = set_nat(m, *g_column_name, pos.second);
    return mk_mdata(m, unwrap_pos(e));
}

expr copy_pos(expr const & src, expr const & dest) {
    if (auto pos = get_pos(src))
        return save_pos(dest, *pos);
    else
        return dest;
}

optional<pos_info> get_pos(expr const & e) {
    if (is_mdata(e)) {
        kvmap const & m = mdata_data(e);
        auto const & column = get_nat(m, *g_column_name);
        auto const & row = get_nat(m, *g_row_name);
        if (column && row)
            return some(pos_info(row->get_small_value(), column->get_small_value()));
    }
    return optional<pos_info>();
}

bool contains_pos(expr const & e) {
    return !!find(e, [](expr const & e, unsigned) { return get_pos(e); });
}

char const * pos_info_provider::get_file_name() const {
    return "unknown";
}

format pos_info_provider::pp(expr const & e) const {
    try {
        auto p = get_pos_info_or_some(e);
        return format(get_file_name()) + format(":") + format(p.first) + format(":") + format(p.second) + format(":");
    } catch (exception &) {
        return format();
    }
}

void initialize_pos_info_provider() {
    g_column_name = new name("column");
    g_row_name = new name("row");
}

void finalize_pos_info_provider() {
    delete g_row_name;
    delete g_column_name;
}

optional<expr> is_local_p(expr const & e) {
    auto e2 = unwrap_pos(e);
    if (is_fvar(e2))
        return some_expr(e2);
    else
        return none_expr();
}
name const & local_name_p(expr const & e) { auto o = is_local_p(e); lean_assert(o); return local_name(*o); }
name const & local_pp_name_p(expr const & e) { auto o = is_local_p(e); lean_assert(o); return local_pp_name(*o); }
expr const & local_type_p(expr const & e) { auto o = is_local_p(e); lean_assert(o); return local_type(*o); }
binder_info local_info_p(expr const & e) { auto o = is_local_p(e); lean_assert(o); return local_info(*o); }
expr update_local_p(expr const & e, expr const & new_type) {
    return copy_pos(e, update_local(unwrap_pos(e), new_type));
}
expr update_local_p(expr const & e, expr const & new_type, binder_info bi) {
    return copy_pos(e, update_local(unwrap_pos(e), new_type, bi));
}
expr update_local_p(expr const & e, binder_info bi) {
    return copy_pos(e, update_local(unwrap_pos(e), bi));
}

expr abstract_p(expr const & e, unsigned n, expr const * subst) {
    lean_assert(std::all_of(subst, subst+n, [](expr const & e) { return !has_loose_bvars(e) && is_fvar(unwrap_pos(e)); }));
    if (!has_fvar(e))
        return e;
    return replace(e, [=](expr const & m, unsigned offset) -> optional<expr> {
        if (!has_fvar(m))
            return some_expr(m); // expression m does not contain free variables
        if (is_fvar(m)) {
            unsigned i = n;
            while (i > 0) {
                --i;
                if (fvar_name(unwrap_pos(subst[i])) == fvar_name(m))
                    return some_expr(mk_bvar(offset + n - i - 1));
            }
            return none_expr();
        }
        return none_expr();
    });
}

template<bool is_lambda>
static expr mk_binding_p(unsigned num, expr const * locals, expr const & b) {
    expr r     = abstract_p(b, num, locals);
    unsigned i = num;
    while (i > 0) {
        --i;
        expr const & l = locals[i];
        expr t = abstract_p(local_type_p(l), i, locals);
        if (is_lambda)
            r = mk_lambda(local_pp_name_p(l), t, r, local_info_p(l));
        else
            r = mk_pi(local_pp_name_p(l), t, r, local_info_p(l));
    }
    return r;
}

expr Pi_p(unsigned num, expr const * locals, expr const & b) { return mk_binding_p<false>(num, locals, b); }
expr Fun_p(unsigned num, expr const * locals, expr const & b) { return mk_binding_p<true>(num, locals, b); }
}
