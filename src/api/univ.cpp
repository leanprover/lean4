/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/sstream.h"
#include "api/name.h"
#include "api/string.h"
#include "api/univ.h"
#include "api/lean_univ.h"
namespace lean {
void to_buffer(unsigned sz, lean_univ const * us, buffer<level> & r) {
    check_nonnull(us);
    for (unsigned i = 0; i < sz; i++) {
        check_nonnull(us[i]);
        r.push_back(to_level_ref(us[i]));
    }
}
}
using namespace lean; // NOLINT

lean_bool lean_univ_mk_zero(lean_univ * r, lean_exception * ex) {
    LEAN_TRY;
    *r = of_level(new level());
    LEAN_CATCH;
}

lean_bool lean_univ_mk_succ(lean_univ u, lean_univ * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(u);
    *r = of_level(new level(mk_succ(to_level_ref(u))));
    LEAN_CATCH;
}

lean_bool lean_univ_mk_max(lean_univ u1, lean_univ u2, lean_univ * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(u1);
    check_nonnull(u2);
    *r = of_level(new level(mk_max(to_level_ref(u1), to_level_ref(u2))));
    LEAN_CATCH;
}

lean_bool lean_univ_mk_imax(lean_univ u1, lean_univ u2, lean_univ * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(u1);
    check_nonnull(u2);
    *r = of_level(new level(mk_imax(to_level_ref(u1), to_level_ref(u2))));
    LEAN_CATCH;
}

lean_bool lean_univ_mk_param(lean_name n, lean_univ * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    *r = of_level(new level(mk_param_univ(to_name_ref(n))));
    LEAN_CATCH;
}

lean_bool lean_univ_mk_global(lean_name n, lean_univ * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    *r = of_level(new level(mk_global_univ(to_name_ref(n))));
    LEAN_CATCH;
}

lean_bool lean_univ_mk_meta(lean_name n, lean_univ * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(n);
    *r = of_level(new level(mk_meta_univ(to_name_ref(n))));
    LEAN_CATCH;
}

lean_bool lean_univ_to_string(lean_univ u, char const ** r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(u);
    std::ostringstream out;
    out << pp(to_level_ref(u));
    *r = mk_string(out.str());
    LEAN_CATCH;
}

lean_bool lean_univ_to_string_using(lean_univ u, lean_options o, char const ** r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(u);
    check_nonnull(o);
    std::ostringstream out;
    out << mk_pair(pp(to_level_ref(u), to_options_ref(o)), to_options_ref(o));
    *r = mk_string(out.str());
    LEAN_CATCH;
}

void lean_univ_del(lean_univ u) {
    delete to_level(u);
}

lean_univ_kind lean_univ_get_kind(lean_univ u) {
    if (!u)
        return LEAN_UNIV_ZERO;
    switch (to_level_ref(u).kind()) {
    case level_kind::Zero:     return LEAN_UNIV_ZERO;
    case level_kind::Succ:     return LEAN_UNIV_SUCC;
    case level_kind::Max:      return LEAN_UNIV_MAX;
    case level_kind::IMax:     return LEAN_UNIV_IMAX;
    case level_kind::Param:    return LEAN_UNIV_PARAM;
    case level_kind::Global:   return LEAN_UNIV_GLOBAL;
    case level_kind::Meta:     return LEAN_UNIV_META;
    }
    lean_unreachable();
}

lean_bool lean_univ_eq(lean_univ u1, lean_univ u2, lean_bool * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(u1);
    check_nonnull(u2);
    *r = to_level_ref(u1) == to_level_ref(u2);
    LEAN_CATCH;
}

lean_bool lean_univ_lt(lean_univ u1, lean_univ u2, lean_bool * b, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(u1);
    check_nonnull(u2);
    *b = is_lt(to_level_ref(u1), to_level_ref(u2), false);
    LEAN_CATCH;
}

lean_bool lean_univ_quick_lt(lean_univ u1, lean_univ u2, lean_bool * b, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(u1);
    check_nonnull(u2);
    *b = is_lt(to_level_ref(u1), to_level_ref(u2), true);
    LEAN_CATCH;
}

lean_bool lean_univ_geq(lean_univ u1, lean_univ u2, lean_bool * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(u1);
    check_nonnull(u2);
    *r = is_geq(to_level_ref(u1), to_level_ref(u2));
    LEAN_CATCH;
}

lean_bool lean_univ_get_pred(lean_univ u, lean_univ * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(u);
    if (lean_univ_get_kind(u) != LEAN_UNIV_SUCC)
        throw exception("invalid argument, argument is not a successor universe");
    *r = of_level(new level(succ_of(to_level_ref(u))));
    LEAN_CATCH;
}

lean_bool lean_univ_get_max_lhs(lean_univ u, lean_univ * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(u);
    if (lean_univ_get_kind(u) == LEAN_UNIV_MAX)
        *r = of_level(new level(max_lhs(to_level_ref(u))));
    else if (lean_univ_get_kind(u) == LEAN_UNIV_IMAX)
        *r = of_level(new level(imax_lhs(to_level_ref(u))));
    else
        throw exception("invalid argument, argument is not a max/imax universe");
    LEAN_CATCH;
}

lean_bool lean_univ_get_max_rhs(lean_univ u, lean_univ * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(u);
    if (lean_univ_get_kind(u) == LEAN_UNIV_MAX)
        *r = of_level(new level(max_rhs(to_level_ref(u))));
    else if (lean_univ_get_kind(u) == LEAN_UNIV_IMAX)
        *r = of_level(new level(imax_rhs(to_level_ref(u))));
    else
        throw exception("invalid argument, argument is not a max/imax universe");
    LEAN_CATCH;
}

lean_bool lean_univ_get_name(lean_univ u, lean_name * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(u);
    if (lean_univ_get_kind(u) == LEAN_UNIV_PARAM)
        *r = of_name(new name(param_id(to_level_ref(u))));
    else if (lean_univ_get_kind(u) == LEAN_UNIV_GLOBAL)
        *r = of_name(new name(global_id(to_level_ref(u))));
    else if (lean_univ_get_kind(u) == LEAN_UNIV_META)
        *r = of_name(new name(meta_id(to_level_ref(u))));
    else
        throw exception("invalid argument, argument is not a parameter/global/meta universe");
    LEAN_CATCH;
}

lean_bool lean_univ_normalize(lean_univ u, lean_univ * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(u);
    *r = of_level(new level(normalize(to_level_ref(u))));
    LEAN_CATCH;
}

lean_bool lean_list_univ_mk_nil(lean_list_univ * r, lean_exception * ex) {
    LEAN_TRY;
    *r = of_list_level(new list<level>());
    LEAN_CATCH;
}

lean_bool lean_list_univ_mk_cons(lean_univ h, lean_list_univ t, lean_list_univ * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(h);
    check_nonnull(t);
    *r = of_list_level(new list<level>(to_level_ref(h), to_list_level_ref(t)));
    LEAN_CATCH;
}

void lean_list_univ_del(lean_list_univ l) {
    delete to_list_level(l);
}

lean_bool lean_list_univ_is_cons(lean_list_univ l) {
    return l && !is_nil(to_list_level_ref(l));
}

lean_bool lean_list_univ_eq(lean_list_univ l1, lean_list_univ l2, lean_bool * b, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(l1);
    check_nonnull(l2);
    *b = to_list_level_ref(l1) == to_list_level_ref(l2);
    LEAN_CATCH;
}

lean_bool lean_list_univ_head(lean_list_univ l, lean_univ * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(l);
    if (!lean_list_univ_is_cons(l))
        throw lean::exception("invalid argument, non-nil list expected");
    *r = of_level(new level(head(to_list_level_ref(l))));
    LEAN_CATCH;
}

lean_bool lean_list_univ_tail(lean_list_univ l, lean_list_univ * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(l);
    if (!lean_list_univ_is_cons(l))
        throw lean::exception("invalid argument, non-nil list expected");
    *r = of_list_level(new list<level>(tail(to_list_level_ref(l))));
    LEAN_CATCH;
}

/** \brief Instantiate the universe parameters names <tt>ns[i]</tt> with <tt>us[i]</tt> in \c u,
    and store the result in \c r.
    \remark \c ns and \c us are arrays of names and universes, and both have size \c sz.
*/
lean_bool lean_univ_instantiate(lean_univ u, lean_list_name ns, lean_list_univ us, lean_univ * r, lean_exception * ex) {
    LEAN_TRY;
    check_nonnull(u);
    check_nonnull(ns);
    check_nonnull(us);
    if (length(to_list_name_ref(ns)) != length(to_list_level_ref(us)))
        throw lean::exception("invalid arguments, the given lists must have the same length");
    *r = of_level(new level(instantiate(to_level_ref(u), to_list_name_ref(ns), to_list_level_ref(us))));
    LEAN_CATCH;
}
