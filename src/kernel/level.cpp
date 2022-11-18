/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <algorithm>
#include <vector>
#include <unordered_set>
#include "runtime/debug.h"
#include "runtime/interrupt.h"
#include "runtime/hash.h"
#include "runtime/buffer.h"
#include "util/list.h"
#include "kernel/level.h"
#include "kernel/environment.h"

namespace lean {

extern "C" unsigned lean_level_hash(obj_arg l);
extern "C" unsigned lean_level_depth(obj_arg l);
extern "C" uint8 lean_level_has_mvar(obj_arg l);
extern "C" uint8 lean_level_has_param(obj_arg l);

extern "C" object * lean_level_mk_zero(object*);
extern "C" object * lean_level_mk_succ(obj_arg);
extern "C" object * lean_level_mk_mvar(obj_arg);
extern "C" object * lean_level_mk_param(obj_arg);
extern "C" object * lean_level_mk_max(obj_arg, obj_arg);
extern "C" object * lean_level_mk_imax(obj_arg, obj_arg);

level mk_succ(level const & l) { return level(lean_level_mk_succ(l.to_obj_arg())); }
level mk_max_core(level const & l1, level const & l2) { return level(lean_level_mk_max(l1.to_obj_arg(), l2.to_obj_arg())); }
level mk_imax_core(level const & l1, level const & l2) { return level(lean_level_mk_imax(l1.to_obj_arg(), l2.to_obj_arg())); }
level mk_univ_param(name const & n) { return level(lean_level_mk_param(n.to_obj_arg())); }
level mk_univ_mvar(name const & n) { return level(lean_level_mk_mvar(n.to_obj_arg())); }

unsigned level::hash() const { return lean_level_hash(to_obj_arg()); }
unsigned get_depth(level const & l) { return lean_level_depth(l.to_obj_arg()); }
bool has_param(level const & l) { return lean_level_has_param(l.to_obj_arg()); }
bool has_mvar(level const & l) { return lean_level_has_mvar(l.to_obj_arg()); }

bool is_explicit(level const & l) {
    switch (kind(l)) {
    case level_kind::Zero:
        return true;
    case level_kind::Param: case level_kind::MVar: case level_kind::Max: case level_kind::IMax:
        return false;
    case level_kind::Succ:
        return is_explicit(succ_of(l));
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

/** \brief Convert (succ^k l) into (l, k). If l is not a succ, then return (l, 0) */
pair<level, unsigned> to_offset(level l) {
    unsigned k = 0;
    while (is_succ(l)) {
        l = succ_of(l);
        k++;
    }
    return mk_pair(l, k);
}

unsigned to_explicit(level const & l) {
    lean_assert(is_explicit(l));
    return to_offset(l).second;
}

level mk_max(level const & l1, level const & l2)  {
    if (is_explicit(l1) && is_explicit(l2)) {
        return get_depth(l1) >= get_depth(l2) ? l1 : l2;
    } else if (l1 == l2) {
        return l1;
    } else if (is_zero(l1)) {
        return l2;
    } else if (is_zero(l2)) {
        return l1;
    } else if (is_max(l2) && (max_lhs(l2) == l1 || max_rhs(l2) == l1)) {
        return l2;  // if l2 == (max l1 l'), then max l1 l2 == l2
    } else if (is_max(l1) && (max_lhs(l1) == l2 || max_rhs(l1) == l2)) {
        return l1;  // if l1 == (max l2 l'), then max l1 l2 == l1
    } else {
        auto p1 = to_offset(l1);
        auto p2 = to_offset(l2);
        if (p1.first == p2.first) {
            lean_assert(p1.second != p2.second);
            return p1.second > p2.second ? l1 : l2;
        } else {
            return mk_max_core(l1, l2);
        }
    }
}

level mk_imax(level const & l1, level const & l2) {
    if (is_not_zero(l2))
        return mk_max(l1, l2);
    else if (is_zero(l2))
        return l2;  // imax u 0 = 0  for any u
    else if (is_zero(l1))
        return l2;  // imax 0 u = u  for any u
    else if (l1 == l2)
        return l1;  // imax u u = u
    else
        return mk_imax_core(l1, l2);
}

static level * g_level_zero = nullptr;
static level * g_level_one  = nullptr;
level const & mk_level_zero() { return *g_level_zero; }
level const & mk_level_one() { return *g_level_one; }
bool is_one(level const & l) { return l == mk_level_one(); }

bool operator==(level const & l1, level const & l2) {
    if (kind(l1) != kind(l2)) return false;
    if (hash(l1) != hash(l2)) return false;
    if (is_eqp(l1, l2))       return true;
    switch (kind(l1)) {
    case level_kind::Zero:
        return true;
    case level_kind::Param: case level_kind::MVar:
        return level_id(l1) == level_id(l2);
    case level_kind::Max: case level_kind::IMax: case level_kind::Succ:
        if (get_depth(l1) != get_depth(l2))
            return false;
        break;
    }
    switch (kind(l1)) {
    case level_kind::Zero: case level_kind::Param: case level_kind::MVar:
        lean_unreachable(); // LCOV_EXCL_LINE
    case level_kind::Max: case level_kind::IMax:
        return
            level_lhs(l1) == level_lhs(l2) &&
            level_rhs(l1) == level_rhs(l2);
    case level_kind::Succ:
        return succ_of(l1) == succ_of(l2);
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

extern "C" LEAN_EXPORT uint8 lean_level_eqv(object * l1, object * l2) {
    return is_equivalent(TO_REF(level, l1), TO_REF(level, l2));
}

extern "C" LEAN_EXPORT uint8 lean_level_eq(object * l1, object * l2) {
    return TO_REF(level, l1) == TO_REF(level, l2);
}

bool is_not_zero(level const & l) {
    switch (kind(l)) {
    case level_kind::Zero: case level_kind::Param: case level_kind::MVar:
        return false;
    case level_kind::Succ:
        return true;
    case level_kind::Max:
        return is_not_zero(max_lhs(l)) || is_not_zero(max_rhs(l));
    case level_kind::IMax:
        return is_not_zero(imax_rhs(l));
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool is_lt(level const & a, level const & b, bool use_hash) {
    if (is_eqp(a, b))              return false;
    unsigned da = get_depth(a);
    unsigned db = get_depth(b);
    if (da < db)                   return true;
    if (da > db)                   return false;
    if (kind(a) != kind(b))        return kind(a) < kind(b);
    if (use_hash) {
        if (hash(a) < hash(b))         return true;
        if (hash(a) > hash(b))         return false;
    }
    if (a == b)                    return false;
    switch (kind(a)) {
    case level_kind::Zero:
        lean_unreachable(); // LCOV_EXCL_LINE
    case level_kind::Param: case level_kind::MVar:
        return level_id(a) < level_id(b);
    case level_kind::Max: case level_kind::IMax:
        if (level_lhs(a) != level_lhs(b))
            return is_lt(level_lhs(a), level_lhs(b), use_hash);
        else
            return is_lt(level_rhs(a), level_rhs(b), use_hash);
    case level_kind::Succ:
        return is_lt(succ_of(a), succ_of(b), use_hash);
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool is_lt(levels const & as, levels const & bs, bool use_hash) {
    if (is_nil(as))
        return !is_nil(bs);
    if (is_nil(bs))
        return false;
    if (car(as) == car(bs))
        return is_lt(cdr(as), cdr(bs), use_hash);
    else
        return is_lt(car(as), car(bs), use_hash);
}

bool levels_has_param(b_obj_arg ls) {
    while (!is_scalar(ls)) {
        if (lean_level_has_param(cnstr_get(ls, 0))) return true;
        ls = cnstr_get(ls, 1);
    }
    return false;
}

bool levels_has_mvar(b_obj_arg ls) {
    while (!is_scalar(ls)) {
        if (lean_level_has_mvar(cnstr_get(ls, 0))) return true;
        ls = cnstr_get(ls, 1);
    }
    return false;
}

bool has_param(levels const & ls) { return levels_has_param(ls.raw()); }
bool has_mvar(levels const & ls) { return levels_has_mvar(ls.raw()); }

void for_each_level_fn::apply(level const & l) {
    if (!m_f(l))
        return;
    switch (l.kind()) {
    case level_kind::Succ:
        apply(succ_of(l)); break;
    case level_kind::Max: case level_kind::IMax:
        apply(level_lhs(l)); apply(level_rhs(l)); break;
    case level_kind::Zero: case level_kind::Param:
    case level_kind::MVar:
        break;
    }
}

level replace_level_fn::apply(level const & l) {
    optional<level> r = m_f(l);
    if (r)
        return *r;
    switch (l.kind()) {
    case level_kind::Succ:
        return update_succ(l, apply(succ_of(l)));
    case level_kind::Max: case level_kind::IMax: {
        level l1 = apply(level_lhs(l));
        level l2 = apply(level_rhs(l));
        return update_max(l, l1, l2);
    }
    case level_kind::Zero: case level_kind::Param: case level_kind::MVar:
        return l;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool occurs(level const & u, level const & l) {
    bool found = false;
    for_each(l, [&](level const & l) {
            if (found) return false;
            if (l == u) { found = true; return false; }
            return true;
        });
    return found;
}

optional<name> get_undef_param(level const & l, names const & ps) {
    optional<name> r;
    for_each(l, [&](level const & l) {
            if (!has_param(l) || r)
                return false;
            if (is_param(l) && std::find(ps.begin(), ps.end(), param_id(l)) == ps.end())
                r = param_id(l);
            return true;
        });
    return r;
}

level update_succ(level const & l, level const & new_arg) {
    if (is_eqp(succ_of(l), new_arg))
        return l;
    else
        return mk_succ(new_arg);
}

level update_max(level const & l, level const & new_lhs, level const & new_rhs) {
    if (is_eqp(level_lhs(l), new_lhs) && is_eqp(level_rhs(l), new_rhs))
        return l;
    else if (is_max(l))
        return mk_max(new_lhs, new_rhs);
    else
        return mk_imax(new_lhs, new_rhs);
}

level instantiate(level const & l, names const & ps, levels const & ls) {
    lean_assert(length(ps) == length(ls));
    return replace(l, [=](level const & l) {
            if (!has_param(l)) {
                return some_level(l);
            } else if (is_param(l)) {
                name const & id = param_id(l);
                names const *it1  = &ps;
                levels const *it2 = &ls;
                /* The assertion above ensures that !is_nil(*it2) is unnecessay, but we
                   we keep it here to ensure the lean_instantiate_lparams does not crash
                   at runtime when misused. */
                while (!is_nil(*it1) && !is_nil(*it2)) {
                    if (head(*it1) == id)
                        return some_level(head(*it2));
                    it1 = &tail(*it1);
                    it2 = &tail(*it2);
                }
                return some_level(l);
            } else {
                return none_level();
            }
        });
}

static void print(std::ostream & out, level l);

static void print_child(std::ostream & out, level const & l) {
    if (is_explicit(l) || is_param(l) || is_mvar(l)) {
        print(out, l);
    } else {
        out << "(";
        print(out, l);
        out << ")";
    }
}

static void print(std::ostream & out, level l) {
    if (is_explicit(l)) {
        out << get_depth(l);
    } else {
        switch (kind(l)) {
        case level_kind::Zero:
            lean_unreachable(); // LCOV_EXCL_LINE
        case level_kind::Param:
            out << param_id(l); break;
        case level_kind::MVar:
            out << "?" << mvar_id(l); break;
        case level_kind::Succ:
            out << "succ "; print_child(out, succ_of(l)); break;
        case level_kind::Max: case level_kind::IMax:
            if (is_max(l))
                out << "max ";
            else
                out << "imax ";
            print_child(out, level_lhs(l));
            // max and imax are right associative
            while (kind(level_rhs(l)) == kind(l)) {
                l = level_rhs(l);
                out << " ";
                print_child(out, level_lhs(l));
            }
            out << " ";
            print_child(out, level_rhs(l));
            break;
        }
    }
}

std::ostream & operator<<(std::ostream & out, level const & l) {
    print(out, l);
    return out;
}

// A total order on level expressions that has the following properties
//  - succ(l) is an immediate successor of l.
//  - zero is the minimal element.
// This total order is used in the normalization procedure.
static bool is_norm_lt(level const & a, level const & b) {
    if (is_eqp(a, b)) return false;
    auto p1 = to_offset(a);
    auto p2 = to_offset(b);
    level const & l1 = p1.first;
    level const & l2 = p2.first;
    if (l1 != l2) {
        if (kind(l1) != kind(l2)) return kind(l1) < kind(l2);
        switch (kind(l1)) {
        case level_kind::Zero: case level_kind::Succ:
            lean_unreachable(); // LCOV_EXCL_LINE
        case level_kind::Param: case level_kind::MVar:
            return level_id(l1) < level_id(l2);
        case level_kind::Max: case level_kind::IMax:
            if (level_lhs(l1) != level_lhs(l2))
                return is_norm_lt(level_lhs(l1), level_lhs(l2));
            else
                return is_norm_lt(level_rhs(l1), level_rhs(l2));
        }
        lean_unreachable(); // LCOV_EXCL_LINE
    } else {
        return p1.second < p2.second;
    }
}

void push_max_args(level const & l, buffer<level> & r) {
    if (is_max(l)) {
        push_max_args(max_lhs(l), r);
        push_max_args(max_rhs(l), r);
    } else {
        r.push_back(l);
    }
}

level mk_max(buffer<level> const & args) {
    lean_assert(!args.empty());
    unsigned nargs = args.size();
    if (nargs == 1) {
        return args[0];
    } else {
        lean_assert(nargs >= 2);
        level r = mk_max(args[nargs-2], args[nargs-1]);
        unsigned i = nargs-2;
        while (i > 0) {
            --i;
            r = mk_max(args[i], r);
        }
        return r;
    }
}

level mk_succ(level l, unsigned k) {
    while (k > 0) {
        --k;
        l = mk_succ(l);
    }
    return l;
}

level normalize(level const & l) {
    auto p = to_offset(l);
    level const & r = p.first;
    switch (kind(r)) {
    case level_kind::Succ:
        lean_unreachable(); // LCOV_EXCL_LINE
    case level_kind::Zero:   case level_kind::Param:
    case level_kind::MVar:
        return l;
    case level_kind::IMax: {
        auto l1 = normalize(imax_lhs(r));
        auto l2 = normalize(imax_rhs(r));
        return mk_succ(mk_imax(l1, l2), p.second);
    }
    case level_kind::Max: {
        buffer<level> todo;
        buffer<level> args;
        push_max_args(r, todo);
        for (level const & a : todo)
            push_max_args(normalize(a), args);
        std::sort(args.begin(), args.end(), is_norm_lt);
        buffer<level> & rargs = todo;
        rargs.clear();
        unsigned i = 0;
        if (is_explicit(args[i])) {
            // find max explicit univierse
            while (i+1 < args.size() && is_explicit(args[i+1]))
                i++;
            lean_assert(is_explicit(args[i]));
            unsigned k = to_offset(args[i]).second;
            // an explicit universe k is subsumed by succ^k(l)
            unsigned j = i+1;
            for (; j < args.size(); j++) {
                if (to_offset(args[j]).second >= k)
                    break;
            }
            if (j < args.size()) {
                // explicit universe was subsumed by succ^k'(l) where k' >= k
                i++;
            }
        }
        rargs.push_back(args[i]);
        auto p_prev = to_offset(args[i]);
        i++;
        for (; i < args.size(); i++) {
            auto p_curr = to_offset(args[i]);
            if (p_prev.first == p_curr.first) {
                if (p_prev.second < p_curr.second) {
                    p_prev = p_curr;
                    rargs.pop_back();
                    rargs.push_back(args[i]);
                }
            } else {
                p_prev = p_curr;
                rargs.push_back(args[i]);
            }
        }
        for (level & a : rargs)
            a = mk_succ(a, p.second);
        return mk_max(rargs);
    }}
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool is_equivalent(level const & lhs, level const & rhs) {
    check_system("level constraints");
    return lhs == rhs || normalize(lhs) == normalize(rhs);
}

bool is_geq_core(level l1, level l2) {
    if (l1 == l2 || is_zero(l2))
        return true;
    if (is_max(l2))
        return is_geq(l1, max_lhs(l2)) && is_geq(l1, max_rhs(l2));
    if (is_max(l1) && (is_geq(max_lhs(l1), l2) || is_geq(max_rhs(l1), l2)))
        return true;
    if (is_imax(l2))
        return is_geq(l1, imax_lhs(l2)) && is_geq(l1, imax_rhs(l2));
    if (is_imax(l1))
        return is_geq(imax_rhs(l1), l2);
    auto p1 = to_offset(l1);
    auto p2 = to_offset(l2);
    if (p1.first == p2.first || is_zero(p2.first))
        return p1.second >= p2.second;
    if (p1.second == p2.second && p1.second > 0)
        return is_geq(p1.first, p2.first);
    return false;
}
bool is_geq(level const & l1, level const & l2) {
    return is_geq_core(normalize(l1), normalize(l2));
}
levels lparams_to_levels(names const & ps) {
    buffer<level> ls;
    for (auto const & p : ps)
        ls.push_back(mk_univ_param(p));
    return levels(ls);
}

level::level():level(*g_level_zero) {
}

void initialize_level() {
    g_level_zero = new level(lean_level_mk_zero(box(0)));
    mark_persistent(g_level_zero->raw());
    g_level_one  = new level(mk_succ(*g_level_zero));
    mark_persistent(g_level_one->raw());
}

void finalize_level() {
    delete g_level_one;
    delete g_level_zero;
}
}
void print(lean::level const & l) { std::cout << l << std::endl; }
