/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <algorithm>
#include <vector>
#include <unordered_set>
#include "util/safe_arith.h"
#include "util/buffer.h"
#include "util/rc.h"
#include "util/list.h"
#include "util/debug.h"
#include "util/hash.h"
#include "util/interrupt.h"
#include "kernel/level.h"
#include "kernel/environment.h"

namespace lean {
level cache(level const & e);

level_cell const & to_cell(level const & l) {
    return *l.m_ptr;
}

/** \brief Base class for representing universe level terms. */
struct level_cell {
    void dealloc();
    MK_LEAN_RC()
    level_kind m_kind;
    unsigned   m_hash;
    level_cell(level_kind k, unsigned h):m_rc(0), m_kind(k), m_hash(h) {}
};

struct level_composite : public level_cell {
    unsigned   m_depth;
    unsigned   m_has_param:1;
    unsigned   m_has_global:1;
    unsigned   m_has_meta:1;
    level_composite(level_kind k, unsigned h, unsigned d, bool has_param, bool has_global, bool has_meta):
        level_cell(k, h), m_depth(d), m_has_param(has_param), m_has_global(has_global), m_has_meta(has_meta) {}
};

bool is_composite(level const & l) {
    switch (kind(l)) {
    case level_kind::Succ: case level_kind::Max: case level_kind::IMax:
        return true;
    case level_kind::Param: case level_kind::Global: case level_kind::Meta: case level_kind::Zero:
        return false;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

static level_composite const & to_composite(level const & l) {
    lean_assert(is_composite(l));
    return static_cast<level_composite const &>(to_cell(l));
}

struct level_succ : public level_composite {
    level m_l;
    bool  m_explicit;
    level_succ(level const & l):
        level_composite(level_kind::Succ, hash(hash(l), 17u), get_depth(l) + 1, has_param(l), has_global(l), has_meta(l)),
        m_l(l),
        m_explicit(is_explicit(l)) {}
};

level_succ const & to_level_succ(level const & l) { lean_assert(is_succ(l)); return static_cast<level_succ const &>(to_cell(l)); }
level const & succ_of(level const & l) { return to_level_succ(l).m_l; }

struct level_max_core : public level_composite {
    level m_lhs;
    level m_rhs;
    level_max_core(bool imax, level const & l1, level const & l2):
        level_composite(imax ? level_kind::IMax : level_kind::Max,
                        hash(hash(l1), hash(l2)),
                        std::max(get_depth(l1), get_depth(l2)) + 1,
                        has_param(l1)  || has_param(l2),
                        has_global(l1) || has_global(l2),
                        has_meta(l1)   || has_meta(l2)),
        m_lhs(l1), m_rhs(l2) {
        lean_assert(!is_explicit(l1) || !is_explicit(l2));
    }
};

static level_max_core const & to_max_core(level const & l) {
    lean_assert(is_max(l) || is_imax(l));
    return static_cast<level_max_core const &>(to_cell(l));
}

level const & max_lhs(level const & l) { lean_assert(is_max(l));   return to_max_core(l).m_lhs; }
level const & max_rhs(level const & l) { lean_assert(is_max(l));   return to_max_core(l).m_rhs; }
level const & imax_lhs(level const & l) { lean_assert(is_imax(l)); return to_max_core(l).m_lhs; }
level const & imax_rhs(level const & l) { lean_assert(is_imax(l)); return to_max_core(l).m_rhs; }

struct level_param_core : public level_cell {
    name m_id;
    level_param_core(level_kind k, name const & id):
        level_cell(k, hash(id.hash(), static_cast<unsigned>(k))),
        m_id(id) {
        lean_assert(k == level_kind::Meta || k == level_kind::Param || k == level_kind::Global);
    }
};

bool is_param_core(level const & l) { return is_param(l) || is_global(l) || is_meta(l); }

static level_param_core const & to_param_core(level const & l) {
    lean_assert(is_param_core(l));
    return static_cast<level_param_core const &>(to_cell(l));
}

name const & param_id(level const & l) { lean_assert(is_param(l)); return to_param_core(l).m_id; }
name const & global_id(level const & l)  { lean_assert(is_global(l));  return to_param_core(l).m_id; }
name const & meta_id(level const & l)  { lean_assert(is_meta(l));  return to_param_core(l).m_id; }
name const & level_id(level const & l) {
    lean_assert(is_param(l) || is_global(l) || is_meta(l));
    return to_param_core(l).m_id;
}

void level_cell::dealloc() {
    switch (m_kind) {
    case level_kind::Succ:
        delete static_cast<level_succ*>(this);
        break;
    case level_kind::Max: case level_kind::IMax:
        delete static_cast<level_max_core*>(this);
        break;
    case level_kind::Param: case level_kind::Global: case level_kind::Meta:
        delete static_cast<level_param_core*>(this);
        break;
    case level_kind::Zero:
        delete this;
        break;
    }
}

unsigned get_depth(level const & l) {
    switch (kind(l)) {
    case level_kind::Zero: case level_kind::Param: case level_kind::Global: case level_kind::Meta:
        return 1;
    case level_kind::Succ: case level_kind::Max: case level_kind::IMax:
        return to_composite(l).m_depth;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool has_param(level const & l) {
    switch (kind(l)) {
    case level_kind::Zero: case level_kind::Meta: case level_kind::Global:
        return false;
    case level_kind::Param:
        return true;
    case level_kind::Succ: case level_kind::Max: case level_kind::IMax:
        return to_composite(l).m_has_param;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool has_global(level const & l) {
    switch (kind(l)) {
    case level_kind::Zero: case level_kind::Param: case level_kind::Meta:
        return false;
    case level_kind::Global:
        return true;
    case level_kind::Succ: case level_kind::Max: case level_kind::IMax:
        return to_composite(l).m_has_param;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool has_meta(level const & l) {
    switch (kind(l)) {
    case level_kind::Zero: case level_kind::Param: case level_kind::Global:
        return false;
    case level_kind::Meta:
        return true;
    case level_kind::Succ: case level_kind::Max: case level_kind::IMax:
        return to_composite(l).m_has_meta;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool is_explicit(level const & l) {
    switch (kind(l)) {
    case level_kind::Zero:
        return true;
    case level_kind::Param: case level_kind::Global: case level_kind::Meta: case level_kind::Max: case level_kind::IMax:
        return false;
    case level_kind::Succ:
        return to_level_succ(l).m_explicit;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

level mk_succ(level const & l) {
    return cache(level(new level_succ(l)));
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
            return cache(level(new level_max_core(false, l1, l2)));
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
        return cache(level(new level_max_core(true,  l1, l2)));
}

level mk_param_univ(name const & n)  { return cache(level(new level_param_core(level_kind::Param, n))); }
level mk_global_univ(name const & n) { return cache(level(new level_param_core(level_kind::Global, n))); }
level mk_meta_univ(name const & n)   { return cache(level(new level_param_core(level_kind::Meta, n))); }

static level * g_level_zero = nullptr;
static level * g_level_one  = nullptr;
level const & mk_level_zero() { return *g_level_zero; }
level const & mk_level_one() { return *g_level_one; }
bool is_one(level const & l) { return l == mk_level_one(); }

typedef typename std::unordered_set<level, level_hash> level_cache;
LEAN_THREAD_VALUE(bool, g_level_cache_enabled, true);
MK_THREAD_LOCAL_GET_DEF(level_cache, get_level_cache);
bool enable_level_caching(bool f) {
    bool r = g_level_cache_enabled;
    g_level_cache_enabled = f;
    level_cache new_cache;
    get_level_cache().swap(new_cache);
    get_level_cache().insert(mk_level_zero());
    get_level_cache().insert(mk_level_one());
    return r;
}
level cache(level const & e) {
    if (g_level_cache_enabled) {
        level_cache & cache = get_level_cache();
        auto it = cache.find(e);
        if (it != cache.end()) {
            return *it;
        } else {
            cache.insert(e);
        }
    }
    return e;
}
bool is_cached(level const & e) {
    return get_level_cache().find(e) != get_level_cache().end();
}

level::level():level(mk_level_zero()) {}
level::level(level_cell * ptr):m_ptr(ptr) { if (m_ptr) m_ptr->inc_ref(); }
level::level(level const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
level::level(level && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
level::~level() { if (m_ptr) m_ptr->dec_ref(); }
level & level::operator=(level const & l) { LEAN_COPY_REF(l); }
level & level::operator=(level&& l) { LEAN_MOVE_REF(l); }
level_kind level::kind() const { return m_ptr->m_kind; }
unsigned level::hash() const { return m_ptr->m_hash; }

bool operator==(level const & l1, level const & l2) {
    if (kind(l1) != kind(l2)) return false;
    if (hash(l1) != hash(l2)) return false;
    if (is_eqp(l1, l2))       return true;
    switch (kind(l1)) {
    case level_kind::Zero:
        return true;
    case level_kind::Param: case level_kind::Global: case level_kind::Meta:
        return to_param_core(l1).m_id == to_param_core(l2).m_id;
    case level_kind::Max: case level_kind::IMax: case level_kind::Succ:
        if (to_composite(l1).m_depth != to_composite(l2).m_depth)
            return false;
        break;
    }
    switch (kind(l1)) {
    case level_kind::Zero: case level_kind::Param: case level_kind::Global: case level_kind::Meta:
        lean_unreachable(); // LCOV_EXCL_LINE
    case level_kind::Max: case level_kind::IMax:
        return
            to_max_core(l1).m_lhs == to_max_core(l2).m_lhs &&
            to_max_core(l1).m_rhs == to_max_core(l2).m_rhs;
    case level_kind::Succ:
        if (is_explicit(l1) != is_explicit(l2)) {
            return false;
        } else if (is_explicit(l1)) {
            lean_assert(get_depth(l1) == get_depth(l2));
            // the depths are equal, then l1 and l2 must be the same universe
            return true;
        } else {
            return succ_of(l1) == succ_of(l2);
        }
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool is_not_zero(level const & l) {
    switch (kind(l)) {
    case level_kind::Zero: case level_kind::Param: case level_kind::Global: case level_kind::Meta:
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

// Monotonic total order on universe level terms.
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
    case level_kind::Param: case level_kind::Global: case level_kind::Meta:
        return to_param_core(a).m_id < to_param_core(b).m_id;
    case level_kind::Max: case level_kind::IMax:
        if (to_max_core(a).m_lhs != to_max_core(b).m_lhs)
            return is_lt(to_max_core(a).m_lhs, to_max_core(b).m_lhs, use_hash);
        else
            return is_lt(to_max_core(a).m_rhs, to_max_core(b).m_rhs, use_hash);
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

bool has_param(levels const & ls) { return std::any_of(ls.begin(), ls.end(), [](level const & l) { return has_param(l); }); }
bool has_global(levels const & ls) { return std::any_of(ls.begin(), ls.end(), [](level const & l) { return has_global(l); }); }
bool has_meta(levels const & ls) { return std::any_of(ls.begin(), ls.end(), [](level const & l) { return has_meta(l); }); }

void for_each_level_fn::apply(level const & l) {
    if (!m_f(l))
        return;
    switch (l.kind()) {
    case level_kind::Succ:                          apply(succ_of(l)); break;
    case level_kind::Max: case level_kind::IMax:    apply(to_max_core(l).m_lhs); apply(to_max_core(l).m_rhs); break;
    case level_kind::Zero: case level_kind::Param:
    case level_kind::Meta: case level_kind::Global: break;
    }
}

level replace_level_fn::apply(level const & l) {
    optional<level> r = m_f(l);
    if (r)
        return *r;
    switch (l.kind()) {
    case level_kind::Succ:
        return update_succ(l, apply(succ_of(l)));
    case level_kind::Max: case level_kind::IMax:
        return update_max(l, apply(to_max_core(l).m_lhs), apply(to_max_core(l).m_rhs));
    case level_kind::Zero: case level_kind::Param: case level_kind::Meta: case level_kind::Global:
        return l;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

optional<name> get_undef_param(level const & l, level_param_names const & ps) {
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

optional<name> get_undef_global(level const & l, environment const & env) {
    optional<name> r;
    for_each(l, [&](level const & l) {
            if (!has_global(l) || r)
                return false;
            if (is_global(l) && !env.is_universe(global_id(l)))
                r = global_id(l);
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
    if (is_eqp(to_max_core(l).m_lhs, new_lhs) && is_eqp(to_max_core(l).m_rhs, new_rhs))
        return l;
    else if (is_max(l))
        return mk_max(new_lhs, new_rhs);
    else
        return mk_imax(new_lhs, new_rhs);
}

level instantiate(level const & l, level_param_names const & ps, levels const & ls) {
    lean_assert(length(ps) == length(ls));
    return replace(l, [=](level const & l) {
            if (!has_param(l)) {
                return some_level(l);
            } else if (is_param(l)) {
                name const & id = param_id(l);
                list<name> const *it1 = &ps;
                list<level> const * it2 = &ls;
                while (!is_nil(*it1)) {
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
    if (is_explicit(l) || is_param(l) || is_meta(l) || is_global(l)) {
        print(out, l);
    } else {
        out << "(";
        print(out, l);
        out << ")";
    }
}

static void print(std::ostream & out, level l) {
    if (is_explicit(l)) {
        lean_assert(get_depth(l) > 0);
        out << get_depth(l) - 1;
    } else {
        switch (kind(l)) {
        case level_kind::Zero:
            lean_unreachable(); // LCOV_EXCL_LINE
        case level_kind::Param: case level_kind::Global:
            out << to_param_core(l).m_id; break;
        case level_kind::Meta:
            out << "?" << meta_id(l); break;
        case level_kind::Succ:
            out << "succ "; print_child(out, succ_of(l)); break;
        case level_kind::Max: case level_kind::IMax:
            if (is_max(l))
                out << "max ";
            else
                out << "imax ";
            print_child(out, to_max_core(l).m_lhs);
            // max and imax are right associative
            while (kind(to_max_core(l).m_rhs) == kind(l)) {
                l = to_max_core(l).m_rhs;
                out << " ";
                print_child(out, to_max_core(l).m_lhs);
            }
            out << " ";
            print_child(out, to_max_core(l).m_rhs);
            break;
        }
    }
}

std::ostream & operator<<(std::ostream & out, level const & l) {
    print(out, l);
    return out;
}

format pp(level l, bool unicode, unsigned indent);

static format pp_child(level const & l, bool unicode, unsigned indent) {
    if (is_explicit(l) || is_param(l) || is_meta(l) || is_global(l)) {
        return pp(l, unicode, indent);
    } else {
        return paren(pp(l, unicode, indent));
    }
}

format pp(level l, bool unicode, unsigned indent) {
    if (is_explicit(l)) {
        lean_assert(get_depth(l) > 0);
        return format(get_depth(l) - 1);
    } else {
        switch (kind(l)) {
        case level_kind::Zero:
            lean_unreachable(); // LCOV_EXCL_LINE
        case level_kind::Param: case level_kind::Global:
            return format(to_param_core(l).m_id);
        case level_kind::Meta:
            return format("?") + format(meta_id(l));
        case level_kind::Succ: {
            auto p = to_offset(l);
            return pp_child(p.first, unicode, indent) + format("+") + format(p.second);
        }
        case level_kind::Max: case level_kind::IMax: {
            format r = format(is_max(l) ? "max" : "imax");
            r += nest(indent, compose(line(), pp_child(to_max_core(l).m_lhs, unicode, indent)));
            // max and imax are right associative
            while (kind(to_max_core(l).m_rhs) == kind(l)) {
                l = to_max_core(l).m_rhs;
                r += nest(indent, compose(line(), pp_child(to_max_core(l).m_lhs, unicode, indent)));
            }
            r += nest(indent, compose(line(), pp_child(to_max_core(l).m_rhs, unicode, indent)));
            return group(r);
        }}
        lean_unreachable(); // LCOV_EXCL_LINE
    }
}

format pp(level const & l, options const & opts) {
    return pp(l, get_pp_unicode(opts), get_pp_indent(opts));
}

format pp(level const & lhs, level const & rhs, bool unicode, unsigned indent) {
    format leq = unicode ? format("≤") : format("<=");
    return group(pp(lhs, unicode, indent) + space() + leq + line() + pp(rhs, unicode, indent));
}

format pp(level const & lhs, level const & rhs, options const & opts) {
    return pp(lhs, rhs, get_pp_unicode(opts), get_pp_indent(opts));
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
        case level_kind::Param: case level_kind::Global: case level_kind::Meta:
            return to_param_core(l1).m_id < to_param_core(l2).m_id;
        case level_kind::Max: case level_kind::IMax:
            if (to_max_core(l1).m_lhs != to_max_core(l2).m_lhs)
                return is_norm_lt(to_max_core(l1).m_lhs, to_max_core(l2).m_lhs);
            else
                return is_norm_lt(to_max_core(l1).m_rhs, to_max_core(l2).m_rhs);
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
    case level_kind::Global: case level_kind::Meta:
        return l;
    case level_kind::IMax: {
        auto l1 = normalize(imax_lhs(r));
        auto l2 = normalize(imax_rhs(r));
        if (!is_eqp(l1, imax_lhs(r)) || !is_eqp(l2, imax_rhs(r)))
            return mk_succ(mk_imax(l1, l2), p.second);
        else
            return l;
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
levels param_names_to_levels(level_param_names const & ps) {
    return map2<level>(ps, [](name const & p) { return mk_param_univ(p); });
}

void initialize_level() {
    g_level_zero = new level(new level_cell(level_kind::Zero, 7u));
    g_level_one  = new level(new level_succ(*g_level_zero));
}

void finalize_level() {
    enable_level_caching(false);
    delete g_level_one;
    delete g_level_zero;
}
}
void print(lean::level const & l) { std::cout << l << std::endl; }
