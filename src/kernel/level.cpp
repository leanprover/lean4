/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <vector>
#include "util/safe_arith.h"
#include "util/buffer.h"
#include "util/rc.h"
#include "util/list.h"
#include "util/debug.h"
#include "util/hash.h"
#include "util/object_serializer.h"
#include "kernel/level.h"

namespace lean {
level_cell const & to_cell(level const & l) {
    return *l.m_ptr;
}

/** \brief Base class for representing universe level terms. */
struct level_cell {
    void dealloc();
    MK_LEAN_RC()
    level_kind m_kind;
    unsigned   m_hash;
    level_cell(level_kind k, unsigned h):m_rc(1), m_kind(k), m_hash(h) {}
};

unsigned hash(level const & l) { return to_cell(l).m_hash; }
level_kind kind(level const & l) { return to_cell(l).m_kind; }

struct level_composite : public level_cell {
    unsigned   m_depth;
    unsigned   m_param_range;
    unsigned   m_meta_range;
    level_composite(level_kind k, unsigned h, unsigned d, unsigned r1, unsigned r2):
        level_cell(k, h), m_depth(d), m_param_range(r1), m_meta_range(r2) {}
};

static bool is_composite(level const & l) {
    switch (kind(l)) {
    case level_kind::Succ: case level_kind::Max: case level_kind::IMax:
        return true;
    default:
        return false;
    }
}

static level_composite const & to_composite(level const & l) {
    lean_assert(is_composite(l));
    return static_cast<level_composite const &>(to_cell(l));
}

struct level_succ : public level_composite {
    level m_l;
    bool  m_explicit;
    level_succ(level const & l):
        level_composite(level_kind::Succ, hash(hash(l), 17u), get_depth(l) + 1, get_param_range(l), get_meta_range(l)),
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
                        std::max(get_param_range(l1), get_param_range(l2)),
                        std::max(get_meta_range(l1), get_meta_range(l2))),
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
    unsigned m_id;
    level_param_core(bool is_param, unsigned id):
        level_cell(is_param ? level_kind::Param : level_kind::Meta, hash(id, 11u)),
        m_id(id) {}
};

static bool is_param_core(level const & l) { return is_param(l) || is_meta(l); }

static level_param_core const & to_param_core(level const & l) {
    lean_assert(is_param_core(l));
    return static_cast<level_param_core const &>(to_cell(l));
}

unsigned param_id(level const & l) { lean_assert(is_param(l)); return to_param_core(l).m_id; }
unsigned meta_id(level const & l)  { lean_assert(is_meta(l));  return to_param_core(l).m_id; }

void level_cell::dealloc() {
    switch (m_kind) {
    case level_kind::Succ:
        delete static_cast<level_succ*>(this);
        break;
    case level_kind::Max: case level_kind::IMax:
        delete static_cast<level_max_core*>(this);
        break;
    case level_kind::Param: case level_kind::Meta:
        delete static_cast<level_param_core*>(this);
        break;
    case level_kind::Zero:
        delete this;
        break;
    }
}

unsigned get_depth(level const & l) {
    switch (kind(l)) {
    case level_kind::Zero: case level_kind::Param: case level_kind::Meta:
        return 1;
    case level_kind::Succ: case level_kind::Max: case level_kind::IMax:
        return to_composite(l).m_depth;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

unsigned get_param_range(level const & l) {
    switch (kind(l)) {
    case level_kind::Zero: case level_kind::Meta:
        return 0;
    case level_kind::Param:
        return to_param_core(l).m_id + 1;
    case level_kind::Succ: case level_kind::Max: case level_kind::IMax:
        return to_composite(l).m_param_range;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

unsigned get_meta_range(level const & l) {
    switch (kind(l)) {
    case level_kind::Zero: case level_kind::Param:
        return 0;
    case level_kind::Meta:
        return to_param_core(l).m_id + 1;
    case level_kind::Succ: case level_kind::Max: case level_kind::IMax:
        return to_composite(l).m_param_range;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

bool is_explicit(level const & l) {
    switch (kind(l)) {
    case level_kind::Zero:
        return true;
    case level_kind::Param: case level_kind::Meta: case level_kind::Max: case level_kind::IMax:
        return false;
    case level_kind::Succ:
        return to_level_succ(l).m_explicit;
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

level mk_succ(level const & l) {
    return level(new level_succ(l));
}

level mk_max(level const & l1, level const & l2)  {
    if (is_explicit(l1) && is_explicit(l2))
        return get_depth(l1) >= get_depth(l2) ? l1 : l2;
    else if (l1 == l2)
        return l1;
    else if (is_zero(l1))
        return l2;
    else if (is_zero(l2))
        return l1;
    else
        return level(new level_max_core(false, l1, l2));
}

level mk_imax(level const & l1, level const & l2) {
    if (is_not_zero(l2))
        return mk_max(l1, l2);
    else if (is_zero(l2))
        return l2;
    else if (l1 == l2)
        return l1;
    else
        return level(new level_max_core(true,  l1, l2));
}

level mk_param_univ(unsigned i) {
    return level(new level_param_core(true, i));
}

level mk_meta_univ(unsigned i) {
    return level(new level_param_core(false, i));
}

static level g_zero(new level_cell(level_kind::Zero, 7u));
static level g_one(mk_succ(g_zero));

level const & mk_level_zero() { return g_zero; }
level const & mk_level_one()  { return g_one; }

level::level():level(g_zero) {}
level::level(level_cell * ptr):m_ptr(ptr) { lean_assert(m_ptr->get_rc() == 1); }
level::level(level const & s):
    m_ptr(s.m_ptr) {
    if (m_ptr)
        m_ptr->inc_ref();
}
level::level(level && s):
    m_ptr(s.m_ptr) {
    s.m_ptr = nullptr;
}
level::~level() {
    if (m_ptr)
        m_ptr->dec_ref();
}

level & level::operator=(level const & l) { LEAN_COPY_REF(l); }
level & level::operator=(level&& l) { LEAN_MOVE_REF(l); }

bool operator==(level const & l1, level const & l2) {
    if (kind(l1) != kind(l2)) return false;
    if (hash(l1) != hash(l2)) return false;
    if (is_eqp(l1, l2))       return true;
    switch (kind(l1)) {
    case level_kind::Zero:
        return true;
    case level_kind::Param: case level_kind::Meta:
        return to_param_core(l1).m_id == to_param_core(l2).m_id;
    case level_kind::Max: case level_kind::IMax: case level_kind::Succ:
        if (to_composite(l1).m_depth != to_composite(l2).m_depth ||
            to_composite(l1).m_param_range != to_composite(l2).m_param_range ||
            to_composite(l1).m_meta_range != to_composite(l2).m_meta_range)
            return false;
        break;
    }
    switch (kind(l1)) {
    case level_kind::Zero: case level_kind::Param: case level_kind::Meta:
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
    case level_kind::Zero: case level_kind::Param: case level_kind::Meta:
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
bool is_lt(level const & a, level const & b) {
    if (is_eqp(a, b))              return false;
    unsigned da = get_depth(a);
    unsigned db = get_depth(b);
    if (da < db)                   return true;
    if (da > db)                   return false;
    if (kind(a) != kind(b))        return kind(a) < kind(b);
    if (hash(a) < hash(b))         return true;
    if (hash(a) > hash(b))         return false;
    if (a == b)                    return false;
    switch (kind(a)) {
    case level_kind::Zero:
        return false;
    case level_kind::Param: case level_kind::Meta:
        return to_param_core(a).m_id < to_param_core(b).m_id;
    case level_kind::Max: case level_kind::IMax:
        if (to_max_core(a).m_lhs != to_max_core(b).m_lhs)
            return is_lt(to_max_core(a).m_lhs, to_max_core(b).m_lhs);
        else
            return is_lt(to_max_core(a).m_rhs, to_max_core(b).m_rhs);
    case level_kind::Succ:
        return is_lt(succ_of(a), succ_of(b));
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

class level_serializer : public object_serializer<level, level::ptr_hash, level::ptr_eq> {
    typedef object_serializer<level, level::ptr_hash, level::ptr_eq> super;
public:
    void write(level const & l) {
        super::write(l, [&]() {
                serializer & s = get_owner();
                auto k = kind(l);
                s << static_cast<char>(k);
                switch (k) {
                case level_kind::Zero:
                    break;
                case level_kind::Param: case level_kind::Meta:
                    s << to_param_core(l).m_id;
                    break;
                case level_kind::Max: case level_kind::IMax:
                    write(to_max_core(l).m_lhs);
                    write(to_max_core(l).m_rhs);
                    break;
                case level_kind::Succ:
                    write(succ_of(l));
                    break;
                }
            });
    }
};

class level_deserializer : public object_deserializer<level> {
    typedef object_deserializer<level> super;
public:
    level read() {
        return super::read([&]() -> level {
                deserializer & d = get_owner();
                auto k = static_cast<level_kind>(d.read_char());
                switch (k) {
                case level_kind::Zero:
                    return mk_level_zero();
                case level_kind::Param: {
                    unsigned id = d.read_unsigned();
                    return mk_param_univ(id);
                }
                case level_kind::Meta: {
                    unsigned id = d.read_unsigned();
                    return mk_meta_univ(id);
                }
                case level_kind::Max: {
                    level lhs = read();
                    return mk_max(lhs, read());
                }
                case level_kind::IMax: {
                    level lhs = read();
                    return mk_imax(lhs, read());
                }
                case level_kind::Succ:
                    return mk_succ(read());
                }
                throw_corrupted_file();
            });
    }
};

struct level_sd {
    unsigned m_s_extid;
    unsigned m_d_extid;
    level_sd() {
        m_s_extid = serializer::register_extension([](){
                return std::unique_ptr<serializer::extension>(new level_serializer());
            });
        m_d_extid = deserializer::register_extension([](){
                return std::unique_ptr<deserializer::extension>(new level_deserializer());
            });
    }
};

static level_sd g_level_sd;

serializer & operator<<(serializer & s, level const & n) {
    s.get_extension<level_serializer>(g_level_sd.m_s_extid).write(n);
    return s;
}

level read_level(deserializer & d) {
    return d.get_extension<level_deserializer>(g_level_sd.m_d_extid).read();
}

static void print(std::ostream & out, level l);

static void print_child(std::ostream & out, level const & l) {
    if (is_explicit(l) || is_param(l) || is_meta(l)) {
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
        case level_kind::Param:
            out << "l_" << param_id(l); break;
        case level_kind::Meta:
            out << "?" << meta_id(l); break;
        case level_kind::Succ:
            out << "succ "; print_child(out, succ_of(l)); break;
        case level_kind::Max: case level_kind::IMax:
            if (is_max(l))
                out << "max ";
            else
                out << "imax ";
            print_child(out, max_lhs(l));
            // max and imax are right associative
            while (kind(max_rhs(l)) == kind(l)) {
                l = max_rhs(l);
                out << " ";
                print_child(out, max_lhs(l));
            }
            out << " ";
            print_child(out, max_rhs(l));
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
    if (is_explicit(l) || is_param(l) || is_meta(l)) {
        return pp(l, unicode, indent);
    } else {
        return paren(pp(l, unicode, indent));
    }
}

static char const * g_sub[10] = {
    "\u2080", "\u2081", "\u2082", "\u2083", "\u2084", "\u2085", "\u2086", "\u2087", "\u2088", "\u2089"
};

format pp(level l, bool unicode, unsigned indent) {
    if (is_explicit(l)) {
        lean_assert(get_depth(l) > 0);
        return format(get_depth(l) - 1);
    } else {
        switch (kind(l)) {
        case level_kind::Zero:
            lean_unreachable(); // LCOV_EXCL_LINE
        case level_kind::Param:
            if (unicode) {
                format r = format("ℓ");
                if (param_id(l) == 0)
                    return r;
                else if (param_id(l) <= 9)
                    return r + format(g_sub[param_id(l)]);
                else
                    return r + format{format("_"), format(param_id(l))};
            } else {
                return format{format("l_"), format(param_id(l))};
            }
        case level_kind::Meta:
            return format{format("?"), format(meta_id(l))};
        case level_kind::Succ:
            return group(compose(format("succ"), nest(indent, compose(line(), pp_child(succ_of(l), unicode, indent)))));
        case level_kind::Max: case level_kind::IMax: {
            format r = format(is_max(l) ? "max" : "imax");
            r += nest(indent, compose(line(), pp_child(max_lhs(l), unicode, indent)));
            // max and imax are right associative
            while (kind(max_rhs(l)) == kind(l)) {
                l = max_rhs(l);
                r += nest(indent, compose(line(), pp_child(max_lhs(l), unicode, indent)));
            }
            r += nest(indent, compose(line(), pp_child(max_rhs(l), unicode, indent)));
            return group(r);
        }}
        lean_unreachable(); // LCOV_EXCL_LINE
    }
}

format pp(level const & l, options const & opts) {
    return pp(l, get_pp_unicode(opts), get_pp_indent(opts));
}
}

void print(lean::level const & l) { std::cout << l << std::endl; }
