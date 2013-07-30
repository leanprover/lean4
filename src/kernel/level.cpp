/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "level.h"
#include "rc.h"
#include "debug.h"

namespace lean {
struct level_cell {
    void dealloc();
    MK_LEAN_RC()
    level_kind m_kind;
    level_cell(level_kind k):m_rc(1), m_kind(k) {}
};
struct level_uvar : public level_cell {
    name m_name;
    uvar m_uvar;
    level_uvar(name const & n, uvar u):level_cell(level_kind::UVar), m_name(n), m_uvar(u) {}
};
struct level_lift : public level_cell {
    level    m_l;
    unsigned m_k;
    level_lift(level const & l, unsigned k):level_cell(level_kind::Lift), m_l(l), m_k(k) {}
};
struct level_max : public level_cell {
    level m_l1;
    level m_l2;
    level_max(level const & l1, level const & l2):level_cell(level_kind::Max), m_l1(l1), m_l2(l2) {}
};
void level_cell::dealloc() {
    switch (m_kind) {
    case level_kind::UVar:    delete static_cast<level_uvar*>(this); break;
    case level_kind::Lift:    delete static_cast<level_lift*>(this); break;
    case level_kind::Max:     delete static_cast<level_max*> (this); break;
    }
}
level::level():                                  m_ptr(new level_uvar(name("bot"), 0)) { lean_assert(uvar_name(*this) == name("bot")); }
level::level(name const & n, uvar u):            m_ptr(new level_uvar(n, u)) {}
level::level(level const & l, unsigned k):       m_ptr(new level_lift(l, k)) {}
level::level(level const & l1, level const & l2):m_ptr(new level_max(l1, l2)) {}
level::level(level const & s):
    m_ptr(s.m_ptr) {
    if (m_ptr)
        m_ptr->inc_ref();
}
level::level(level && s):
    m_ptr(s.m_ptr) {
    s.m_ptr = 0;
}
level::~level() {
    if (m_ptr)
        m_ptr->dec_ref();
}

level_kind    kind       (level const & l) { lean_assert(l.m_ptr); return l.m_ptr->m_kind; }
name const &  uvar_name  (level const & l) { lean_assert(is_uvar(l)); return static_cast<level_uvar*>(l.m_ptr)->m_name; }
uvar          uvar_idx   (level const & l) { lean_assert(is_uvar(l)); return static_cast<level_uvar*>(l.m_ptr)->m_uvar; }
level const & lift_of    (level const & l) { lean_assert(is_lift(l)); return static_cast<level_lift*>(l.m_ptr)->m_l; }
unsigned      lift_offset(level const & l) { lean_assert(is_lift(l)); return static_cast<level_lift*>(l.m_ptr)->m_k; }
level const & max_level1 (level const & l) { lean_assert(is_max(l));  return static_cast<level_max*>(l.m_ptr)->m_l1; }
level const & max_level2 (level const & l) { lean_assert(is_max(l));  return static_cast<level_max*>(l.m_ptr)->m_l2; }

level & level::operator=(level const & l) { LEAN_COPY_REF(level, l); }
level & level::operator=(level&& l) { LEAN_MOVE_REF(level, l); }

bool operator==(level const & l1, level const & l2) {
    if (kind(l1) != kind(l2)) return false;
    switch (kind(l1)) {
    case level_kind::UVar: return uvar_idx(l1)   == uvar_idx(l2);
    case level_kind::Lift: return lift_of(l1)    == lift_of(l2)    && lift_offset(l1) == lift_offset(l2);
    case level_kind::Max:  return max_level1(l1) == max_level1(l2) && max_level2(l1)  == max_level2(l2);
    }
    lean_unreachable();
    return false;
}

std::ostream & operator<<(std::ostream & out, level const & l) {
    switch (kind(l)) {
    case level_kind::UVar: out << uvar_name(l);                                            return out;
    case level_kind::Lift: out << lift_of(l) << " + " << lift_offset(l);                   return out;
    case level_kind::Max:  out << "max(" << max_level1(l) << ", " << max_level2(l) << ")"; return out;
    }
    return out;
}

level max(std::initializer_list<level> const & l) {
    lean_assert(l.size() >= 1);
    auto it = l.begin();
    level r = *it;
    ++it;
    for (; it != l.end(); ++it)
        r = max(r, *it);
    return r;
}
}
