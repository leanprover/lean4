/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "kernel/for_each_fn.h"
#include "library/blast/branch.h"

namespace lean {
namespace blast {
struct hypothesis_depth_lt {
    branch const & m_branch;
    hypothesis_depth_lt(branch const & b): m_branch(b) {}
    bool operator()(unsigned hidx1, unsigned hidx2) const {
        hypothesis const * h1 = m_branch.get(hidx1);
        hypothesis const * h2 = m_branch.get(hidx2);
        return h1 && h2 && h1->get_depth() < h2->get_depth() && (h1->get_depth() == h2->get_depth() && hidx1 < hidx2);
    }
};

void branch::get_sorted_hypotheses(hypothesis_idx_buffer & r) const {
    m_context.for_each([&](unsigned hidx, hypothesis const &) {
            r.push_back(hidx);
        });
    std::sort(r.begin(), r.end(), hypothesis_depth_lt(*this));
}

void branch::add_forward_dep(unsigned hidx_user, unsigned hidx_provider) {
    if (auto s = m_forward_deps.find(hidx_provider)) {
        if (!s->contains(hidx_user)) {
            hypothesis_idx_set new_s(*s);
            new_s.insert(hidx_user);
            m_forward_deps.insert(hidx_provider, new_s);
        }
    } else {
        hypothesis_idx_set new_s;
        new_s.insert(hidx_user);
        m_forward_deps.insert(hidx_provider, new_s);
    }
}

void branch::add_deps(expr const & e, hypothesis & h_user, unsigned hidx_user) {
    if (!has_href(e) && !has_mref(e))
        return; // nothing to be done
    for_each(e, [&](expr const & l, unsigned) {
            if (!has_href(l) && !has_mref(l)) {
                return false;
            } else if (is_href(l)) {
                unsigned hidx_provider = href_index(l);
                hypothesis const * h_provider = get(hidx_provider);
                lean_assert(h_provider);
                if (h_user.m_depth <= h_provider->m_depth)
                    h_user.m_depth = h_provider->m_depth + 1;
                if (!h_user.m_deps.contains(hidx_provider)) {
                    h_user.m_deps.insert(hidx_provider);
                    add_forward_dep(hidx_user, hidx_provider);
                }
                return false;
            } else if (is_mref(l)) {
                m_mvar_idxs.insert(mref_index(l));
                return false;
            } else {
                return true;
            }
        });
}

void branch::add_deps(hypothesis & h_user, unsigned hidx_user) {
    add_deps(h_user.m_type, h_user, hidx_user);
    if (!is_local_non_href(h_user.m_value)) {
        add_deps(h_user.m_value, h_user, hidx_user);
    }
}

expr branch::add_hypothesis(name const & n, expr const & type, expr const & value) {
    hypothesis new_h;
    new_h.m_name          = n;
    new_h.m_type          = type;
    new_h.m_value         = value;
    unsigned new_hidx = m_next;
    m_next++;
    add_deps(new_h, new_hidx);
    m_context.insert(new_hidx, new_h);
    if (new_h.is_assumption())
        m_assumption.insert(new_hidx);
    m_todo.insert(new_hidx);
    return blast::mk_href(new_hidx);
}

static name * g_prefix = nullptr;

expr branch::add_hypothesis(expr const & type, expr const & value) {
    return add_hypothesis(name(*g_prefix, m_next), type, value);
}

bool branch::hidx_depends_on(unsigned hidx_user, unsigned hidx_provider) const {
    if (auto s = m_forward_deps.find(hidx_provider)) {
        return s->contains(hidx_user);
    } else {
        return false;
    }
}

void branch::set_target(expr const & t) {
    m_target = t;
    m_target_deps.clear();
    if (has_href(t) || has_mref(t)) {
        for_each(t, [&](expr const & e, unsigned) {
                if (!has_href(e) && !has_mref(e)) {
                    return false;
                } else if (is_href(e)) {
                    m_target_deps.insert(href_index(e));
                    return false;
                } else if (is_mref(e)) {
                    m_mvar_idxs.insert(mref_index(e));
                    return false;
                } else {
                    return true;
                }
            });
    }
}

void initialize_branch() {
    g_prefix     = new name(name::mk_internal_unique_name());
}

void finalize_branch() {
    delete g_prefix;
}
}}
