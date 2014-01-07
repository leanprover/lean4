/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <vector>
#include "util/safe_arith.h"
#include "util/pair.h"
#include "util/buffer.h"
#include "kernel/universe_constraints.h"

namespace lean {
optional<int> universe_constraints::get_distance(name const & n1, name const & n2) const {
    auto it = m_distances.find(mk_pair(n1, n2));
    if (it != m_distances.end())
        return optional<int>(it->second);
    else
        return optional<int>();
}

void universe_constraints::add_var(name const & n) {
    lean_assert(!get_distance(n, n));
    m_distances[mk_pair(n, n)] = 0;
    m_outgoing_edges[n].emplace_back(n, 0);
    m_incoming_edges[n].emplace_back(n, 0);
}

bool universe_constraints::contains(name const & n) const {
    return static_cast<bool>(get_distance(n, n));
}

bool universe_constraints::is_implied(name const & n1, name const & n2, int k) const {
    auto d = get_distance(n1, n2);
    return d && *d >= k;
}

bool universe_constraints::is_consistent(name const & n1, name const & n2, int k) const {
    // we just check if n2 >= n1 - k + 1 is not implied
    return !is_implied(n2, n1, safe_add(safe_sub(0, k), 1));
}

/**
    \brief Add the pair (n, k) to entries if it does not contain an entry (n, k').
    Otherwise, replace entry (n, k') with (n, k).
*/
static void updt_entry(std::vector<std::pair<name, int>> & entries, name const & n, int k) {
    auto it = std::find_if(entries.begin(), entries.end(), [&](std::pair<name, int> const & p) { return p.first == n; });
    if (it == entries.end())
        entries.emplace_back(n, k);
    else
        it->second = k;
}

void universe_constraints::add_constraint(name const & n1, name const & n2, int k) {
    lean_assert(contains(n1));
    lean_assert(contains(n2));
    lean_assert(is_consistent(n1, n2, k));
    if (is_implied(n1, n2, k))
        return; // redundant
    buffer<std::tuple<name, name, int>> to_add;
    for (auto const & in : m_incoming_edges[n1])
        to_add.emplace_back(in.first, n2, safe_add(in.second, k));
    for (auto const & out : m_outgoing_edges[n2])
        to_add.emplace_back(n1, out.first, safe_add(out.second, k));
    for (auto const & e : to_add) {
        name const & from = std::get<0>(e);
        name const & to   = std::get<1>(e);
        int new_k         = std::get<2>(e);
        auto old_k        = get_distance(from, to);
        if (!old_k || new_k > *old_k) {
            updt_entry(m_outgoing_edges[from], to, new_k);
            updt_entry(m_incoming_edges[to], from, new_k);
            m_distances[mk_pair(from, to)] = new_k;
        }
    }
}
}
