/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Joachim Breitner
*/
#pragma once
#include <deque>
#include <vector>
#include "util/alloc.h"
#include "runtime/optional.h"

namespace lean {

/*
Conceptually, the scope cache is a stack of `Key → (Value × Scope)` hashmaps.
The `Scope` is a counter indicating the lowest position in the stack for which
the entry is valid.

Its purpose is to provide caching for an operation that:
 * maintains scopes (e.g. local contexts, substitutions). Higher stack
   positions correspond to inner, more local scopes.
 * For a given key, the result may depend on all or part of that scope.
 * At lookup time, it is not known whether the value for a key will depend on
   all or part of the scope, so only entries for the current innermost scope
   are considered.
 * At insert time, it is known which outermost scope the result depends on
   (the "result scope"), and the result is valid for all scopes between that
   and the innermost scope.

The operations are:
 * push(): push a new (empty) hashmap onto the stack.
 * pop(): pop the top hashmap from the stack.
 * scope(): current size of the stack (i.e. the index of the innermost scope).
 * lookup(key, result_scope): look up in the top hashmap, returning the value
   and propagating its result scope into `result_scope` via max.
 * insert(key, value, result_scope): insert a key-value pair into the hashmaps
   in the stack at depths in the range from `result_scope` to `scope()`. If it
   encounters an existing value along the way, uses and returns that value for
   improved sharing.

The implementation inverts the data structure to a hashmap of stacks for
efficiency. It uses a generation counter to assign a unique identifier to each
scope, and maintains a persistent linked list of these to represent the current
scope stack. Cache entries are not touched upon pop(); instead they are lazily
cleaned up when accessed (the `rewind` operation). Upon insert, instead of
duplicating the entry for all valid scopes, it stores one entry with the range
of scopes it is valid for.
*/
template<typename Key, typename Value, typename Hash = std::hash<Key>>
class scope_cache {
    struct scope_gen_node {
        unsigned gen;
        scope_gen_node * tail; /* parent scope, or nullptr for scope -1 */
    };

    struct cache_entry {
        Value result;
        unsigned scope_level;       /* scope at which this entry is (currently) valid */
        scope_gen_node * scope_gens; /* snapshot of scope_gens list at store time */
        unsigned result_scope;      /* maximum scope that contributed to the result */
    };

    typedef lean::unordered_map<Key, std::vector<cache_entry>, Hash> cache_map;

    cache_map m_cache;
    std::deque<scope_gen_node> m_gen_arena;
    scope_gen_node * m_scope_gens_list;
    unsigned m_gen_counter;
    unsigned m_scope;

public:
    scope_cache() : m_scope_gens_list(nullptr), m_gen_counter(0), m_scope(0) {
        m_gen_arena.push_back({0, nullptr});
        m_scope_gens_list = &m_gen_arena.back();
    }

    unsigned scope() const { return m_scope; }

    /* Enter a new scope. Bumps the generation counter so that stale
       entries at the new scope level are detected on lookup. */
    void push() {
        m_scope++;
        m_gen_counter++;
        m_gen_arena.push_back({m_gen_counter, m_scope_gens_list});
        m_scope_gens_list = &m_gen_arena.back();
    }

    /* Leave the current scope. Follows the tail of the persistent
       generation list back to the parent scope. */
    void pop() {
        m_scope--;
        m_scope_gens_list = m_scope_gens_list->tail;
    }

private:
    /* Lazily clean up the top of a per-key entry stack: degrade entries
       whose scopes were popped and evict entries that are stale due to
       popped result scopes or scope re-entry.  After rewind, either the
       stack is empty or its top entry satisfies scope_level <= m_scope
       with a matching scope generation. */
    void rewind(std::vector<cache_entry> & stack) {
        while (!stack.empty()) {
            auto & top = stack.back();
            /* Discard entries whose result depends on popped scopes. */
            if (top.result_scope > m_scope) {
                stack.pop_back();
                continue;
            }
            /* Degrade: follow tail pointers for scopes that were popped. */
            while (top.scope_level > m_scope) {
                top.scope_gens = top.scope_gens->tail;
                top.scope_level--;
            }
            /* Check generation at scope_level. When scope_level < m_scope,
               walk the current list down to scope_level first. */
            scope_gen_node * current_node = m_scope_gens_list;
            for (unsigned i = m_scope; i > top.scope_level; i--)
                current_node = current_node->tail;
            if (top.scope_gens->gen == current_node->gen) return;
            /* Generation mismatch: scope was re-entered. Walk both lists
               in lockstep to find a valid level or exhaust to result_scope. */
            scope_gen_node * entry_node = top.scope_gens;
            unsigned level = top.scope_level;
            while (level > top.result_scope) {
                entry_node = entry_node->tail;
                current_node = current_node->tail;
                level--;
                if (entry_node->gen == current_node->gen) {
                    top.scope_level = level;
                    top.scope_gens = entry_node;
                    return; /* now scope_level < m_scope */
                }
            }
            /* No valid level found → discard. */
            stack.pop_back();
        }
    }

public:
    /* Look up a cached result for the given key at the current scope.
       On hit, updates `result_scope = max(result_scope, entry.result_scope)`
       and returns the cached result. On miss, returns none. */
    optional<Value> lookup(Key const & key, unsigned & result_scope) {
        auto it = m_cache.find(key);
        if (it == m_cache.end()) return {};
        auto & stack = it->second;
        rewind(stack);
        if (stack.empty()) return {};
        auto & top = stack.back();
        if (top.scope_level != m_scope) return {};
        result_scope = std::max(result_scope, top.result_scope);
        return optional<Value>(top.result);
    }

    /* Insert a result for the given key at the current scope.
       `result_scope` is the maximum scope that contributed to the result;
       the entry is only valid when all scopes up to result_scope are unchanged.
       If a valid entry with the same `result_scope` already exists, its value
       is reused for sharing; the returned reference is the stored value. */
    Value const & insert(Key const & key, Value const & result, unsigned result_scope) {
        auto & stack = m_cache[key];
        rewind(stack);
        Value shared = result;
        if (!stack.empty() && stack.back().result_scope == result_scope) {
            shared = stack.back().result;
        }
        while (!stack.empty() && stack.back().scope_level >= result_scope) {
            stack.pop_back();
        }
        stack.push_back({std::move(shared), m_scope, m_scope_gens_list, result_scope});
        return stack.back().result;
    }
};

}
