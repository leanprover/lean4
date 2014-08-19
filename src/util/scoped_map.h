/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <unordered_map>
#include <vector>
#include <utility>
#include <functional>
#include "util/debug.h"
#include "util/pair.h"

#ifndef LEAN_SCOPED_MAP_INITIAL_BUCKET_SIZE
#define LEAN_SCOPED_MAP_INITIAL_BUCKET_SIZE 8
#endif

namespace lean {
/**
   \brief Scoped maps (aka backtrackable maps).
*/
template<typename Key, typename T, typename Hash = std::hash<Key>, typename KeyEqual = std::equal_to<Key>>
class scoped_map {
    typedef std::unordered_map<Key, T, Hash, KeyEqual> map;
    typedef typename map::size_type                    size_type;
    typedef typename map::value_type                   value_type;
    enum class action_kind { Insert, Replace, Erase };
    map                                        m_map;
    std::vector<pair<action_kind, value_type>> m_actions;
    std::vector<unsigned>                      m_scopes;
public:
    explicit scoped_map(size_type bucket_count = LEAN_SCOPED_MAP_INITIAL_BUCKET_SIZE,
                        const Hash& hash = Hash(),
                        const KeyEqual& equal = KeyEqual()):
        m_map(bucket_count, hash, equal) {
        // the return type of Hash()(k) should be convertible to size_t
        static_assert(std::is_convertible<typename std::result_of<decltype(std::declval<Hash>())(Key const &)>::type,
                                          std::size_t>::value,
                      "The return type of hash function is not convertible to std::size_t");
        // the return type of KeyEqual()(k1, k2) should be bool
        static_assert(std::is_same<typename std::result_of<decltype(std::declval<KeyEqual>())(Key const &, Key const &)>::type,
                                   bool>::value,
                      "The return type of KeyEqual()(k1, k2) is not bool");
    }

    void swap(scoped_map & other) {
        m_map.swap(other.m_map);
        m_actions.swap(other.m_actions);
        m_scopes.swap(other.m_scopes);
    }

    /** \brief Return the number of scopes. */
    unsigned num_scopes() const {
        return m_scopes.size();
    }

    /** \brief Return true iff there are no scopes. */
    bool at_base_lvl() const {
        return m_scopes.empty();
    }

    /** \brief Create a new scope (it allows us to restore the current state of the map). */
    void push() {
        m_scopes.push_back(m_actions.size());
    }

    /** \brief Remove \c num scopes, and restores the state of the map. */
    void pop(unsigned num = 1) {
        lean_assert(num <= num_scopes());
        unsigned old_sz = m_scopes[num_scopes() - num];
        lean_assert(old_sz <= m_actions.size());
        unsigned i = m_actions.size();
        while (i > old_sz) {
            --i;
            auto const & p = m_actions.back();
            switch (p.first) {
            case action_kind::Insert:
                m_map.erase(p.second.first);
                break;
            case action_kind::Replace: {
                auto it    = m_map.find(p.second.first);
                it->second = p.second.second;
                break;
            }
            case action_kind::Erase:
                m_map.insert(p.second);
                break;
            }
            m_actions.pop_back();
        }
        lean_assert(m_actions.size() == old_sz);
        m_scopes.resize(num_scopes() - num);
    }

    /** \brief Remove the top scope without 'undoing' the operations. */
    void keep() {
        lean_assert(num_scopes() > 0);
        m_scopes.pop_back();
        if (at_base_lvl())
            m_actions.clear();
    }

    /** \brief Return true iff the map is empty */
    bool empty() const {
        return m_map.empty();
    }

    /** \brief Return the number of elements stored in the map. */
    unsigned size() const {
        return m_map.size();
    }

    /** \brief Insert an element in the map */
    void insert(Key const & k, T const & v) {
        auto it = m_map.find(k);
        if (it == m_map.end()) {
            if (!at_base_lvl())
                m_actions.emplace_back(action_kind::Insert, value_type(k, v /* dummy */));
            m_map.insert(value_type(k, v));
        } else {
            if (!at_base_lvl())
                m_actions.emplace_back(action_kind::Replace, *it);
            it->second = v;
        }
    }

    void insert(value_type const & p) {
        insert(p.first, p.second);
    }

    /** \brief Remove an element from the map */
    void erase(Key const & k) {
        if (!at_base_lvl()) {
            auto it = m_map.find(k);
            if (m_map.find(k) != m_map.end())
                m_actions.emplace_back(action_kind::Erase, *it);
        }
        m_map.erase(k);
    }

    /** \brief Remove all elements and scopes */
    void clear() {
        m_map.clear();
        m_actions.clear();
        m_scopes.clear();
    }

    typedef typename map::const_iterator const_iterator;
    const_iterator find(Key const & k) const {
        return m_map.find(k);
    }

    const_iterator begin() const {
        return m_map.begin();
    }

    const_iterator end() const {
        return m_map.end();
    }

    bool contains(Key const & k) const {
        return find(k) != end();
    }

    /** \brief (For debugging) Display the content of this scoped map. */
    friend std::ostream & operator<<(std::ostream & out, scoped_map const & m) {
        out << "{";
        for (auto e : m) {
            out << e.first << " |-> " << e.second << "; ";
        };
        out << "}";
        return out;
    }

    /**
       \brief Auxiliary class for automatically performing a \c push
       in the constructor and a \c pop in the destructor.
    */
    class mk_scope {
        scoped_map & m_map;
    public:
        mk_scope(scoped_map & m):m_map(m) { m_map.push(); }
        ~mk_scope() { m_map.pop(); }
    };
};
}
