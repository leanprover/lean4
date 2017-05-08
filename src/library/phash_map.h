/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/bit_tricks.h"
#include "util/name.h"
#include "library/phashtable.h"

namespace lean {
template<typename Key, typename Value>
struct key_value_pair {
    Key   m_key;
    Value m_value;
    key_value_pair(Key const & k):m_key(k) {}
    key_value_pair(Key const & k, Value const & v):
        m_key(k), m_value(v) {}
};

template<typename Key, typename Value>
class default_map_entry : public default_hash_entry<key_value_pair<Key, Value>> {
    typedef default_hash_entry<key_value_pair<Key, Value>> parent;

    explicit default_map_entry(bool b):parent(b) {}
public:
    typedef Key                        key;
    typedef Value                      value;
    typedef key_value_pair<Key, Value> key_value;
    default_map_entry() {}
    default_map_entry(key_value const & d, unsigned h):parent(d, h) {}
    static default_map_entry mk_deleted() { return default_map_entry(false); }
    default_map_entry & operator=(default_map_entry const & src) {
        parent::operator=(src);
        return *this;
    }
};

template<typename Entry, typename HashProc, typename EqProc, bool ThreadSafe>
class phashtable2map {
protected:
    typedef Entry    entry;
    typedef typename Entry::key      key;
    typedef typename Entry::value    value;
    typedef typename Entry::key_value key_value;

    struct entry_hash_proc : private HashProc {
        entry_hash_proc(HashProc const & p):HashProc(p) {}

        unsigned operator()(key_value const & d) const {
            return HashProc::operator()(d.m_key);
        }
    };

    struct entry_eq_proc : private EqProc {
        entry_eq_proc(EqProc const & p):EqProc(p) {}

        bool operator()(key_value const & d1, key_value const & d2) const {
            return EqProc::operator()(d1.m_key, d2.m_key);
        }
    };

    typedef phashtable_core<entry, entry_hash_proc, entry_eq_proc, ThreadSafe> table;

    table m_table;

public:
    phashtable2map(HashProc const & h = HashProc(), EqProc const & e = EqProc()):
        m_table(LEAN_DEFAULT_PHASHTABLE_INITIAL_CAPACITY, entry_hash_proc(h), entry_eq_proc(e)) {
    }

    void clear() {
        m_table.clear();
    }

    unsigned size() const {
        return m_table.size();
    }

    unsigned capacity() const {
        return m_table.capacity();
    }

    void insert(key const & k, value const & v) {
        m_table.insert(key_value(k, v));
    }

    optional<value> find(key const & k) const {
        if (auto e = m_table.find(key_value(k)))
            return optional<value>(e->m_value);
        else
            return optional<value>();
    }

    bool contains(key const & k) const {
        return m_table.contains(key_value(k));
    }

    void erase(key const & k) {
        m_table.erase(key_value(k));
    }

    template<typename F>
    void for_each(F && f) const {
        m_table.for_each([&](key_value const & e) {
                f(e.m_key, e.m_value);
            });
    }
};


template<typename Key, typename Value, typename HashProc, typename EqProc, bool ThreadSafe>
class phash_map : public phashtable2map<default_map_entry<Key, Value>, HashProc, EqProc, ThreadSafe> {
public:
    phash_map(HashProc const & h = HashProc(), EqProc const & e = EqProc()):
        phashtable2map<default_map_entry<Key, Value>, HashProc, EqProc, ThreadSafe>(h, e) {
    }
};

template<typename T>
using name_hash_map = phash_map<name, T, name_hash, name_eq, true>;
}
