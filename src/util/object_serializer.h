/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <unordered_map>
#include <vector>
#include "util/serializer.h"

#ifndef LEAN_OBJECT_SERIALIZER_BUCKET_SIZE
#define LEAN_OBJECT_SERIALIZER_BUCKET_SIZE 8
#endif

namespace lean {
/**
   \brief Helper class for serializing objects.
*/
template<class T, class HashFn, class EqFn>
class object_serializer : public serializer::extension {
    std::unordered_map<T, unsigned, HashFn, EqFn> m_table;
public:
    object_serializer(HashFn const & h = HashFn(), EqFn const & e = EqFn()):m_table(LEAN_OBJECT_SERIALIZER_BUCKET_SIZE, h, e) {}
    template<typename F>
    void write(T const & v, F && f) {
        auto it = m_table.find(v);
        serializer & s = get_owner();
        if (it == m_table.end()) {
            s.write_bool(true);
            f();
            m_table.insert(std::make_pair(v, m_table.size()));
        } else {
            s.write_bool(false);
            s.write_unsigned(it->second);
        }
    }
};

/**
   \brief Helper class for deserializing objects.
*/
template<class T>
class object_deserializer : public deserializer::extension {
    std::vector<T> m_table;
public:
    template<typename F>
    T read(F && f) {
        deserializer & d = get_owner();
        if (d.read_bool()) {
            T r = f();
            m_table.push_back(r);
            return r;
        } else {
            unsigned i = d.read_unsigned();
            lean_assert(i < m_table.size());
            return m_table[i];
        }
    }
};
}
