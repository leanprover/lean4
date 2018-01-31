/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
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
/** \brief Helper class for serializing objects. */
template<class T, class HashFn, class EqFn>
class object_serializer : public serializer::extension {
    std::unordered_map<T, unsigned, HashFn, EqFn> m_table;
public:
    object_serializer(HashFn const & h = HashFn(), EqFn const & e = EqFn()):m_table(LEAN_OBJECT_SERIALIZER_BUCKET_SIZE, h, e) {}

    template<typename F>
    void write_core(T const & v, char k, F && f) {
        auto it = m_table.find(v);
        serializer & s = get_owner();
        if (it == m_table.end()) {
            s.write_char(k + 1);
            f();
            m_table.insert(std::make_pair(v, static_cast<unsigned>(m_table.size())));
        } else {
            s.write_char(0);
            s.write_unsigned(it->second);
        }
    }

    template<typename F>
    void write(T const & v, F && f) {
        write_core(v, 0, f);
    }
};

/** \brief Helper class for deserializing objects. */
template<class T>
class object_deserializer : public deserializer::extension {
    std::vector<T> m_table;
public:
    template<typename F>
    T read_core(F && f) {
        deserializer & d = get_owner();
        char c = d.read_char();
        if (c != 0) {
            T r = f(c-1);
            m_table.push_back(r);
            return r;
        } else {
            unsigned i = d.read_unsigned();
            if (i >= m_table.size())
                throw corrupted_stream_exception();
            return m_table[i];
        }
    }

    template<typename F>
    T read(F && f) {
        return read_core([&](char ) { return f(); });
    }
};
}
