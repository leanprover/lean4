/*
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "runtime/buffer.h"
#include "runtime/object_ref.h"

namespace lean {
template<typename C> object * to_array(C const & elems) {
    object * a = alloc_array(elems.size(), elems.size());
    size_t i   = 0;
    for (typename C::value_type const & elem : elems) {
        inc(elem.raw());
        array_set(a, i, elem.raw());
        i++;
    }
    return a;
}

/* Wrapper for manipulating Lean Arrays in C++ */
template<typename T>
class array_ref : public object_ref {
public:
    explicit array_ref(obj_arg o):object_ref(o) {}
    array_ref(b_obj_arg o, bool b):object_ref(o, b) {}
    array_ref():object_ref(array_mk_empty()) {}
    array_ref(array_ref const & other):object_ref(other) {}
    array_ref(array_ref && other):object_ref(std::move(other)) {}
    array_ref(std::initializer_list<T> const & elems):object_ref(to_array(elems)) {}
    array_ref(buffer<T> const & elems):object_ref(to_array(elems)) {}

    array_ref & operator=(array_ref const & other) { object_ref::operator=(other); return *this; }
    array_ref & operator=(array_ref && other) { object_ref::operator=(std::move(other)); return *this; }

    size_t size() const { return array_size(raw()); }

    T const & operator[](size_t i) const {
        static_assert(sizeof(T const &) == sizeof(object *), "unexpected array_ref element size"); // NOLINT
        return reinterpret_cast<T const *>(array_cptr(raw()))[i];
    }

    class iterator {
        friend class array_ref;
        object ** m_it;
        iterator(object ** o):m_it(o) {}
    public:
        typedef std::forward_iterator_tag iterator_category;
        typedef T         value_type;
        typedef unsigned  difference_type;
        typedef T const * pointer;
        typedef T const & reference;
        iterator(iterator const & s):m_it(s.m_it) {}
        iterator & operator++() { m_it++; return *this; }
        iterator operator++(int) { iterator tmp(*this); operator++(); return tmp; }
        bool operator==(iterator const & s) const { return m_it == s.m_it; }
        bool operator!=(iterator const & s) const { return !operator==(s); }
        T const & operator*() { return reinterpret_cast<T const &>(*m_it); }
    };

    iterator begin() const { return iterator(array_cptr(raw())); }
    iterator end() const { return iterator(array_cptr(raw()) + size()); }
};
}
