/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/object_ref.h"

namespace lean {
template<typename T> T const & head(object * o) { return static_cast<T const &>(cnstr_obj_ref(o, 0)); }

/* Wrapper for manipulating Lean lists in C++ */
template<typename T>
class obj_list : public object_ref {
    explicit obj_list(object * o):object_ref(o) { inc(o); }
public:
    obj_list():object_ref(box(0)) {}
    obj_list(T const & a):object_ref(mk_cnstr(1, a.raw(), box(0))) { inc(a.raw()); }
    obj_list(T const & h, obj_list<T> const & t):object_ref(mk_cnstr(1, h.raw(), t.raw())) { inc(h.raw()); inc(t.raw()); }
    obj_list(obj_list const & other):object_ref(other) {}
    obj_list(obj_list && other):object_ref(other) {}
    template<typename It> obj_list(It const & begin, It const & end):obj_list() {
        auto it = end;
        while (it != begin) {
            --it;
            *this = obj_list(*it, *this);
        }
    }
    obj_list(std::initializer_list<T> const & l):obj_list(l.begin(), l.end()) {}
    obj_list(buffer<T> const & b):obj_list(b.begin(), b.end()) {}

    obj_list & operator=(obj_list const & other) { object_ref::operator=(other); return *this; }
    obj_list & operator=(obj_list && other) { object_ref::operator=(other); return *this; }

    explicit operator bool() const { return !is_scalar(raw()); }
    friend bool is_nil(obj_list const & l) { return is_scalar(l.raw()); }
    friend bool empty(obj_list const & l) { return is_nil(l); }
    friend T const & head(obj_list const & l) { lean_assert(!is_nil(l)); return static_cast<T const &>(cnstr_obj_ref(l, 0)); }
    friend obj_list const & tail(obj_list const & l) { lean_assert(!is_nil(l)); return static_cast<obj_list const &>(cnstr_obj_ref(l, 1)); }
    friend T const & car(obj_list const & l) { return head(l); }
    friend obj_list const & cdr(obj_list const & l) { return tail(l); }
    friend obj_list cons(T const & h, obj_list<T> const & t) { return obj_list(h, t); }

    friend bool is_eqp(obj_list const & l1, obj_list const & l2) { return l1.raw() == l2.raw(); }
    void serialize(serializer & s) const { s.write_object(raw()); }
    static obj_list deserialize(deserializer & d) { return obj_list(d.read_object()); }

    /** \brief Structural equality. */
    friend bool operator==(obj_list const & l1, obj_list const & l2) {
        object * it1 = l1.raw();
        object * it2 = l2.raw();
        while (!is_scalar(it1) && !is_scalar(it2)) {
            if (it1 == it2)
                return true;
            T const & h1 = ::lean::head<T>(it1);
            T const & h2 = ::lean::head<T>(it2);
            if (h1 != h2)
                return false;
            it1 = cnstr_obj(it1, 1);
            it2 = cnstr_obj(it2, 1);
        }
        return is_scalar(it1) && is_scalar(it2);
    }
    friend bool operator!=(obj_list const & l1, obj_list const & l2) { return !(l1 == l2); }

    class iterator {
        friend class obj_list;
        object * m_it;
        iterator(object * o):m_it(o) {}
    public:
        typedef std::forward_iterator_tag iterator_category;
        typedef T         value_type;
        typedef unsigned  difference_type;
        typedef T const * pointer;
        typedef T const & reference;
        iterator(iterator const & s):m_it(s.m_it) {}
        iterator & operator++() { m_it = cnstr_obj(m_it, 1); return *this; }
        iterator operator++(int) { iterator tmp(*this); operator++(); return tmp; }
        bool operator==(iterator const & s) const { return m_it == s.m_it; }
        bool operator!=(iterator const & s) const { return !operator==(s); }
        T const & operator*() { return ::lean::head<T>(m_it); }
    };

    iterator begin() const { return iterator(raw()); }
    iterator end() const { return iterator(box(0)); }

    void get_cons_cells(buffer<object*> & r) const {
        object * it = raw();
        while (!is_scalar(it)) {
            r.push_back(it);
            it = cnstr_obj(it, 1);
        }
    }
};

template<typename T> obj_list<T> const & tail(object * o) { return static_cast<obj_list<T> const &>(cnstr_obj_ref(o, 1)); }

template<typename T> size_t length(obj_list<T> const & l) {
    size_t r    = 0;
    object * it = l.raw();
    while (!is_scalar(it)) {
        r++;
        it = cnstr_obj(it, 1);
    }
    return r;
}

template<typename T> serializer & operator<<(serializer & s, obj_list<T> const & l) { l.serialize(s); return s; }
template<typename T> obj_list<T> read_obj_list(deserializer & d) { return obj_list<T>::deserialize(d); }

/** \brief Given `[a_0, ..., a_k]`, return `[f a_0, ..., f a_k]`. */
template<typename To, typename From, typename F>
obj_list<To> map2(obj_list<From> const & l, F && f) {
    if (is_nil(l)) {
        return obj_list<To>();
    } else {
        buffer<To> new_vs;
        for (To const & v : l)
            new_vs.push_back(f(v));
        return obj_list<To>(new_vs);
    }
}

/** \brief Given `[a_0, ..., a_k]`, return `[f a_0, ..., f a_k]`. */
template<typename T, typename F>
obj_list<T> map(obj_list<T> const & l, F && f) {
    return map2<T, T, F>(l, std::move(f));
}

template<typename T, typename F>
obj_list<T> map_reuse(obj_list<T> const & l, F && f) {
    if (is_nil(l))
        return l;
    buffer<object*> tmp;
    l.get_cons_cells(tmp);
    auto it    = tmp.end();
    auto begin = tmp.begin();
    while (it != begin) {
        --it;
        object * curr  = *it;
        T const & h = head<T>(curr);
        T new_h = f(h);
        if (new_h.raw() != h.raw()) {
            obj_list<T> const & t = tail<T>(curr);
            obj_list<T> r(new_h, t);
            while (it != begin) {
                --it;
                object * curr  = *it;
                T const & h = head<T>(curr);
                r = cons(f(h), r);
            }
            return r;
        }
    }
    return l;
}

/** \brief Compare two lists using the binary predicate p. */
template<typename T, typename P>
bool compare(obj_list<T> const & l1, obj_list<T> const & l2, P && p) {
    auto it1 = l1.begin();
    auto it2 = l2.begin();
    auto end1 = l1.end();
    auto end2 = l2.end();
    for (; it1 != end1 && it2 != end2; ++it1, ++it2) {
        if (!p(*it1, *it2))
            return false;
    }
    return it1 == end1 && it2 == end2;
}

template<typename T>
void to_buffer(obj_list<T> const & l, buffer<T> & r) {
    for (T const & h : l) r.push_back(h);
}

/** \brief Filter/Remove elements from the list
    that do not satisfy the given predicate. */
template<typename T, typename P>
obj_list<T> filter(obj_list<T> const & l, P && p) {
    if (is_nil(l))
        return l;
    buffer<object*> tmp;
    l.get_cons_cells(tmp);
    size_t i = tmp.size();
    while (i > 0) {
        --i;
        if (!p(head<T>(tmp[i]))) {
            obj_list<T> r;
            r = tail<T>(tmp[i]);
            while (i > 0) {
                --i;
                T const & h = head<T>(tmp[i]);
                if (p(h))
                    r = cons(h, r);
            }
            return r;
        }
    }
    return l; // no element was removed
}
}
