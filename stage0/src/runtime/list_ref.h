/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "runtime/buffer.h"
#include "runtime/object_ref.h"

namespace lean {
template<typename T> T const & head(object * o) { return static_cast<T const &>(cnstr_get_ref(o, 0)); }

/* Wrapper for manipulating Lean lists in C++ */
template<typename T>
class list_ref : public object_ref {
public:
    list_ref():object_ref(box(0)) {}
    explicit list_ref(obj_arg o):object_ref(o) {}
    list_ref(b_obj_arg o, bool b):object_ref(o, b) {}
    explicit list_ref(T const & a):object_ref(mk_cnstr(1, a.raw(), box(0))) { inc(a.raw()); }
    explicit list_ref(T const * a) { if (a) *this = list_ref(*a); }
    explicit list_ref(list_ref<T> const * l) { if (l) *this = *l; }
    list_ref(T const & h, list_ref<T> const & t):object_ref(mk_cnstr(1, h.raw(), t.raw())) { inc(h.raw()); inc(t.raw()); }
    list_ref(list_ref const & other):object_ref(other) {}
    list_ref(list_ref && other):object_ref(std::move(other)) {}
    template<typename It> list_ref(It const & begin, It const & end):list_ref() {
        auto it = end;
        while (it != begin) {
            --it;
            *this = list_ref(*it, *this);
        }
    }
    list_ref(std::initializer_list<T> const & l):list_ref(l.begin(), l.end()) {}
    list_ref(buffer<T> const & b):list_ref(b.begin(), b.end()) {}

    list_ref & operator=(list_ref const & other) { object_ref::operator=(other); return *this; }
    list_ref & operator=(list_ref && other) { object_ref::operator=(std::move(other)); return *this; }

    explicit operator bool() const { return !is_scalar(raw()); }
    friend bool is_nil(list_ref const & l) { return is_scalar(l.raw()); }
    friend bool empty(list_ref const & l) { return is_nil(l); }
    friend T const & head(list_ref const & l) { lean_assert(!is_nil(l)); return static_cast<T const &>(cnstr_get_ref(l, 0)); }
    friend list_ref const & tail(list_ref const & l) { lean_assert(!is_nil(l)); return static_cast<list_ref const &>(cnstr_get_ref(l, 1)); }
    friend T const & car(list_ref const & l) { return head(l); }
    friend list_ref const & cdr(list_ref const & l) { return tail(l); }
    friend list_ref cons(T const & h, list_ref<T> const & t) { return list_ref(h, t); }

    friend bool is_eqp(list_ref const & l1, list_ref const & l2) { return l1.raw() == l2.raw(); }

    /** \brief Structural equality. */
    friend bool operator==(list_ref const & l1, list_ref const & l2) {
        object * it1 = l1.raw();
        object * it2 = l2.raw();
        while (!is_scalar(it1) && !is_scalar(it2)) {
            if (it1 == it2)
                return true;
            T const & h1 = ::lean::head<T>(it1);
            T const & h2 = ::lean::head<T>(it2);
            if (h1 != h2)
                return false;
            it1 = cnstr_get(it1, 1);
            it2 = cnstr_get(it2, 1);
        }
        return is_scalar(it1) && is_scalar(it2);
    }
    friend bool operator!=(list_ref const & l1, list_ref const & l2) { return !(l1 == l2); }

    // lexicographical order
    friend bool operator<(list_ref const & l1, list_ref const & l2) {
        object * it1 = l1.raw();
        object * it2 = l2.raw();
        while (!is_scalar(it1) && !is_scalar(it2)) {
            if (it1 == it2)
                return false;
            T const & h1 = ::lean::head<T>(it1);
            T const & h2 = ::lean::head<T>(it2);
            if (h1 < h2)
                return true;
            if (h2 < h1)
                return false;
            it1 = cnstr_get(it1, 1);
            it2 = cnstr_get(it2, 1);
        }
        return is_scalar(it1) && !is_scalar(it2);
    }

    class iterator {
        friend class list_ref;
        object * m_it;
        iterator(object * o):m_it(o) {}
    public:
        typedef std::forward_iterator_tag iterator_category;
        typedef T         value_type;
        typedef unsigned  difference_type;
        typedef T const * pointer;
        typedef T const & reference;
        iterator(iterator const & s):m_it(s.m_it) {}
        iterator & operator++() { m_it = cnstr_get(m_it, 1); return *this; }
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
            it = cnstr_get(it, 1);
        }
    }
};

typedef list_ref<object_ref> objects;

template<typename T> list_ref<T> const & tail(object * o) { return static_cast<list_ref<T> const &>(cnstr_get_ref(o, 1)); }

template<typename T> size_t length(list_ref<T> const & l) {
    size_t r    = 0;
    object * it = l.raw();
    while (!is_scalar(it)) {
        r++;
        it = cnstr_get(it, 1);
    }
    return r;
}

template<typename T> optional<T> head_opt(list_ref<T> const & l) { return is_nil(l) ? optional<T>() : some(head(l)); }

/** \brief Given `[a_0, ..., a_k]`, return `[f a_0, ..., f a_k]`. */
template<typename To, typename From, typename F>
list_ref<To> map2(list_ref<From> const & l, F && f) {
    if (is_nil(l)) {
        return list_ref<To>();
    } else {
        buffer<To> new_vs;
        for (From const & v : l)
            new_vs.push_back(f(v));
        return list_ref<To>(new_vs);
    }
}

/** \brief Given `[a_0, ..., a_k]`, return `[f a_0, ..., f a_k]`. */
template<typename T, typename F>
list_ref<T> map(list_ref<T> const & l, F && f) {
    return map2<T, T, F>(l, std::move(f));
}

template<typename T, typename F>
list_ref<T> map_reuse(list_ref<T> const & l, F && f) {
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
            list_ref<T> const & t = tail<T>(curr);
            list_ref<T> r(new_h, t);
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
bool compare(list_ref<T> const & l1, list_ref<T> const & l2, P && p) {
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
void to_buffer(list_ref<T> const & l, buffer<T> & r) {
    for (T const & h : l) r.push_back(h);
}

template<typename T>
list_ref<T> to_list_ref(buffer<T> const & r) {
    list_ref<T> l;
    for (int i = r.size() - 1; i >= 0; i--)
        l = list_ref<T>(r[i], l);
    return l;
}

/** \brief Filter/Remove elements from the list
    that do not satisfy the given predicate. */
template<typename T, typename P>
list_ref<T> filter(list_ref<T> const & l, P && p) {
    if (is_nil(l))
        return l;
    buffer<object*> tmp;
    l.get_cons_cells(tmp);
    size_t i = tmp.size();
    while (i > 0) {
        --i;
        if (!p(head<T>(tmp[i]))) {
            list_ref<T> r;
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

/** \brief Append two lists */
template<typename T> list_ref<T> append(list_ref<T> const & l1, list_ref<T> const & l2) {
    if (!l1) {
        return l2;
    } else if (!l2) {
        return l1;
    } else {
        buffer<object*> tmp;
        l1.get_cons_cells(tmp);
        list_ref<T> r = l2;
        unsigned i = tmp.size();
        while (i > 0) {
            --i;
            r = cons(head<T>(tmp[i]), r);
        }
        return r;
    }
}

template<typename T>
T const & get_ith(list_ref<T> const & l, unsigned idx) {
    return idx == 0 ? head(l) : get_ith(tail(l), idx - 1);
}
}
