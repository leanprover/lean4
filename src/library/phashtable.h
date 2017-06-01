/*
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <algorithm>
#include "util/bit_tricks.h"
#include "library/parray.h"

#ifndef LEAN_DEFAULT_PHASHTABLE_INITIAL_CAPACITY
#define LEAN_DEFAULT_PHASHTABLE_INITIAL_CAPACITY 8
#endif

#ifndef LEAN_DEFAULT_PHASHTABLE_SMALL_CAPACITY
#define LEAN_DEFAULT_PHASHTABLE_SMALL_CAPACITY 64
#endif

namespace lean {

template<typename T>
class default_hash_entry {
protected:
    enum state { Free, Deleted, Used };

    unsigned  m_hash; //!< cached hash code
    state     m_state;
    union {
        T     m_data;
    };
    explicit default_hash_entry(bool):m_hash(0), m_state(Deleted) {} // NOLINT
public:
    typedef T                data;
    default_hash_entry():m_hash(0), m_state(Free) {}
    default_hash_entry(default_hash_entry const & src):
        m_hash(src.m_hash), m_state(src.m_state) {
        if (m_state == Used)
            new (&m_data) T(src.get_data());
    }
    default_hash_entry(T const & v, unsigned h):m_hash(h), m_state(Used) {
        new (&m_data) T(v);
    }
    ~default_hash_entry() { if (m_state == Used) m_data.~T(); }

    static default_hash_entry mk_deleted() { return default_hash_entry(false); }

    bool is_free() const { return m_state == Free; }
    bool is_deleted() const { return m_state == Deleted; }
    bool is_used() const { return m_state == Used; }

    unsigned get_hash() const  { return m_hash; }
    void set_hash(unsigned h)  { m_hash = h; }

    T const & get_data() const { lean_assert(is_used()); return m_data; }

    void set_data(T const & d) {
        if (is_used())
            m_data.~T();
        new (&m_data) T(d);
        m_state = Used;
    }

    default_hash_entry & operator=(default_hash_entry const & src) {
        if (is_used())
            m_data.~T();
        m_hash  = src.m_hash;
        m_state = src.m_state;
        if (m_state == Used)
            new (&m_data) T(src.get_data());
        return *this;
    }
};

template<typename Entry, typename HashProc, typename EqProc, bool ThreadSafe = false>
class phashtable_core : private HashProc, private EqProc {
protected:
    typedef parray<Entry, ThreadSafe> table;
    typedef typename Entry::data      data;
    typedef Entry                     entry;

    table    m_table;
    unsigned m_size;
    unsigned m_num_deleted;

    static void copy_table(table const & source, table & target) {
        lean_assert(target.get_rc() == 1);
        typename table::exclusive_access B(target);
        unsigned target_sz   = B.size();
        unsigned target_mask = target_sz - 1;
        source.for_each([&](entry const & e) {
                if (!e.is_used())
                    return;
                unsigned hash  = e.get_hash();
                unsigned begin = hash & target_mask;
                unsigned idx   = begin;
                for (; idx < target_sz; idx++) {
                    if (B[idx].is_free()) {
                        B.set(idx, e);
                        return;
                    }
                }
                idx = 0;
                for (; idx < begin; idx++) {
                    if (B[idx].is_free()) {
                        B.set(idx, e);
                        return;
                    }
                }
            });
    }

    void expand_table() {
        table new_table(m_table.size() << 1, entry());
        copy_table(m_table, new_table);
        swap(m_table, new_table);
        m_num_deleted = 0;
    }

    void expand_table_if_needed() {
        if ((m_size + m_num_deleted) << 2 > (m_table.size() * 3))
            expand_table();
    }

    void remove_deleted_entries() {
        table new_table(m_table.size(), entry());
        copy_table(m_table, new_table);
        swap(m_table, new_table);
        m_num_deleted = 0;
    }

    unsigned get_hash(data const & e) const { return HashProc::operator()(e); }
    bool equals(data const & e1, data const & e2) const { return EqProc::operator()(e1, e2); }

public:
    phashtable_core(unsigned initial_capacity = LEAN_DEFAULT_PHASHTABLE_INITIAL_CAPACITY,
                    HashProc const & h = HashProc(),
                    EqProc const & e = EqProc()):
        HashProc(h),
        EqProc(e),
        m_table(initial_capacity, entry()),
        m_size(0),
        m_num_deleted(0) {
        lean_assert(is_power_of_two(initial_capacity));
    }

    phashtable_core(phashtable_core const & source):
        HashProc(source), EqProc(source),
        m_table(source.m_table), m_size(source.m_size), m_num_deleted(source.m_num_deleted) {
    }

    unsigned size() const { return m_size; }

    unsigned capacity() const { return m_table.size(); }

    friend void swap(phashtable_core & t1, phashtable_core & t2) {
        swap(t1.m_table, t2.m_table);
        std::swap(t1.m_size, t2.m_size);
        std::swap(t1.m_num_deleted, t2.m_num_deleted);
    }

    #define INSERT_LOOP_BODY()                                          \
        {                                                               \
            entry const & curr = A[idx];                                \
            if (curr.is_used()) {                                       \
                if (curr.get_hash() == hash && equals(curr.get_data(), e)) { \
                    A.set(idx, entry(e, hash));                         \
                    return;                                             \
                }                                                       \
            } else if (curr.is_free()) {                                \
                unsigned new_idx;                                       \
                if (found_deleted) {                                    \
                    new_idx = del_idx; m_num_deleted--;                 \
                } else {                                                \
                    new_idx = idx;                                      \
                }                                                       \
                A.set(new_idx, entry(e, hash));                         \
                m_size++;                                               \
                return;                                                 \
            } else {                                                    \
                lean_assert(curr.is_deleted());                         \
                del_idx = idx;                                          \
            }                                                           \
        } ((void) 0)

    void insert(data const & e) {
        expand_table_if_needed();
        typename table::exclusive_access A(m_table);
        unsigned hash      = get_hash(e);
        unsigned cap       = A.size();
        unsigned mask      = cap - 1;
        unsigned begin     = hash & mask;
        unsigned idx       = begin;
        bool found_deleted = false;
        unsigned del_idx   = 0;
        for (; idx < cap; idx++) {
            INSERT_LOOP_BODY();
        }
        for (idx = 0; idx < begin; idx++) {
            INSERT_LOOP_BODY();
        }
        lean_unreachable();
    }

    #undef INSERT_LOOP_BODY

    template<typename F>
    void for_each(F && fn) const {
        m_table.for_each([&](entry const & e) {
                if (e.is_used()) {
                    fn(e.get_data());
                }
            });
    }

    #define CONTAINS_LOOP_BODY()                                            \
        {                                                               \
            entry const & curr = A[idx];                                \
            if (curr.is_used()) {                                       \
                if (curr.get_hash() == hash && equals(curr.get_data(), e)) { \
                    return true;                                        \
                }                                                       \
            } else if (curr.is_free()) {                                \
                return false;                                           \
            }                                                           \
        } ((void) 0)

    bool contains(data const & e) const {
        typename table::exclusive_access A(const_cast<table &>(m_table));
        unsigned hash  = get_hash(e);
        unsigned cap   = A.size();
        unsigned mask  = cap - 1;
        unsigned begin = hash & mask;
        unsigned idx   = begin;
        for (; idx < cap; idx++) {
            CONTAINS_LOOP_BODY();
        }
        for (idx = 0; idx < begin; idx++) {
            CONTAINS_LOOP_BODY();
        }
        return false;
    }

    #undef CONTAINS_LOOP_BODY

    #define FIND_LOOP_BODY()                                            \
        {                                                               \
            entry const & curr = A[idx];                                \
            if (curr.is_used()) {                                       \
                if (curr.get_hash() == hash && equals(curr.get_data(), e)) { \
                    return optional<data>(curr.get_data());             \
                }                                                       \
            } else if (curr.is_free()) {                                \
                return optional<data>();                                \
            }                                                           \
        } ((void) 0)

    optional<data> find(data const & e) const {
        typename table::exclusive_access A(const_cast<table &>(m_table));
        unsigned hash  = get_hash(e);
        unsigned cap   = A.size();
        unsigned mask  = cap - 1;
        unsigned begin = hash & mask;
        unsigned idx   = begin;
        for (; idx < cap; idx++) {
            FIND_LOOP_BODY();
        }
        for (idx = 0; idx < begin; idx++) {
            FIND_LOOP_BODY();
        }
        return optional<data>();
    }

    #undef FIND_LOOP_BODY

private:
    #define ERASE_LOOP_BODY()                                           \
        {                                                               \
            entry const & curr = A[idx];                                \
            if (curr.is_used()) {                                       \
                if (curr.get_hash() == hash && equals(curr.get_data(), e)) { \
                    goto found_elem;                                    \
                }                                                       \
            } else if (curr.is_free()) {                                \
                return false;                                           \
            }                                                           \
        } ((void) 0)

    bool erase_aux(data const & e) {
        typename table::exclusive_access A(m_table);
        unsigned hash  = get_hash(e);
        unsigned cap   = A.size();
        unsigned mask  = cap - 1;
        unsigned begin = hash & mask;
        unsigned idx   = begin;
        for (; idx < cap; idx++) {
            ERASE_LOOP_BODY();
        }
        for (idx = 0; idx < begin; idx++) {
            ERASE_LOOP_BODY();
        }
        return false; /* e is not in the table */
      found_elem:
        unsigned next_idx = idx + 1;
        if (next_idx == cap)
            next_idx = 0;
        if (A[next_idx].is_free()) {
            A.set(idx, entry());
            lean_assert(A[idx].is_free());
            m_size--;
        } else {
            A.set(idx, entry::mk_deleted());
            lean_assert(A[idx].is_deleted());
            m_num_deleted++;
            m_size--;
            if (m_num_deleted > m_size && m_num_deleted > LEAN_DEFAULT_PHASHTABLE_SMALL_CAPACITY) {
                return true;
            }
        }
        return false;
    }

    #undef ERASE_LOOP_BODY

public:
    void erase(data const & e) {
        if (erase_aux(e)) {
            remove_deleted_entries();
        }
    }

    void clear() {
        if (m_size == 0 && m_num_deleted == 0)
            return;
        unsigned overhead = 0;
        unsigned cap      = 0;
        {
            typename table::exclusive_access A(m_table);
            cap   = A.size();
            for (unsigned idx = 0; idx < cap; idx++) {
                if (!A[idx].is_free)
                    A.set(idx, entry());
                else
                    overhead++;
            }
        }
        if (cap > LEAN_DEFAULT_PHASHTABLE_SMALL_CAPACITY && overhead << 2 > (cap * 3)) {
            cap     = cap >> 1;
            lean_assert(is_power_of_two(cap));
            m_table = table(cap, entry());
        }
        m_size        = 0;
        m_num_deleted = 0;
    }


    bool check_invariant() const {
        typename table::exclusive_access A(const_cast<table &>(m_table));
        unsigned cap = A.size();
        unsigned num_deleted = 0;
        unsigned num_used = 0;
        for (unsigned idx = 0; idx < cap; idx++) {
            entry const & curr = A[idx];
            if (curr.is_deleted()) {
                num_deleted++;
            }
            if (curr.is_used()) {
                num_used++;
            }
        }
        lean_assert(num_deleted == m_num_deleted);
        lean_assert(num_used == m_size);
        return true;
    }
};

template<typename T, typename HashProc, typename EqProc, bool ThreadSafe = false>
class phashtable : public phashtable_core<default_hash_entry<T>, HashProc, EqProc, ThreadSafe> {
public:
    phashtable(unsigned initial_capacity = LEAN_DEFAULT_PHASHTABLE_INITIAL_CAPACITY,
               HashProc const & h = HashProc(),
               EqProc const & e = EqProc()):
        phashtable_core<default_hash_entry<T>, HashProc, EqProc, ThreadSafe>(initial_capacity, h, e) {}

    phashtable(phashtable const & src):
        phashtable_core<default_hash_entry<T>, HashProc, EqProc, ThreadSafe>(src) {}

    phashtable & operator=(phashtable const & s) {
        this->m_table       = s.m_table;
        this->m_size        = s.m_size;
        this->m_num_deleted = s.m_num_deleted;
        return *this;
    }
};
}
