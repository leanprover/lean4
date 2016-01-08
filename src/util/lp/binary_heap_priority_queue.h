/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include <vector>
namespace lean {
// the elements with the smallest priority are dequeued first
template <typename T>
class binary_heap_priority_queue {
    std::vector<T> m_priorities;

    // indexing for A starts from 1
    std::vector<unsigned> m_heap; // keeps the elements of the queue
    std::vector<int> m_heap_inverse; // o = m_heap[m_heap_inverse[o]]
    unsigned m_heap_size = 0;

    // is is the child place in heap
    void swap_with_parent(unsigned i) {
        unsigned parent = m_heap[i >> 1];
        put_at(i >> 1, m_heap[i]);
        put_at(i, parent);
    }


    void put_at(unsigned i, unsigned h) {
        m_heap[i] = h;
        m_heap_inverse[h] = i;
    }

    void decrease_priority(unsigned o, T newPriority) {
        m_priorities[o] = newPriority;
        int i = m_heap_inverse[o];
        while (i > 1) {
            if (m_priorities[m_heap[i]] < m_priorities[m_heap[i >> 1]])
                swap_with_parent(i);
            else
                break;
            i >>= 1;
        }
    }

public:
    bool is_consistent() const {
        for (int i = 0; i < m_heap_inverse.size(); i++) {
            int i_index = m_heap_inverse[i];
            lean_assert(i_index <= static_cast<int>(m_heap_size));
            lean_assert(i_index == -1 || m_heap[i_index] == i);
        }
        for (unsigned i = 1; i < m_heap_size; i++) {
            unsigned ch = i << 1;
            for (int k = 0; k < 2; k++) {
                if (ch > m_heap_size) break;
                if (!(m_priorities[m_heap[i]] <= m_priorities[m_heap[ch]])){
                    std::cout << "m_heap_size = " << m_heap_size << std::endl;
                    std::cout << "i = " << i << std::endl;
                    std::cout << "m_heap[i] = " << m_heap[i] << std::endl;
                    std::cout << "ch = " << ch << std::endl;
                    std::cout << "m_heap[ch] = " << m_heap[ch] << std::endl;
                    std::cout << "m_priorities[m_heap[i]] = " << m_priorities[m_heap[i]] << std::endl;
                    std::cout << "m_priorities[m_heap[ch]] = " << m_priorities[m_heap[ch]]<< std::endl;
                    return false;
                }
                ch++;
            }
        }
        return true;
    }

public:
    void remove(unsigned o) {
        T priority_of_o = m_priorities[o];
        int o_in_heap = m_heap_inverse[o];
        if (o_in_heap == -1)  {
            return;  // nothing to do
        }
        lean_assert(o_in_heap <= m_heap_size);
        if (o_in_heap < m_heap_size) {
            put_at(o_in_heap, m_heap[m_heap_size--]);
            if (m_priorities[m_heap[o_in_heap]] > priority_of_o) {
                fix_heap_under(o_in_heap);
            } else { // we need to propogate the m_heap[o_in_heap] up
                unsigned i = o_in_heap;
                while (i > 1) {
                    unsigned ip = i >> 1;
                    if (m_priorities[m_heap[i]] < m_priorities[m_heap[ip]])
                        swap_with_parent(i);
                    else
                        break;
                    i = ip;
                }
            }
        } else {
            lean_assert(o_in_heap == m_heap_size);
            m_heap_size--;
        }
        m_heap_inverse[o] = -1;
        //        lean_assert(is_consistent());
    }
    unsigned size() const { return m_heap_size; }
    binary_heap_priority_queue(): m_heap(1) {} // the empty constructror
    // n is the initial queue capacity.
    // The capacity will be enlarged two times automatically if needed
    binary_heap_priority_queue(unsigned n) :
        m_priorities(n),
        m_heap(n + 1), // because the indexing for A starts from 1
        m_heap_inverse(n, -1)
        { }

    void clear() {
        m_heap_size = 0;
    }

    void resize(unsigned n) {
        m_priorities.resize(n);
        m_heap.resize(n + 1);
        m_heap_inverse.resize(n, -1);
    }

    void put_to_heap(unsigned i, unsigned o) {
        m_heap[i] = o;
        m_heap_inverse[o] = i;
    }

    void enqueue_new(unsigned o, const T& priority) {
        m_heap_size++;
        int i = m_heap_size;
        lean_assert(o < m_priorities.size());
        m_priorities[o] = priority;
        put_at(i, o);
        while (i > 1 && m_priorities[m_heap[i >> 1]] > priority) {
            swap_with_parent(i);
            i >>= 1;
        }
    }
    // This method can work with an element that is already in the queue.
    // In this case the priority will be changed and the queue adjusted.
    void enqueue(unsigned o, const T & priority) {
        if (o >= m_priorities.size()) {
            resize(o << 1); // make the size twice larger
        }
        if (m_heap_inverse[o] == -1)
            enqueue_new(o, priority);
        else
            change_priority_for_existing(o, priority);
    }

    void change_priority_for_existing(unsigned o, const T & priority) {
        if (m_priorities[o] > priority) {
            decrease_priority(o, priority);
        } else {
            m_priorities[o] = priority;
            fix_heap_under(m_heap_inverse[o]);
        }
    }

    T get_priority(unsigned o) const {
        lean_assert(m_priorities.size() > o);
        return m_priorities[o];
    }
    bool is_empty() const {
        return m_heap_size == 0;
    }

    /// return the first element of the queue and removes it from the queue
    unsigned dequeue_and_get_priority(T & priority) {
        lean_assert(m_heap_size != 0);
        int ret = m_heap[1];
        priority = m_priorities[ret];
        put_the_last_at_the_top_and_fix_the_heap();
        return ret;
    }

    void fix_heap_under(unsigned i) {
        while (true) {
            int smallest = i;
            int l = i << 1;
            if (l <= m_heap_size && m_priorities[m_heap[l]] < m_priorities[m_heap[i]])
                smallest = l;
            int r = l + 1;
            if (r <= m_heap_size && m_priorities[m_heap[r]] < m_priorities[m_heap[smallest]])
                smallest = r;
            if (smallest != i)
                swap_with_parent(smallest);
            else
                break;
            i = smallest;
        }
    }

    void put_the_last_at_the_top_and_fix_the_heap() {
        if (m_heap_size > 1) {
            put_at(1, m_heap[m_heap_size--]);
            fix_heap_under(1);
        } else {
            m_heap_size--;
        }
    }
    /// return the first element of the queue and removes it from the queue
    unsigned dequeue() {
        lean_assert(m_heap_size);
        int ret = m_heap[1];
        put_the_last_at_the_top_and_fix_the_heap();
        m_heap_inverse[ret] = -1;
        return ret;
    }

    void print() {
        std::vector<int> index;
        std::vector<T> prs;
        while (size()) {
            T prior;
            int j = dequeue_and_get_priority(prior);
            index.push_back(j);
            prs.push_back(prior);
            std::cout << "(" << j << ", " << prior << ")";
        }
        std::cout << std::endl;
        // restore the queue
        for (int i = 0; i < index.size(); i++)
            enqueue(index[i], prs[i]);
    }
};
}
