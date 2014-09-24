/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include "util/thread.h"
#include "util/int64.h"
#include "util/debug.h"
#include "util/exception.h"
#include "util/numerics/primes.h"

#ifndef LEAN_PRIME_LIST_MAX_SIZE
#define LEAN_PRIME_LIST_MAX_SIZE 1<<20
#endif

namespace lean {
class prime_generator {
    std::vector<uint64> m_primes;
    void process_next_k_numbers(uint64 k) {
        std::vector<uint64> todo;
        uint64 begin = m_primes.back() + 2;
        uint64 end   = begin + k;
        for (uint64 i = begin; i < end; i += 2) {
            todo.push_back(i);
        }
        unsigned j = 1;
        lean_assert(m_primes[j] == 3);
        while (!todo.empty()) {
            unsigned sz = m_primes.size();
            for (; j < sz; j++) {
                uint64 p = m_primes[j];
                unsigned todo_sz = todo.size();
                unsigned k1 = 0;
                unsigned k2 = 0;
                for (; k1 < todo_sz; k1++) {
                    if (todo[k1] % p == 0)
                        continue;
                    todo[k2] = todo[k1];
                    k2++;
                }
                todo.resize(k2);
                if (k2 == 0)
                    return;
                if (p > (todo[k2-1] / p) + 1) {
                    // all numbers in todo are primes
                    for (unsigned k1 = 0; k1 < k2; k1++) {
                        m_primes.push_back(todo[k1]);
                    }
                    return;
                }
            }
            uint64 p = m_primes.back();
            p = p*p;
            unsigned todo_sz = todo.size();
            unsigned k1 = 0;
            for (k1 = 0; k1 < todo_sz; k1++) {
                if (todo[k1] < p) {
                    m_primes.push_back(todo[k1]);
                }
                break;
            }
            unsigned k2 = 0;
            for (; k1 < todo_sz; k1++, k2++) {
                todo[k2] = todo[k1];
            }
            todo.resize(k2);
        }
    }

public:
    prime_generator() {
        m_primes.push_back(2);
        m_primes.push_back(3);
        process_next_k_numbers(128);
    }

    uint64 operator()(unsigned idx) {
        if (idx < m_primes.size())
            return m_primes[idx];
        if (idx > LEAN_PRIME_LIST_MAX_SIZE)
            throw exception("prime generator capacity exceeded");
        process_next_k_numbers(1024);
        if (idx < m_primes.size())
            return m_primes[idx];
        while (idx <= m_primes.size())
            process_next_k_numbers(1024*16);
        return m_primes[idx];
    }
};

static prime_generator * g_prime_generator = nullptr;
static mutex           * g_prime_generator_mutex = nullptr;

void initialize_primes() {
    g_prime_generator = new prime_generator();
    g_prime_generator_mutex = new mutex();
}

void finalize_primes() {
    delete g_prime_generator_mutex;
    delete g_prime_generator;
}

prime_iterator::prime_iterator():
    m_idx(0) {
}

uint64 prime_iterator::next() {
    unsigned idx = m_idx;
    m_idx++;
    {
        lock_guard<mutex> guard(*g_prime_generator_mutex);
        return (*g_prime_generator)(idx);
    }
}

bool is_prime(uint64 p) {
    // Naive is_prime implementation that tests for divisors up to sqrt(p),
    // and skips multiples of 2 and 3
    if (p == 2 || p == 3)
        return true;
    uint64 i = 5;
    while (i*i <= p) {
        if (p % i == 0)
            return false;
        i += 2;
        if (p % i == 0)
            return false;
        i += 3;
    }
    return true;
}
}
