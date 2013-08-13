/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <cstdio>
#include "scanner.h"
#include "debug.h"

namespace lean {

scanner::scanner(std::istream& stream, bool interactive):
    m_interactive(interactive),
    m_spos(0),
    m_curr(0),
    m_line(1),
    m_pos(0),
    m_bpos(0),
    m_bend(0),
    m_stream(stream),
    m_cache_input(false) {
}

scanner::~scanner() {
}

void scanner::next() {
    if (m_cache_input)
        m_cache.push_back(m_curr);
    lean_assert(m_curr != EOF);
    if (m_interactive) {
        m_curr = m_stream.get();
    }
    else if (m_bpos < m_bend) {
        m_curr = m_buffer[m_bpos];
        m_bpos++;
    }
    else {
        m_stream.read(m_buffer, scanner_buffer_size);
        m_bend = static_cast<unsigned>(m_stream.gcount());
        m_bpos = 0;
        if (m_bpos == m_bend) {
            m_curr = EOF;
        }
        else {
            m_curr = m_buffer[m_bpos];
            m_bpos++;
        }
    }
    m_spos++;
}

void scanner::start_caching() {
    m_cache_input = true;
    m_cache.clear();
}

void scanner::stop_caching() {
    m_cache_input = false;
}

unsigned scanner::cache_size() const {
    return m_cache.size();
}

void scanner::reset_cache() {
    m_cache.clear();
}

char const * scanner::cached_str(unsigned begin, unsigned end) {
    m_cache_result.clear();
    while (isspace(m_cache[begin]) && begin < end)
        begin++;
    while (begin < end && isspace(m_cache[end-1]))
        end--;
    for (unsigned i = begin; i < end; i++)
        m_cache_result.push_back(m_cache[i]);
    m_cache_result.push_back(0);
    return m_cache_result.data();
}

}
