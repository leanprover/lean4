/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <iostream>
#include <vector>

namespace lean {
constexpr unsigned scanner_buffer_size = 1024;

/**
    \brief Base class for all scanners in Lean

    It provides basic support for reading streams, buffering, and caching the contents of the input stream.
*/
class scanner {
protected:
    bool               m_interactive;
    int                m_spos; // position in the current line of the stream
    char               m_curr;  // current char;

    int                m_line;  // line
    int                m_pos;   // start position of the token

    char               m_buffer[scanner_buffer_size];
    unsigned           m_bpos;
    unsigned           m_bend;
    std::istream&      m_stream;

    bool               m_cache_input;
    std::vector<char>  m_cache;
    std::vector<char>  m_cache_result;

    char curr() const { return m_curr; }
    void new_line() { m_line++; m_spos = 0; }
    void next();

public:
    scanner(std::istream& stream, bool interactive = false);
    ~scanner();

    int get_line() const { return m_line; }
    int get_pos() const { return m_pos; }

    void start_caching();
    void stop_caching();
    unsigned cache_size() const;
    void reset_cache();
    char const * cached_str(unsigned begin, unsigned end);
};

}
