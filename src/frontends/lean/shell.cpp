/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#ifdef LEAN_USE_READLINE
#include <stdio.h>
#include <readline/readline.h>
#include <readline/history.h>
#include <stdlib.h>
#include <unistd.h>
#include <algorithm>
#endif
#include <string>
#include "frontends/lean/shell.h"
#include "frontends/lean/pp.h"

namespace lean {
#ifdef LEAN_USE_READLINE
// Hackish wrapper for implementing a streambuf on top of the readline library
class readline_streambuf : public std::streambuf {
    std::string      m_buffer;
    std::streamsize  m_curr;
    std::streamsize  m_high;
protected:
    virtual int_type underflow() {
        while (m_curr == m_high) {
            char * line = readline("");
            if (!line) {
                // EOF received
                return traits_type::eof();
            } else if (strlen(line) == 0) {
                // ignore blank line
                m_buffer.push_back('\n');
                free(line);
            } else {
                add_history(line);
                m_buffer += line;
                m_buffer.push_back('\n');
                free(line);
                m_high = m_buffer.size();
            }
        }

        return traits_type::to_int_type(m_buffer[m_curr]);
    }

    virtual int_type uflow() {
        int_type r = underflow();
        if (r != traits_type::eof())
            m_curr++;
        return r;
    }

    virtual int_type pbackfail(int_type c) {
        if (m_curr == 0)
            return traits_type::eof();
        m_curr--;
        if (c != traits_type::eof())
            m_buffer[m_curr] = c;
        return traits_type::eof() + 1; // something different from eof()
    }

    virtual std::streamsize showmanyc() {
        return m_high - m_curr;
    }

public:
    readline_streambuf():
        m_curr(0), m_high(0) {
        setbuf(0, 0);
    }
};

struct readline_config {
    FILE * m_devnull;
    readline_config() {
        // By default, the readline library echos the input in the standard output.
        // We can change this behavior by setting rl_outstream to /dev/null
        m_devnull = fopen("/dev/null", "a");
        rl_outstream = m_devnull;
    }
    ~readline_config() {
        fclose(m_devnull);
    }
};
static readline_config g_readline_config;
#endif

shell::shell(environment const & env, io_state const & ios, script_state * S):m_env(env), m_io_state(ios), m_script_state(S) {
}

shell::shell(environment const & env, script_state * S):m_env(env), m_io_state(), m_script_state(S) {
    m_io_state.set_formatter(mk_pp_formatter(m_env));
}

shell::~shell() {
}

bool shell::operator()() {
#ifdef LEAN_USE_READLINE
    readline_streambuf buf;
    std::istream is(&buf);
    parser p(m_env, m_io_state, is, m_script_state, false, true);
#else
    parser p(m_env, m_io_state, std::cin, m_script_state, false, true);
#endif
    return p();
}
}
