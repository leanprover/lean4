/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include <string>
#include "frontends/lean/parser.h"

namespace lean {
/**
   \brief Class for managing an input stream used to communicate with
   external processes.

   It process blocks of Lean commands separated by an ACK string.
   The lean commands may create snapshots that can be resumed at the start
   of the next block.
*/
class interactive {
    struct snapshot {
        environment       m_env;
        local_level_decls m_lds;
        local_expr_decls  m_eds;
        options           m_options;
        unsigned          m_line;
        snapshot():m_line(1) {}
        snapshot(environment const & env, local_level_decls const & lds, local_expr_decls const & eds, options const & opts, unsigned line):
            m_env(env), m_lds(lds), m_eds(eds), m_options(opts), m_line(line) {}
    };

    std::vector<snapshot>     m_snapshots;
    std::vector<std::string>  m_lines;
    environment               m_env;
    io_state                  m_ios;
    script_state              m_ss;
    unsigned                  m_num_threads;
    local_level_decls         m_lds;
    local_expr_decls          m_eds;
    unsigned                  m_line;
    std::string               m_ack_cmd;
    std::string               m_snapshot_cmd;
    std::string               m_restore_cmd;
    std::string               m_restart_cmd;
    void parse_block(std::string const & str, char const * strm_name);
    void save_snapshot();
    void restore(unsigned new_line, std::string & block);
public:
    interactive(environment const & env, io_state const & ios, script_state const & ss,
                unsigned num_threads = 1,
                char const * ack_cmd = "#ACK", char const * snapshot_cmd = "#SNAPSHOT",
                char const * res_cmd = "#RESTORE", char const * restart_cmd = "#RESTART");
    environment const & env() const { return m_env; }
    void operator()(std::istream & in, char const * strm_name);
};
}
