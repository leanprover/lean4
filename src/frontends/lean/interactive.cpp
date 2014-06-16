/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <iostream>
#include <sstream>
#include <vector>
#include <algorithm>
#include "frontends/lean/interactive.h"

namespace lean {
interactive::interactive(environment const & env, io_state const & ios, script_state const & ss, unsigned num_threads,
                         char const * ack_cmd, char const * snapshot_cmd, char const * restore_cmd, char const * restart_cmd):
    m_env(env), m_ios(ios), m_ss(ss), m_num_threads(num_threads), m_line(1),
    m_ack_cmd(ack_cmd), m_snapshot_cmd(snapshot_cmd), m_restore_cmd(restore_cmd), m_restart_cmd(restart_cmd) {
    save_snapshot();
}

void interactive::parse_block(std::string const & str, char const * strm_name) {
    if (str.size() > 0) {
        std::istringstream block(str);
        parser p(m_env, m_ios, block, strm_name, &m_ss, false, m_num_threads, m_lds, m_eds, m_line);
        p();
        m_env  = p.env();
        m_ios  = p.ios();
        m_lds  = p.get_local_level_decls();
        m_eds  = p.get_local_expr_decls();
        m_line = p.pos().first;
    }
}

void interactive::save_snapshot() {
    m_snapshots.push_back(snapshot(m_env, m_lds, m_eds, m_ios.get_options(), m_line));
}

void interactive::restore(unsigned new_line, std::string & block) {
    block.clear();
    lean_assert(new_line > 0);
    // try to find a snapshop
    unsigned i = m_snapshots.size();
    while (i > 0) {
        --i;
        if (m_snapshots[i].m_line <= new_line)
            break;
    }
    m_snapshots.resize(i+1);
    auto & s = m_snapshots[i];
    m_env  = s.m_env;
    m_lds  = s.m_lds;
    m_eds  = s.m_eds;
    m_ios.set_options(s.m_options);
    m_line = s.m_line;
    unsigned new_sz = std::min(new_line, static_cast<unsigned>(m_lines.size())) - 1;
    m_lines.resize(new_sz);
    for (unsigned i = s.m_line; i < new_sz; i++) {
        block += m_lines[i];
        block += '\n';
    }
}

void interactive::operator()(std::istream & in, char const * strm_name) {
    std::string block;
    for (std::string line; std::getline(in, line);) {
        if (line == m_ack_cmd) {
            parse_block(block, strm_name);
            block.clear();
        } else if (line == m_snapshot_cmd) {
            parse_block(block, strm_name);
            save_snapshot();
            block.clear();
        } else if (line.compare(0, m_restore_cmd.size(), m_restore_cmd) == 0) {
            parse_block(block, strm_name);
            block.clear();
            std::string rest = line.substr(m_restore_cmd.size());
            restore(std::atoi(rest.c_str()), block);
        } else if (line == m_restart_cmd) {
            parse_block(block, strm_name);
            block.clear();
            // keep consuming lines while they match the m_lines
            unsigned i = 0;
            while (true) {
                if (!std::getline(in, line))
                    return; // end of file
                if (m_lines[i] != line)
                    break;
                i++;
            }
            restore(i+1, block);
            block += line;
            block += '\n';
        } else {
            block += line;
            block += '\n';
            m_lines.push_back(line);
        }
    }
    parse_block(block, strm_name);
}
}
