/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include <string>
#include "library/definitions_cache.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/info_manager.h"

namespace lean {
/**
   \brief Class for managing an input stream used to communicate with
   external processes.
*/
class server {
    std::vector<std::string>  m_lines;
    snapshot_vector           m_snapshots;
    info_manager              m_info;
    environment               m_env;
    options                   m_options;
    io_state                  m_ios;
    unsigned                  m_num_threads;
    snapshot                  m_empty_snapshot;
    std::string               m_fname;
    unsigned                  m_from;
    definitions_cache         m_cache;

    void read_file(std::string const & fname);
    void replace_line(unsigned linenum, std::string const & new_line);
    void insert_line(unsigned linenum, std::string const & new_line);
    void remove_line(unsigned linenum);
    void show_info(unsigned linenum);
    void process_from(unsigned linenum);
    unsigned find(unsigned linenum);
    void update();
    void read_line(std::istream & in, std::string & line);
    unsigned get_linenum(std::string const & line, std::string const & cmd);

public:
    server(environment const & env, io_state const & ios, unsigned num_threads = 1);
    bool operator()(std::istream & in);
};
}
