/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <vector>
#include <string>
#include <unordered_map>
#include "util/interrupt.h"
#include "library/definition_cache.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/info_manager.h"

namespace lean {
/**
   \brief Class for managing an input stream used to communicate with
   external processes.
*/
class server {
    class worker;
    class file {
        friend class server::worker;
        std::string               m_fname;
        mutable mutex             m_lines_mutex;
        std::vector<std::string>  m_lines;
        snapshot_vector           m_snapshots;
        info_manager              m_info;

        unsigned find(unsigned line_num);
        unsigned copy_to(std::string & block, unsigned starting_from);
    public:
        file(std::istream & in, std::string const & fname);
        void replace_line(unsigned line_num, std::string const & new_line);
        void insert_line(unsigned line_num, std::string const & new_line);
        void remove_line(unsigned line_num);
        void show(std::ostream & out, bool valid);
        std::string const & get_fname() const { return m_fname; }
        info_manager const & infom() const { return m_info; }
        void sync(std::vector<std::string> const & lines);
    };
    typedef std::shared_ptr<file>                     file_ptr;
    typedef std::unordered_map<std::string, file_ptr> file_map;
    class worker {
        snapshot              m_empty_snapshot;
        definition_cache &    m_cache;
        file_ptr              m_todo_file;
        optional<std::string> m_base_dir;
        unsigned              m_todo_line_num;
        options               m_todo_options;
        mutex                 m_todo_mutex;
        condition_variable    m_todo_cv;
        file_ptr              m_last_file;
        atomic_bool           m_terminate;
        interruptible_thread  m_thread;
    public:
        worker(environment const & env, io_state const & ios, definition_cache & cache,
               optional<std::string> const & base_dir);
        ~worker();
        void set_todo(file_ptr const & f, unsigned line_num, options const & o);
        void request_interrupt();
        bool wait(optional<unsigned> const & ms);
    };

    file_map                  m_file_map;
    file_ptr                  m_file;
    environment               m_env;
    io_state                  m_ios;
    std::ostream &            m_out;
    optional<std::string>     m_base_dir;
    unsigned                  m_num_threads;
    snapshot                  m_empty_snapshot;
    definition_cache          m_cache;
    worker                    m_worker;

    void load_file(std::string const & fname, bool error_if_nofile = true);
    void save_olean(std::string const & fname);
    void visit_file(std::string const & fname);
    void check_file();
    void replace_line(unsigned line_num, std::string const & new_line);
    void insert_line(unsigned line_num, std::string const & new_line);
    void remove_line(unsigned line_num);
    void show_info(unsigned line_num, optional<unsigned> const & col_num);
    void process_from(unsigned line_num);
    void set_option(std::string const & line);
    void eval_core(environment const & env, options const & o, std::string const & line);
    void eval(std::string const & line);
    void display_decl(name const & short_name, name const & long_name, environment const & env, options const & o);
    void display_decl(name const & long_name, environment const & env, options const & o);
    void find_pattern(unsigned line_num, std::string const & pattern);
    unsigned find(unsigned line_num);
    void read_line(std::istream & in, std::string & line);
    void interrupt_worker();
    void show_options();
    void show(bool valid);
    void sync(std::vector<std::string> const & lines);
    void wait(optional<unsigned> ms);
    unsigned get_line_num(std::string const & line, std::string const & cmd);
    optional<unsigned> get_optional_num(std::string const & line, std::string const & cmd);
    unsigned get_num(std::string const & line, std::string const & cmd);
    pair<unsigned, optional<unsigned>> get_line_opt_col_num(std::string const & line, std::string const & cmd);
    pair<unsigned, unsigned> get_line_col_num(std::string const & line, std::string const & cmd);
    void find_goal_matches(unsigned line_num, unsigned col_num, std::string const & filters);

public:
    server(environment const & env, io_state const & ios, optional<std::string> const & base_dir, unsigned num_threads = 1);
    ~server();
    bool operator()(std::istream & in);
};

bool parse_server_trace(environment const & env, io_state const & ios, char const * fname, optional<std::string> const & base_dir);

void initialize_server();
void finalize_server();
}
