/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <functional>
#include "util/sstream.h"
#include "util/exception.h"
#include "util/sexpr/option_declarations.h"
#include "library/aliases.h"
#include "frontends/lean/server.h"
#include "frontends/lean/parser.h"

// #define LEAN_SERVER_DIAGNOSTIC

#if defined(LEAN_SERVER_DIAGNOSTIC)
#define DIAG(CODE) CODE
#else
#define DIAG(CODE)
#endif

namespace lean {
server::file::file(std::istream & in, std::string const & fname):m_fname(fname) {
    for (std::string line; std::getline(in, line);) {
        m_lines.push_back(line);
    }
}

void server::file::replace_line(unsigned linenum, std::string const & new_line) {
    lock_guard<mutex> lk(m_lines_mutex);
    while (linenum >= m_lines.size())
        m_lines.push_back("");
    std::string const & old_line = m_lines[linenum];
    unsigned i = 0;
    while (i < old_line.size() && i < new_line.size() && old_line[i] == new_line[i])
        i++;
    m_info.block_new_info(true);
    m_info.invalidate_line_col(linenum+1, i);
    m_lines[linenum] = new_line;
}

void server::file::insert_line(unsigned linenum, std::string const & new_line) {
    lock_guard<mutex> lk(m_lines_mutex);
    m_info.block_new_info(true);
    m_info.insert_line(linenum+1);
    while (linenum >= m_lines.size())
        m_lines.push_back("");
    m_lines.push_back("");
    lean_assert(m_lines.size() >= linenum+1);
    unsigned i = m_lines.size();
    while (i > linenum) {
        --i;
        m_lines[i] = m_lines[i-1];
    }
    m_lines[linenum] = new_line;
}

void server::file::remove_line(unsigned linenum) {
    lock_guard<mutex> lk(m_lines_mutex);
    m_info.block_new_info(true);
    m_info.remove_line(linenum+1);
    if (linenum >= m_lines.size())
        return;
    lean_assert(!m_lines.empty());
    for (unsigned i = linenum; i < m_lines.size()-1; i++)
        m_lines[i] = m_lines[i+1];
    m_lines.pop_back();
}

void server::file::show(std::ostream & out, bool valid) {
    lock_guard<mutex> lk(m_lines_mutex);
    for (unsigned i = 0; i < m_lines.size(); i++) {
        if (valid) {
            if (m_info.is_invalidated(i+1))
                out << "*";
            else
                out << " ";
            out << " ";
        }
        out << m_lines[i] << "\n";
    }
}

/**
   \brief Return index i <= m_snapshots.size() s.t.
      * forall j < i, m_snapshots[j].m_line < line
      * forall i <= j < m_snapshots.size(),  m_snapshots[j].m_line >= line
*/
unsigned server::file::find(unsigned linenum) {
    unsigned low  = 0;
    unsigned high = m_snapshots.size();
    while (true) {
        lean_assert(low <= high);
        if (low == high)
            return low;
        unsigned mid = low + ((high - low)/2);
        lean_assert(low <= mid && mid < high);
        lean_assert(mid < m_snapshots.size());
        snapshot const & s = m_snapshots[mid];
        if (s.m_line < linenum) {
            low  = mid+1;
        } else {
            high = mid;
        }
    }
}

/** \brief Copy lines [starting_from, m_lines.size()) to block and return the total number of lines */
unsigned server::file::copy_to(std::string & block, unsigned starting_from) {
    unsigned num_lines = m_lines.size();
    for (unsigned j = starting_from; j < num_lines; j++) {
        block += m_lines[j];
        block += '\n';
    }
    return num_lines;
}

server::worker::worker(environment const & env, io_state const & ios, definition_cache & cache):
    m_empty_snapshot(env, ios.get_options()),
    m_cache(cache),
    m_todo_linenum(0),
    m_todo_options(ios.get_options()),
    m_terminate(false),
    m_thread([=]() {
            io_state _ios(ios);
            while (!m_terminate) {
                file_ptr todo_file;
                unsigned todo_linenum = 0;
                options  todo_options;
                // wait for next task
                while (!m_terminate) {
                    unique_lock<mutex> lk(m_todo_mutex);
                    if (m_todo_file) {
                        todo_file    = m_todo_file;
                        todo_linenum = m_todo_linenum;
                        todo_options = m_todo_options;
                        break;
                    } else {
                        m_todo_cv.wait(lk);
                    }
                }
                // extract block of code and snapshot from todo_file
                reset_interrupt();
                bool worker_interrupted = false;
                if (m_terminate)
                    break;
                DIAG(std::cerr << "processing '" << todo_file->get_fname() << "'\n";)
                std::string block;
                unsigned    num_lines;
                snapshot    s;
                {
                    lean_assert(todo_file);
                    lock_guard<mutex> lk(todo_file->m_lines_mutex);
                    unsigned i = todo_file->find(todo_linenum);
                    todo_file->m_snapshots.resize(i);
                    s = i == 0 ? m_empty_snapshot : todo_file->m_snapshots[i-1];
                    lean_assert(s.m_line > 0);
                    todo_file->m_info.block_new_info(false);
                    todo_file->m_info.set_processed_upto(s.m_line);
                    num_lines = todo_file->copy_to(block, s.m_line - 1);
                }
                if (m_terminate)
                    break;
                // parse block of code with respect to snapshot
                try {
                    std::istringstream strm(block);
                    #if defined(LEAN_SERVER_DIAGNOSTIC)
                    std::shared_ptr<output_channel> out1(new stderr_channel());
                    std::shared_ptr<output_channel> out2(new stderr_channel());
                    #else
                    std::shared_ptr<output_channel> out1(new string_output_channel());
                    std::shared_ptr<output_channel> out2(new string_output_channel());
                    #endif
                    io_state tmp_ios(_ios, out1, out2);
                    tmp_ios.set_options(join(s.m_options, _ios.get_options()));
                    bool use_exceptions  = false;
                    unsigned num_threads = 1;
                    parser p(s.m_env, tmp_ios, strm, todo_file->m_fname.c_str(), use_exceptions, num_threads,
                             s.m_lds, s.m_eds, s.m_line, &todo_file->m_snapshots, &todo_file->m_info);
                    p.set_cache(&m_cache);
                    p();
                } catch (interrupted &) {
                    worker_interrupted = true;
                } catch (exception & ex) {
                    DIAG(std::cerr << "worker exception: " << ex.what() << "\n";)
                }
                if (!m_terminate && !worker_interrupted) {
                    DIAG(std::cerr << "finished '" << todo_file->get_fname() << "'\n";)
                    unique_lock<mutex> lk(m_todo_mutex);
                    if (m_todo_file == todo_file && m_last_file == todo_file && m_todo_linenum == todo_linenum) {
                        m_todo_linenum = num_lines + 1;
                        m_todo_file    = nullptr;
                        m_todo_cv.notify_all();
                    }
                }
            }
        }) {}

server::worker::~worker() {
    m_terminate = true;
    request_interrupt();
    m_thread.join();
}

void server::worker::request_interrupt() {
    m_todo_cv.notify_all();
    m_thread.request_interrupt();
}

void server::worker::wait() {
    while (true) {
        unique_lock<mutex> lk(m_todo_mutex);
        if (!m_todo_file)
            break;
        m_todo_cv.wait(lk);
    }
}

void server::worker::set_todo(file_ptr const & f, unsigned linenum, options const & o) {
    lock_guard<mutex> lk(m_todo_mutex);
    if (m_last_file != f || linenum < m_todo_linenum)
        m_todo_linenum = linenum;
    m_todo_file    = f;
    m_last_file    = f;
    m_todo_options = o;
    m_todo_cv.notify_all();
}

server::server(environment const & env, io_state const & ios, unsigned num_threads):
    m_env(env), m_ios(ios), m_out(ios.get_regular_channel().get_stream()),
    m_num_threads(num_threads), m_empty_snapshot(m_env, m_ios.get_options()),
    m_worker(env, ios, m_cache) {
}

server::~server() {
}

void server::interrupt_worker() {
    m_worker.request_interrupt();
}

static std::string g_load("LOAD");
static std::string g_visit("VISIT");
static std::string g_replace("REPLACE");
static std::string g_insert("INSERT");
static std::string g_remove("REMOVE");
static std::string g_info("INFO");
static std::string g_set("SET");
static std::string g_eval("EVAL");
static std::string g_wait("WAIT");
static std::string g_clear_cache("CLEAR_CACHE");
static std::string g_echo("ECHO");
static std::string g_options("OPTIONS");
static std::string g_show("SHOW");
static std::string g_valid("VALID");
static std::string g_sleep("SLEEP");
static std::string g_findp("FINDP");

static bool is_command(std::string const & cmd, std::string const & line) {
    return line.compare(0, cmd.size(), cmd) == 0;
}

static std::string & ltrim(std::string & s) {
    s.erase(s.begin(), std::find_if(s.begin(), s.end(), std::not1(std::ptr_fun<int, int>(std::isspace))));
    return s;
}

static std::string & rtrim(std::string & s) {
    s.erase(std::find_if(s.rbegin(), s.rend(), std::not1(std::ptr_fun<int, int>(std::isspace))).base(), s.end());
    return s;
}

static std::string & trim(std::string & s) {
    return ltrim(rtrim(s));
}

void server::process_from(unsigned linenum) {
    m_worker.set_todo(m_file, linenum, m_ios.get_options());
}

void server::load_file(std::string const & fname) {
    interrupt_worker();
    std::ifstream in(fname);
    if (in.bad() || in.fail()) {
        m_out << "-- ERROR failed to open file '" << fname << "'" << std::endl;
    } else {
        m_file.reset(new file(in, fname));
        m_file_map.insert(mk_pair(fname, m_file));
        process_from(0);
    }
}

void server::visit_file(std::string const & fname) {
    interrupt_worker();
    auto it = m_file_map.find(fname);
    if (it == m_file_map.end()) {
        load_file(fname);
    } else {
        m_file = it->second;
        process_from(0);
    }
}

void server::read_line(std::istream & in, std::string & line) {
    if (!std::getline(in, line))
        throw exception("unexpected end of input");
}

// Given a line of the form "cmd linenum", return the linenum
unsigned server::get_linenum(std::string const & line, std::string const & cmd) {
    std::string data = line.substr(cmd.size());
    trim(data);
    unsigned r = atoi(data.c_str());
    if (r == 0)
        throw exception("line numbers are indexed from 1");
    return r;
}

void server::check_file() {
    if (!m_file)
        throw exception("no file has been loaded/visited");
}

void server::replace_line(unsigned linenum, std::string const & new_line) {
    interrupt_worker();
    check_file();
    m_file->replace_line(linenum, new_line);
    process_from(linenum);
}

void server::insert_line(unsigned linenum, std::string const & new_line) {
    interrupt_worker();
    check_file();
    m_file->insert_line(linenum, new_line);
    process_from(linenum);
}

void server::remove_line(unsigned linenum) {
    interrupt_worker();
    check_file();
    m_file->remove_line(linenum);
    process_from(linenum);
}

void server::set_option(std::string const & line) {
    std::string cmd = "set_option ";
    cmd += line;
    std::istringstream strm(cmd);
    m_out << "-- BEGINSET" << std::endl;
    try {
        parser p(m_env, m_ios, strm, "SET_command", true);
        p();
        m_ios.set_options(p.ios().get_options());
    } catch (exception & ex) {
        m_out << ex.what() << std::endl;
    }
    m_out << "-- ENDSET" << std::endl;
}

void server::show_info(unsigned linenum) {
    check_file();
    m_out << "-- BEGININFO" << std::endl;
    m_file->infom().display(m_env, m_ios, linenum);
    m_out << "-- ENDINFO" << std::endl;
}

void server::eval_core(environment const & env, options const & o, std::string const & line) {
    std::istringstream strm(line);
    io_state ios(m_ios, o);
    m_out << "-- BEGINEVAL" << std::endl;
    try {
        parser p(env, ios, strm, "EVAL_command", true);
        p();
    } catch (exception & ex) {
        m_out << ex.what() << std::endl;
    }
    m_out << "-- ENDEVAL" << std::endl;
}

void server::eval(std::string const & line) {
    if (!m_file) {
        eval_core(m_env, m_ios.get_options(), line);
    } else if (auto p = m_file->infom().get_final_env_opts()) {
        eval_core(p->first, join(p->second, m_ios.get_options()), line);
    } else {
        eval_core(m_env, m_ios.get_options(), line);
    }
}

void server::show_options() {
    m_out << "-- BEGINOPTIONS" << std::endl;
    option_declarations const & decls = get_option_declarations();
    for (auto it = decls.begin(); it != decls.end(); it++) {
        option_declaration const & d = it->second;
        m_out << "-- " << d.get_name() << "|" << d.kind() << "|" << d.get_default_value() << "|" << d.get_description() << "\n";
    }
    m_out << "-- ENDOPTIONS" << std::endl;
}

void server::show(bool valid) {
    check_file();
    m_out << "-- BEGINSHOW" << std::endl;
    m_file->show(m_out, valid);
    m_out << "-- ENDSHOW" << std::endl;
}

static name string_to_name(std::string const & str) {
    name result;
    std::string id_part;
    for (unsigned i = 0; i < str.size(); i++) {
        if (str[i] == '.') {
            result = name(result, id_part.c_str());
            id_part.clear();
        } else {
            id_part.push_back(str[i]);
        }
    }
    return name(result, id_part.c_str());
}

// Return true iff the last part of p is a prefix of the last part of n
static bool is_last_prefix_of(name const & p, name const & n) {
    if (p.is_string() && n.is_string()) {
        char const * it1 = p.get_string();
        char const * it2 = n.get_string();
        if (!it1 || !it2)
            return false;
        while (*it1 && *it2 && *it1 == *it2) {
            ++it1;
            ++it2;
        }
        return *it1 == 0;
    } else {
        return false;
    }
}

// Auxiliary function for find_prefix
// 1) If p is atomic, then we just check if p is a prefix of the last component of n.
// 2) Otherwise, we check if p.get_prefix() == n.get_prefix(), and
//    p.get_string() is a prefix of n.get_string()
static bool is_findp_prefix_of(name const & p, name const & n) {
    if (p.is_atomic())
        return is_last_prefix_of(p, n);
    else
        return p.get_prefix() == n.get_prefix() && is_last_prefix_of(p, n);
}

void server::display_decl(name const & short_name, name const & long_name, environment const & env, options const & o) {
    declaration const & d = env.get(long_name);
    io_state_stream out   = regular(env, m_ios).update_options(o);
    out << short_name << "|" << mk_pair(flatten(out.get_formatter()(d.get_type())), o) << "\n";
}

void server::find_prefix(unsigned linenum, std::string const & prefix) {
    check_file();
    m_out << "-- BEGINFINDP";
    unsigned upto = m_file->infom().get_processed_upto();
    optional<pair<environment, options>> env_opts = m_file->infom().get_closest_env_opts(linenum);
    if (!env_opts) {
        m_out << " NAY" << std::endl;
        m_out << "-- ENDFINDP" << std::endl;
        return;
    }
    if (upto < linenum)
        m_out << " STALE";
    environment const & env = env_opts->first;
    options opts            = env_opts->second;
    opts = join(opts, m_ios.get_options());
    m_out << std::endl;
    name p = string_to_name(prefix);
    name_set already_added;
    for_each_expr_alias(env, [&](name const & n, list<name> const & ds) {
            if (is_findp_prefix_of(p, n)) {
                unsigned num = length(ds);
                if (num == 1) {
                    display_decl(n, head(ds), env, opts);
                    already_added.insert(car(ds));
                } else if (num > 1) {
                    m_out << n << "\n";
                    for (name const & d : ds) {
                        display_decl(d, d, env, opts);
                        already_added.insert(d);
                    }
                }
            }
        });
    env.for_each_declaration([&](declaration const & d) {
            if (!already_added.contains(d.get_name()) && is_findp_prefix_of(p, d.get_name()))
                display_decl(d.get_name(), d.get_name(), env, opts);
        });
    m_out << "-- ENDFINDP" << std::endl;
}

bool server::operator()(std::istream & in) {
    for (std::string line; std::getline(in, line);) {
        try {
            if (is_command(g_load, line)) {
                std::string fname = line.substr(g_load.size());
                trim(fname);
                load_file(fname);
            } else if (is_command(g_visit, line)) {
                std::string fname = line.substr(g_visit.size());
                trim(fname);
                visit_file(fname);
            } else if (is_command(g_echo, line)) {
                std::string str = line.substr(g_echo.size());
                m_out << "--" << str << "\n";
            } else if (is_command(g_replace, line)) {
                unsigned linenum = get_linenum(line, g_replace);
                read_line(in, line);
                replace_line(linenum-1, line);
            } else if (is_command(g_insert, line)) {
                unsigned linenum = get_linenum(line, g_insert);
                read_line(in, line);
                insert_line(linenum-1, line);
            } else if (is_command(g_remove, line)) {
                unsigned linenum = get_linenum(line, g_remove);
                remove_line(linenum-1);
            } else if (is_command(g_info, line)) {
                unsigned linenum = get_linenum(line, g_info);
                show_info(linenum);
            } else if (is_command(g_set, line)) {
                read_line(in, line);
                set_option(line);
            } else if (is_command(g_eval, line)) {
                read_line(in, line);
                eval(line);
            } else if (is_command(g_clear_cache, line)) {
                m_cache.clear();
            } else if (is_command(g_options, line)) {
                show_options();
            } else if (is_command(g_wait, line)) {
                m_worker.wait();
            } else if (is_command(g_show, line)) {
                show(false);
            } else if (is_command(g_valid, line)) {
                show(true);
            } else if (is_command(g_sleep, line)) {
                unsigned ms = get_linenum(line, g_sleep);
                chrono::milliseconds d(ms);
                this_thread::sleep_for(d);
            } else if (is_command(g_findp, line)) {
                unsigned linenum = get_linenum(line, g_findp);
                read_line(in, line);
                find_prefix(linenum, line);
            } else {
                throw exception(sstream() << "unexpected command line: " << line);
            }
        } catch (exception & ex) {
            m_out << "-- ERROR " << ex.what() << std::endl;
        }
    }
    return true;
}
}
