/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include <functional>
#include "frontends/lean/server.h"
#include "frontends/lean/parser.h"

namespace lean {
server::server(environment const & env, io_state const & ios, unsigned num_threads):
    m_env(env), m_options(ios.get_options()), m_ios(ios), m_num_threads(num_threads),
    m_empty_snapshot(m_env, m_options) {
}

static std::string g_file("FILE");
static std::string g_replace("REPLACE");
static std::string g_info("INFO");

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

/**
   \brief Return index i <= m_snapshots.size() s.t.
      * forall j < i, m_snapshots[j].m_line < line
      * forall i <= j < m_snapshots.size(),  m_snapshots[j].m_line >= line
*/
unsigned server::find(unsigned linenum) {
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

void server::process_from(unsigned linenum) {
    unsigned i = find(linenum);
    m_snapshots.resize(i);
    snapshot & s = i == 0 ? m_empty_snapshot : m_snapshots[i-1];
    std::string block;
    lean_assert(s.m_line > 0);
    m_info.invalidate(s.m_line-1);
    for (unsigned j = s.m_line-1; j < m_lines.size(); j++) {
        block += m_lines[j];
        block += '\n';
    }
    std::istringstream strm(block);
    m_ios.set_options(s.m_options);
    parser p(s.m_env, m_ios, strm, m_fname.c_str(), false, 1, s.m_lds, s.m_eds, s.m_line,
             &m_snapshots, &m_info);
    p();
}

void server::read_file(std::string const & fname) {
    std::ifstream in(fname);
    if (in.bad() || in.fail()) {
        std::cout << "Error: failed to open file '" << fname << "'";
    } else {
        m_fname = fname;
        m_lines.clear();
        for (std::string line; std::getline(in, line);) {
            m_lines.push_back(line);
        }
        process_from(0);
    }
}

void server::replace_line(unsigned linenum, std::string const & new_line) {
    while (linenum >= m_lines.size())
        m_lines.push_back("");
    m_lines[linenum] = new_line;
    process_from(linenum);
}

void server::show_info(unsigned linenum) {
    unsigned i = find(linenum);
    environment const & env = i == 0 ? m_env     : m_snapshots[i-1].m_env;
    options const & o       = i == 0 ? m_options : m_snapshots[i-1].m_options;
    m_ios.set_options(o);
    io_state_stream out(env, m_ios);
    m_info.display(out, linenum);
    out << "-- ENDINFO" << endl;
}

bool server::operator()(std::istream & in) {
    for (std::string line; std::getline(in, line);) {
        if (is_command(g_file, line)) {
            std::string fname = line.substr(g_file.size());
            trim(fname);
            read_file(fname);
        } else if (is_command(g_replace, line)) {
            std::string data = line.substr(g_replace.size());
            trim(data);
            unsigned linenum = atoi(data.c_str());
            if (std::getline(in, line)) {
                replace_line(linenum, line);
            } else {
                std::cout << "Error: unexpected end of input\n";
                return false;
            }
        } else if (is_command(g_info, line)) {
            std::string data = line.substr(g_info.size());
            trim(data);
            unsigned linenum = atoi(data.c_str());
            show_info(linenum);
        } else {
            std::cout << "Error: unexpected command line: " << line << "\n";
        }
    }
    return true;
}
}
