/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#pragma once
#include <string>
#include "util/log_tree.h"
#include "util/message_definitions.h"
#include "util/parser_exception.h"

namespace lean {

enum message_severity { INFORMATION, WARNING, ERROR };

class message : public log_entry_cell {
    std::string        m_file_name;
    pos_info           m_pos;
    optional<pos_info> m_end_pos;
    message_severity   m_severity;
    std::string        m_caption, m_text;
public:
    message(std::string const & file_name, pos_info const & pos, optional<pos_info> const & end_pos,
            message_severity severity, std::string const & caption, std::string const & text) :
        m_file_name(file_name), m_pos(pos), m_end_pos(end_pos),
        m_severity(severity), m_caption(caption), m_text(text) {}
    message(std::string const & file_name, pos_info const & pos,
            message_severity severity, std::string const & caption, std::string const & text) :
        m_file_name(file_name), m_pos(pos),
        m_severity(severity), m_caption(caption), m_text(text) {}
    message(std::string const & file_name, pos_info const & pos,
            message_severity severity, std::string const & text) :
        message(file_name, pos, severity, std::string(), text) {}
    message(std::string const & file_name, pos_info const & pos,
            message_severity severity) :
        message(file_name, pos, severity, std::string()) {}
    message(parser_exception const & ex);

    std::string get_file_name() const { return m_file_name; }
    pos_info get_pos() const { return m_pos; }
    optional<pos_info> get_end_pos() const { return m_end_pos; }
    message_severity get_severity() const { return m_severity; }
    std::string get_caption() const { return m_caption; }
    std::string get_text() const { return m_text; }
    location get_location() const { return {m_file_name, {m_pos, m_pos}}; }

    bool is_error() const { return m_severity >= ERROR; }
};

std::ostream & operator<<(std::ostream &, message const &);
void report_message(message const &);

bool is_error_message(log_entry const &);
task<bool> has_errors(log_tree::node const &);

}
