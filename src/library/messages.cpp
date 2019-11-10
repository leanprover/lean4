/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <string>
#include "library/messages.h"
#include "library/trace.h"

namespace lean {

message::message(parser_exception const & ex) :
        message(ex.get_file_name(), *ex.get_pos(), ERROR, ex.get_msg()) {}

std::ostream & operator<<(std::ostream & out, message const & msg) {
    if (msg.get_severity() != INFORMATION) {
        out << msg.get_filename() << ":" << msg.get_pos().first << ":" << msg.get_pos().second << ": ";
        switch (msg.get_severity()) {
            case INFORMATION: break;
            case WARNING: out << "warning: "; break;
            case ERROR:   out << "error: ";   break;
        }
        if (!msg.get_caption().empty())
            out << msg.get_caption() << ":\n";
    }
    auto const & text = msg.get_text();
    out << text;
    if (!text.size() || text[text.size() - 1] != '\n')
        out << "\n";
    return out;
}

void report_message(message const & msg0) {
    if (!get_global_ios().get_options().get_bool(name {"trace", "as_messages"}, false)) {
        // Print immediately. Still add as a message so that we get the error code correct.
        get_global_ios().get_diagnostic_stream() << msg0;
    }
    lean_assert(global_message_log());
    global_message_log()->add(msg0);
}

LEAN_THREAD_PTR(message_log, g_message_log);

scope_message_log::scope_message_log(message_log * l) :
        flet<message_log *>(g_message_log, l) {}

message_log * global_message_log() {
    return g_message_log;
}

bool message_log::has_errors() const {
    for (auto const & m : m_rev_list) {
        if (m.is_error()) {
            return true;
        }
    }
    return false;
}

void message_log::add(message const & m) {
    m_rev_list = cons(m, m_rev_list);
}

buffer<message> message_log::to_buffer() const {
    buffer<message> buf;
    for (auto const & m : m_rev_list) {
        buf.push_back(m);
    }
    std::reverse(buf.begin(), buf.end());
    return buf;
}
}
