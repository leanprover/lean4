/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include <string>
#include "library/messages.h"
#include "frontends/lean/info_manager.h"
#include "util/task_builder.h"

namespace lean {

message::message(parser_exception const & ex) :
        message(ex.get_file_name(), *ex.get_pos(),
                ERROR, ex.get_msg()) {}

std::ostream & operator<<(std::ostream & out, message const & msg) {
    if (msg.get_severity() != INFORMATION) {
        out << msg.get_file_name() << ":" << msg.get_pos().first << ":" << msg.get_pos().second << ": ";
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
    auto & l = logtree();
    auto & loc = logtree().get_location();

    std::shared_ptr<message> msg;
    if (loc.m_file_name.empty()) {
        msg = std::make_shared<message>(msg0);
    } else {
        auto pos_ok = loc.m_range.m_begin <= msg0.get_pos() && msg0.get_pos() <= loc.m_range.m_end;
        msg = std::make_shared<message>(loc.m_file_name, pos_ok ? msg0.get_pos() : loc.m_range.m_begin,
            msg0.get_severity(), msg0.get_caption(), msg0.get_text());
    }
    l.add(msg);
}

task<bool> has_errors(log_tree::node const & n) {
    return n.has_entry(is_error_message);
}

bool is_error_message(log_entry const & e) {
    if (auto msg = dynamic_cast<message const *>(e.get())) {
        return msg->is_error();
    }
    return false;
}

}
