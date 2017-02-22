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
    out << msg.get_text() << "\n";
    return out;
}

void report_message(message const & msg) {
    logtree().add(std::make_shared<message>(msg));
}

static bool has_errors_sync(log_tree::node const & n) {
    for (auto & e : n.get_entries()) {
        if (auto msg = dynamic_cast<message const *>(e.get())) {
            if (msg->get_severity() >= message_severity::ERROR) {
                return true;
            }
        }
    }
    bool err = false;
    n.get_children().for_each([&] (name const &, log_tree::node const & c) {
        if (!err) err = has_errors_sync(c);
    });
    return err;
}

task<bool> has_errors(log_tree::node const & n) {
    return task_builder<bool>([=] { return has_errors_sync(n); })
            .depends_on(n.wait_for_finish())
            .build();
}

}
