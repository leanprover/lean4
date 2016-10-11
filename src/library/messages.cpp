/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "library/messages.h"
#include "library/flycheck.h"

namespace lean {

message::message(parser_exception const & ex) :
        message(ex.get_file_name(), pos_info(ex.get_line(), ex.get_pos()),
                ERROR, ex.get_msg()) {}

static char const * flycheck_kind_of_severity(message_severity severity) {
    switch (severity) {
        case INFORMATION: return "INFORMATION";
        case WARNING:     return "WARNING";
        case ERROR:       return "ERROR";
        default: lean_unreachable();
    }
}

void output_channel_message_stream::report(message const & msg) {
    flycheck_scope flycheck(m_out->get_stream(), m_options, flycheck_kind_of_severity(msg.get_severity()));
    if (flycheck.enabled() || msg.get_severity() != INFORMATION) {
        m_out->get_stream() << msg.get_file_name()
                            << ":" << msg.get_pos().first << ":" << msg.get_pos().second << ": ";
        switch (msg.get_severity()) {
            case INFORMATION: break;
            case WARNING: m_out->get_stream() << "warning: "; break;
            case ERROR:   m_out->get_stream() << "error: ";   break;
        }
        if (!msg.get_caption().empty())
            m_out->get_stream() << msg.get_caption() << ":\n";
    }
    m_out->get_stream() << msg.get_text() << "\n";
}

}
