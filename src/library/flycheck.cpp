/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/flycheck.h"

namespace lean {

static char const * flycheck_kind_of_severity(message_severity severity) {
    switch (severity) {
        case INFORMATION: return "INFORMATION";
        case WARNING:     return "WARNING";
        case ERROR:       return "ERROR";
        default: lean_unreachable();
    }
}

void flycheck_message_stream::report(message_bucket_id const &, message const & msg) {
    m_out << "FLYCHECK_BEGIN " << flycheck_kind_of_severity(msg.get_severity()) << std::endl;
    m_out << msg.get_file_name()
          << ":" << msg.get_pos().first << ":" << msg.get_pos().second << ": ";
    switch (msg.get_severity()) {
        case INFORMATION: m_out << "information: "; break;
        case WARNING:     m_out << "warning: "; break;
        case ERROR:       m_out << "error: "; break;
    }
    if (!msg.get_caption().empty())
        m_out << msg.get_caption() << ":\n";
    m_out << msg.get_text() << "\n";
    m_out << "FLYCHECK_END" << std::endl;
}

}
