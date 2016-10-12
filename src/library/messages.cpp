/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#include "library/messages.h"

namespace lean {

message::message(parser_exception const & ex) :
        message(ex.get_file_name(), pos_info(ex.get_line(), ex.get_pos()),
                ERROR, ex.get_msg()) {}

void output_channel_message_stream::report(message const & msg) {
    if (msg.get_severity() != INFORMATION) {
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
