/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#if defined(LEAN_SERVER)
#include "json.h"

namespace lean {

json json_of_severity(message_severity sev) {
    switch (sev) {
        case INFORMATION: return "information";
        case WARNING:     return "warning";
        case ERROR:       return "error";
        default: lean_unreachable();
    }
}

json json_of_message(message const & msg) {
    json j;
    j["file_name"] = msg.get_file_name();
    j["pos_line"]  = msg.get_pos().first;
    j["pos_col"]   = msg.get_pos().second;
    j["severity"]  = json_of_severity(msg.get_severity());
    j["caption"]   = msg.get_caption();
    j["text"]      = msg.get_text();
    return j;
}

void json_message_stream::report(message const & msg) {
    m_out << json_of_message(msg) << std::endl;
}

}
#endif
