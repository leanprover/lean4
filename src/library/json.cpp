/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Gabriel Ebner
*/
#ifdef LEAN_JSON
#include "library/json.h"
#include <string>
#include "library/protected.h"
#include "kernel/declaration.h"
#include "library/scoped_ext.h"
#include "kernel/instantiate.h"

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
    j["file_name"] = msg.get_filename();
    j["pos_line"]  = msg.get_pos().first;
    j["pos_col"]   = msg.get_pos().second;
    if (auto end_pos = msg.get_end_pos()) {
        j["end_pos_line"] = end_pos->first;
        j["end_pos_col"]  = end_pos->second;
    }
    j["severity"]  = json_of_severity(msg.get_severity());
    j["caption"]   = msg.get_caption();
    j["text"]      = msg.get_text();
    return j;
}

void print_json(std::ostream & out, message const & msg) {
    out << json_of_message(msg) << std::endl;
}

}
#endif
