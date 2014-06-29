/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <fstream>
#include <string>
#include "util/sstream.h"
#include "util/lean_path.h"
#include "frontends/lean/scanner.h"

namespace lean {
/**
    \brief Keep scanning the input until finds an import or an Eof.
    If \c import return true, otherwise return false
*/
bool consume_until_import(environment const & env, scanner & s) {
    name import("import");
    scanner::token_kind t;
    while (true) {
        try {
            t = s.scan(env);
        } catch (...) {}
        if (t == scanner::token_kind::Eof)
            return false;
        if (t == scanner::token_kind::CommandKeyword && s.get_token_info().value() == import)
            return true;
    }
}

void display_deps(environment const & env, std::ostream & out, char const * fname) {
    std::ifstream in(fname);
    if (in.bad() || in.fail())
        throw exception(sstream() << "failed to open file '" << fname << "'");
    scanner s(in, fname);
    while (consume_until_import(env, s)) {
        while (true) {
            auto t = s.scan(env);
            if (t != scanner::token_kind::Identifier)
                break;
            std::string m_name = find_file(name_to_file(s.get_name_val()), {".lean", ".olean", ".lua"});
            int last_idx = m_name.find_last_of(".");
            std::string rawname = m_name.substr(0, last_idx);
            std::string ext = m_name.substr(last_idx);
            if (ext == ".lean") {
                m_name = rawname + ".olean";
            }
            display_path(out, m_name);
            out << "\n";
        }
    }
}
}
