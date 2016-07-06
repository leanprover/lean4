/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/replace_visitor.h"
#include "library/attribute_manager.h"
#include "frontends/lean/decl_attributes.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/util.h"

namespace lean {
decl_attributes::decl_attributes(bool is_abbrev, bool persistent) {
    m_is_abbrev              = is_abbrev;
    m_persistent             = persistent;
    m_parsing_only           = false;
    if (is_abbrev)
        m_entries = to_list(entry("reducible"));
}

void decl_attributes::parse(parser & p) {
    buffer<char const *> attr_tokens;
    get_attribute_tokens(attr_tokens);
    while (true) {
        auto pos   = p.pos();
        if (auto it = parse_priority(p)) {
            m_prio = *it;
        } else if (p.curr_is_token(get_parsing_only_tk())) {
            if (!m_is_abbrev)
                throw parser_error("invalid '[parsing_only]' attribute, only abbreviations can be "
                                   "marked as '[parsing_only]'", pos);
            m_parsing_only = true;
            p.next();
        } else {
            bool found = false;
            for (char const * tk : attr_tokens) {
                if (p.curr_is_token(tk)) {
                    p.next();
                    char const * attr = get_attribute_from_token(tk);
                    for (auto const & entry : m_entries) {
                        if (are_incompatible(entry.m_attr.c_str(), attr)) {
                            throw parser_error(sstream() << "invalid attribute [" << attr
                                               << "], declaration was already marked with [" << entry.m_attr << "]", pos);
                        }
                    }
                    buffer<unsigned> vs;
                    while (!p.curr_is_token(get_rbracket_tk())) {
                        unsigned v = p.parse_small_nat();
                        if (v == 0)
                            throw parser_error("invalid attribute parameter, value must be positive", pos);
                        vs.push_back(v-1);
                    }
                    p.next();
                    m_entries = cons(entry(attr, to_list(vs)), m_entries);
                    found = true;
                    break;
                }
            }
            if (!found)
                break;
        }
    }
}

environment decl_attributes::apply(environment env, io_state const & ios, name const & d, name const & ns) const {
    buffer<entry> entries;
    to_buffer(m_entries, entries);
    unsigned i = entries.size();
    while (i > 0) {
        --i;
        auto const & entry = entries[i];
        char const * attr = entry.m_attr.c_str();
        unsigned prio = m_prio ? *m_prio : LEAN_DEFAULT_PRIORITY;
        env = set_attribute(env, ios, attr, d, prio, entry.m_params, ns, m_persistent);
    }
    return env;
}

serializer & operator<<(serializer & s, decl_attributes::entry const & e) {
    s << e.m_attr;
    write_list(s, e.m_params);
    return s;
}

deserializer & operator>>(deserializer & d, decl_attributes::entry & e) {
    d >> e.m_attr;
    e.m_params = read_list<unsigned>(d);
    return d;
}

void decl_attributes::write(serializer & s) const {
    s << m_is_abbrev << m_persistent << m_prio << m_parsing_only;
    write_list(s, m_entries);
}

void decl_attributes::read(deserializer & d) {
    d >> m_is_abbrev >> m_persistent >> m_prio >> m_parsing_only;
    m_entries = read_list<decl_attributes::entry>(d);
}

bool operator==(decl_attributes const & d1, decl_attributes const & d2) {
    return
        d1.m_is_abbrev    == d2.m_is_abbrev ||
        d1.m_persistent   == d2.m_persistent ||
        d1.m_parsing_only == d2.m_parsing_only ||
        d1.m_entries      == d2.m_entries ||
        d1.m_prio         == d2.m_prio;
}
}
