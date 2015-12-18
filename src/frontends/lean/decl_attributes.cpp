/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/replace_visitor.h"
#include "library/attribute_manager.h"
#include "library/blast/forward/pattern.h"
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
            bool has_prio_attr = false;
            for (auto const & entry : m_entries) {
                if (get_attribute_kind(entry.m_attr.c_str()) == attribute_kind::Prioritized) {
                    has_prio_attr = true;
                    break;
                }
            }
            if (!has_prio_attr) {
                throw parser_error("invalid '[priority]' attribute, declaration has not been marked with a prioritized attribute", pos);
            }
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
                    switch (get_attribute_kind(attr)) {
                    case attribute_kind::Default:
                    case attribute_kind::Prioritized:
                        m_entries = cons(entry(attr), m_entries);
                        break;
                    case attribute_kind::Parametric: {
                        unsigned v = p.parse_small_nat();
                        if (v == 0)
                            throw parser_error("invalid attribute parameter, value must be positive", pos);
                        p.check_token_next(get_rbracket_tk(), "invalid attribute, ']' expected");
                        m_entries = cons(entry(attr, v-1), m_entries);
                        break;
                    }
                    case attribute_kind::OptParametric:
                        if (!p.curr_is_token(get_rbracket_tk())) {
                            unsigned v = p.parse_small_nat();
                            if (v == 0)
                                throw parser_error("invalid attribute parameter, value must be positive", pos);
                            p.check_token_next(get_rbracket_tk(), "invalid attribute, ']' expected");
                            m_entries = cons(entry(attr, v-1), m_entries);
                        } else {
                            p.check_token_next(get_rbracket_tk(), "invalid attribute, ']' expected");
                            m_entries = cons(entry(attr), m_entries);
                        }
                        break;
                    case attribute_kind::MultiParametric: {
                        buffer<unsigned> vs;
                        while (true) {
                            unsigned v = p.parse_small_nat();
                            if (v == 0)
                                throw parser_error("invalid attribute parameter, value must be positive", pos);
                            vs.push_back(v-1);
                            if (p.curr_is_token(get_rbracket_tk()))
                                break;
                        }
                        p.next();
                        m_entries = cons(entry(attr, to_list(vs)), m_entries);
                        break;
                    }}
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
    if (has_pattern_hints(env.get(d).get_type())) {
        // turn on [forward] if patterns hints have been used in the type.
        entries.push_back(entry("forward"));
    }
    unsigned i = entries.size();
    while (i > 0) {
        --i;
        auto const & entry = entries[i];
        char const * attr = entry.m_attr.c_str();
        switch (get_attribute_kind(attr)) {
        case attribute_kind::Default:
            env = set_attribute(env, ios, attr, d, ns, m_persistent);
            break;
        case attribute_kind::Prioritized:
            if (m_prio)
                env = set_prio_attribute(env, ios, attr, d, *m_prio, ns, m_persistent);
            else
                env = set_prio_attribute(env, ios, attr, d, LEAN_DEFAULT_PRIORITY, ns, m_persistent);
            break;
        case attribute_kind::Parametric:
            env = set_param_attribute(env, ios, attr, d, head(entry.m_params), ns, m_persistent);
            break;
        case attribute_kind::OptParametric:
            if (entry.m_params)
                env = set_opt_param_attribute(env, ios, attr, d, optional<unsigned>(head(entry.m_params)), ns, m_persistent);
            else
                env = set_opt_param_attribute(env, ios, attr, d, optional<unsigned>(), ns, m_persistent);
            break;
        case attribute_kind::MultiParametric:
            env = set_params_attribute(env, ios, attr, d, entry.m_params, ns, m_persistent);
            break;
        }
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
