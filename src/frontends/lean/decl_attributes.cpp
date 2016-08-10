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
void decl_attributes::parse(parser & p) {
    while (true) {
        auto pos   = p.pos();
        if (auto it = parse_priority(p)) {
            m_prio = *it;
        } else if (p.curr_is_command()) {
           if (auto attr = get_attribute_from_token(p.get_token_info().token().get_string())) {
               p.next();
               for (auto const & entry : m_entries) {
                   if (are_incompatible(entry.m_attr, attr)) {
                       throw parser_error(sstream() << "invalid attribute [" << attr
                                                    << "], declaration was already marked with [" << entry.m_attr
                                                    << "]", pos);
                   }
               }
               auto data = attr->parse_data(p);
               p.check_token_next(get_rbracket_tk(), "invalid attribute declaration, ']' expected");
               m_entries = cons({attr, data}, m_entries);
               if (attr->get_name() == "parsing_only")
                   m_parsing_only = true;
           } else {
               break;
           }
        } else {
            break;
        }
    }
}

environment decl_attributes::apply(environment env, io_state const & ios, name const & d) const {
    buffer<entry> entries;
    to_buffer(m_entries, entries);
    unsigned i = entries.size();
    while (i > 0) {
        --i;
        auto const & entry = entries[i];
        if (auto prio_attr = dynamic_cast<prio_attribute const *>(entry.m_attr)) {
            unsigned prio = m_prio ? *m_prio : LEAN_DEFAULT_PRIORITY;
            env = prio_attr->set(env, ios, d, prio, m_persistent);
        } else {
            env = entry.m_attr->set_untyped(env, ios, d, entry.m_params, m_persistent);
        }
    }
    return env;
}
}
