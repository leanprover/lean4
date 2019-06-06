/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/environment.h"
#include "library/attribute_manager.h"
#include "library/io_state.h"
namespace lean {
unsigned get_default_priority(options const & opts);
struct parser;
typedef object_ref syntax;
class decl_attributes {
public:
    struct entry {
        attribute const * m_attr;
        attr_data_ptr     m_params;
        bool deleted() const { return !static_cast<bool>(m_params); }
    };
    /* Entries for the new attribute manager implemented in Lean */
    struct new_entry {
        name   m_attr;
        bool   m_deleted;
        bool   m_scoped;
        syntax m_args;
    };
private:
    bool               m_persistent;
    list<entry>        m_entries;
    list<new_entry>    m_new_entries;
    void parse_core(parser & p, bool compact);
    expr parse_attr_arg(parser & p, name const & attr_id);
    syntax expr_to_syntax(expr const & e);
public:
    decl_attributes(bool persistent = true): m_persistent(persistent) {}
    void set_attribute(environment const & env, name const & attr_name, attr_data_ptr data = get_default_attr_data());
    attr_data_ptr get_attribute(environment const & env, name const & attr_name) const;
    /* attributes: zero-or-more [ ... ] */
    void parse(parser & p);
    /* Parse attributes after `@[` ... ] */
    void parse_compact(parser & p);
    environment apply(environment env, io_state const & ios, name const & d) const;
    list<entry> const & get_entries() const { return m_entries; }
    void set_persistent(bool persistent) { m_persistent = persistent; }
    bool ok_for_inductive_type() const;
    bool has_class() const;
    operator bool() const { return static_cast<bool>(m_entries); }
};

void initialize_decl_attributes();
void finalize_decl_attributes();
}
