/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <string>
#include "kernel/environment.h"
#include "library/io_state.h"

namespace lean {
struct parser;
typedef object_ref syntax;
class decl_attributes {
public:
    /* Entries for the new attribute manager implemented in Lean */
    struct new_entry {
        name   m_attr;
        bool   m_deleted;
        bool   m_scoped;
        syntax m_args;
    };
private:
    bool               m_persistent;
    list<new_entry>    m_before_elab_entries;
    list<new_entry>    m_after_tc_entries;
    list<new_entry>    m_after_comp_entries;
    void parse_core(parser & p, bool compact);
    expr parse_attr_arg(parser & p, name const & attr_id);
    syntax expr_to_syntax(expr const & e);
    environment apply_new_entries(environment env, list<new_entry> const & es, name const & d) const;
    bool has_attribute(list<new_entry> const & entries, name const & attr_name) const;
public:
    decl_attributes(bool persistent = true): m_persistent(persistent) {}
    bool has_attribute(environment const & env, name const & attr_name) const;
    /* attributes: zero-or-more [ ... ] */
    void parse(parser & p);
    /* Parse attributes after `@[` ... ] */
    void parse_compact(parser & p);
    void set_attribute(environment const & env, name const & attr_name);
    environment apply_before_elab(environment env, io_state const & ios, name const & d) const;
    environment apply_after_tc(environment env, io_state const & ios, name const & d) const;
    environment apply_after_comp(environment env, name const & d) const;
    environment apply_all(environment env, io_state const & ios, name const & d) const;
    void set_persistent(bool persistent) { m_persistent = persistent; }
    bool ok_for_inductive_type() const;
    bool has_class() const;
    operator bool() const { return static_cast<bool>(m_after_tc_entries) || static_cast<bool>(m_after_comp_entries); }
};

void initialize_decl_attributes();
void finalize_decl_attributes();
}
