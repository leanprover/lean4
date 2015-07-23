/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/environment.h"
#include "library/io_state.h"
namespace lean {
class parser;
class decl_attributes {
    bool               m_is_abbrev; // if true only abbreviation attributes are allowed
    bool               m_persistent;
    bool               m_is_instance;
    bool               m_is_trans_instance;
    bool               m_is_coercion;
    bool               m_is_reducible;
    bool               m_is_irreducible;
    bool               m_is_semireducible;
    bool               m_is_quasireducible;
    bool               m_is_class;
    bool               m_is_parsing_only;
    bool               m_has_multiple_instances;
    bool               m_unfold_full_hint;
    bool               m_constructor_hint;
    bool               m_symm;
    bool               m_trans;
    bool               m_refl;
    bool               m_subst;
    bool               m_recursor;
    bool               m_simp;
    bool               m_congr;
    optional<unsigned> m_recursor_major_pos;
    optional<unsigned> m_priority;
    list<unsigned>     m_unfold_hint;

    void parse(name const & n, parser & p);
public:
    decl_attributes(bool is_abbrev = false, bool persistent = true);
    void parse(buffer<name> const & ns, parser & p);
    void parse(parser & p);
    environment apply(environment env, io_state const & ios, name const & d) const;
    bool is_parsing_only() const { return m_is_parsing_only; }
    void write(serializer & s) const;
    void read(deserializer & d);
};
}
