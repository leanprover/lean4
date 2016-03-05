/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "library/local_context.h"

namespace lean {
class metavar_decl {
    local_decls m_context;
    expr        m_type;
    friend class metavar_context;
    metavar_decl(local_decls const & ctx, expr const & type):m_context(ctx), m_type(type) {}
public:
    metavar_decl() {}
    expr const & get_type() const { return m_type; }
    local_decls const & get_context() const { return m_context; }
};

bool is_univ_metavar_decl_ref(level const & l);
bool is_metavar_decl_ref(expr const & e);

class metavar_context {
    name_map<metavar_decl> m_decls;
    name_map<level>        m_uassignment;
    name_map<expr>         m_eassignment;
    friend struct instantiate_fn;
public:
    level mk_univ_metavar_decl();
    expr mk_metavar_decl(local_context const & ctx, expr const & type);

    optional<metavar_decl> get_metavar_decl(expr const & e) const;

    bool is_assigned(level const & l) const {
        lean_assert(is_univ_metavar_decl_ref(l));
        return m_uassignment.contains(meta_id(l));
    }

    bool is_assigned(expr const & m) const {
        lean_assert(is_metavar_decl_ref(m));
        return m_eassignment.contains(mlocal_name(m));
    }

    void assign(level const & u, level const & l);
    void assign(expr const & e, expr const & v);

    level instantiate(level const & l);
    expr instantiate(expr const & e);

    bool has_assigned(level const & l) const;
    bool has_assigned(levels const & ls) const;
    bool has_assigned(expr const & e) const;
};

void initialize_metavar_context();
void finalize_metavar_context();
}
