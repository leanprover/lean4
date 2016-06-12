/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name_map.h"
#include "util/name_set.h"
#include "kernel/expr.h"

namespace lean {
class local_decl {
public:
    struct cell {
        /*
          <name> : <type> := <value>

          m_pp_name is used for interacting with the user.
          It may not be not unique.
        */
        name               m_name; /* this one is unique */
        name               m_pp_name;
        expr               m_type;
        optional<expr>     m_value;
        binder_info        m_bi;
        unsigned           m_idx;
        MK_LEAN_RC(); // Declare m_rc counter
        void dealloc();
        cell(unsigned idx, name const & n, name const & pp_n, expr const & t, optional<expr> const & v,
             binder_info const & bi);
    };
private:
    cell * m_ptr;
    friend class local_context;
    friend void initialize_local_context();
    local_decl(unsigned idx, name const & n, name const & pp_n, expr const & t, optional<expr> const & v, binder_info const & bi);
public:
    local_decl();
    local_decl(local_decl const & s):m_ptr(s.m_ptr) { if (m_ptr) m_ptr->inc_ref(); }
    local_decl(local_decl && s):m_ptr(s.m_ptr) { s.m_ptr = nullptr; }
    ~local_decl() { if (m_ptr) m_ptr->dec_ref(); }
    local_decl & operator=(local_decl const & s) { LEAN_COPY_REF(s); }
    local_decl & operator=(local_decl && s) { LEAN_MOVE_REF(s); }

    friend bool is_eqp(local_decl const & a, local_decl const & b) { return a.m_ptr == b.m_ptr; }

    name const & get_name() const { return m_ptr->m_name; }
    name const & get_pp_name() const { return m_ptr->m_pp_name; }
    expr const & get_type() const { return m_ptr->m_type; }
    optional<expr> const & get_value() const { return m_ptr->m_value; }
    binder_info const & get_info() const { return m_ptr->m_bi; }
    expr mk_ref() const;
    unsigned get_idx() const { return m_ptr->m_idx; }
};

bool is_local_decl_ref(expr const & e);

bool depends_on(expr const & e, unsigned num, expr const * locals);
bool depends_on(local_decl const & d, unsigned num, expr const * locals);
bool depends_on(expr const & e, buffer<expr> const & locals);
bool depends_on(local_decl const & d, buffer<expr> const & locals);

class local_context {
    typedef rb_map<unsigned, local_decl, unsigned_cmp> idx2local_decl;
    unsigned              m_next_idx;
    name_map<local_decl>  m_name2local_decl;
    idx2local_decl        m_idx2local_decl;
    /*
      A local context can optionally have a set of frozen declarations.
      Moreover, type class resolution can be restricted to use only frozen local
      declarations. When this restriction is use, we can cache type class instances
      more efficiently.
    */
    name_set              m_frozen_decls; /* declarations that have been frozen */
    friend class type_context;

    local_context remove(buffer<expr> const & locals) const;
    expr mk_local_decl(name const & n, name const & ppn, expr const & type,
                       optional<expr> const & value, binder_info const & bi);
public:
    local_context():m_next_idx(0) {}

    bool empty() const { return m_idx2local_decl.empty(); }

    expr mk_local_decl(expr const & type, binder_info const & bi = binder_info());
    expr mk_local_decl(expr const & type, expr const & value);
    expr mk_local_decl(name const & ppn, expr const & type, binder_info const & bi = binder_info());
    expr mk_local_decl(name const & ppn, expr const & type, expr const & value);
    /** \brief Return the local declarations for the given reference.
        \pre is_local_decl_ref(e) */
    optional<local_decl> get_local_decl(expr const & e) const;
    optional<local_decl> get_local_decl(name const & n) const;
    /** \brief Traverse local declarations based on the order they were created */
    void for_each(std::function<void(local_decl const &)> const & fn) const;
    optional<local_decl> find_if(std::function<bool(local_decl const &)> const & pred) const; // NOLINT
    optional<local_decl> back_find_if(std::function<bool(local_decl const &)> const & pred) const; // NOLINT

    /** \brief Return the most recently added local_decl \c d s.t. d.get_pp_name() == n
        \remark This method is used to implement tactics such as 'revert'. */
    optional<local_decl> get_local_decl_from_user_name(name const & n) const;

    bool rename_user_name(name const & from, name const & to);

    /** \brief Execute fn for each local declaration created after \c d. */
    void for_each_after(local_decl const & d, std::function<void(local_decl const &)> const & fn) const;

    void freeze(name const & n);
    bool is_frozen(name const & n) const { return m_frozen_decls.contains(n); }

    /** \brief Return true iff all locals in this context are in the set \c ls. */
    bool is_subset_of(name_set const & ls) const;
    /** \brief Return true iff all locals in this context are also in \c ctx. */
    bool is_subset_of(local_context const & ctx) const;

    void pop_local_decl();

    /** \brief We say a local context is well-formed iff all local declarations only
        contain local_decl references that were defined before them.

        \remark This method is for debugging purposes. */
    bool well_formed() const;

    /** \brief Return true iff \c e is well-formed with respect to this local context.
        That is, all local_decl references in \c e are defined in this context.

        \remark This method is for debugging purposes. */
    bool well_formed(expr const & e) const;

    format pp(formatter const & fmt) const;
};

void initialize_local_context();
void finalize_local_context();
}
