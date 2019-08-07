/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "util/name_map.h"
#include "util/name_set.h"
#include "kernel/local_ctx.h"
#include "kernel/expr.h"
#include "library/formatter.h"

namespace lean {
bool is_local_decl_ref(expr const & e);

class metavar_context;
class local_context;
bool depends_on(expr const & e, metavar_context const & mctx, unsigned num, expr const * locals);
bool depends_on(local_decl const & d, metavar_context const & mctx,  unsigned num, expr const * locals);
bool depends_on(expr const & e, metavar_context const & mctx,  buffer<expr> const & locals);
bool depends_on(local_decl const & d, metavar_context const & mctx, buffer<expr> const & locals);

/* Similar to depends_on(expr const & e, metavar_context const & mctx, unsigned num, expr const * locals), but it
   will also visit the value v of local definitions (x : t := v) if x occurs in e (directly or indirectly). */
bool depends_on(expr const & e, metavar_context const & mctx, local_context const & lctx, unsigned num, expr const * locals);
inline bool depends_on(expr const & e, metavar_context const & mctx, local_context const & lctx, expr const & local) {
    return depends_on(e, mctx, lctx, 1, &local);
}

/* Create an unieq local_decl name.
   This is a low-level function. The high-level methods
   at local_context use this function internally. */
name mk_local_decl_name();

class metavar_context;

/* Extend kernel local context object with support for generating "unused" user-names and
   "freezing" local instances. */
class local_context : public local_ctx {
    friend class type_context_old;

    local_context remove(buffer<expr> const & locals) const;
    expr mk_local_decl(name const & n, name const & un, expr const & type,
                       optional<expr> const & value, binder_info bi);
    local_decl mk_local_decl_core(name const & n, name const & un, expr const & type, binder_info bi);
    local_decl mk_local_decl_core(name const & n, name const & un, expr const & type, expr const & value);
    unsigned num_indices() const;
    optional<local_decl> get_decl_at(unsigned idx) const;
public:
    local_context() {}

    expr mk_local_decl(expr const & type, binder_info bi = mk_binder_info());
    expr mk_local_decl(expr const & type, expr const & value);
    expr mk_local_decl(name const & un, expr const & type, binder_info bi = mk_binder_info());
    expr mk_local_decl(name const & un, expr const & type, expr const & value);

    /* Low-level version of the methods above.

       \pre `n` was created using mk_local_decl_name
       \pre there is no local_decl named `n` in this local_context. */
    expr mk_local_decl(name const & n, name const & un, expr const & type, binder_info bi = mk_binder_info());
    expr mk_local_decl(name const & n, name const & un, expr const & type, expr const & value);

    /** \brief Return the most recently added local_decl \c d s.t. d.get_user_name() == n
        \remark This method is used to implement tactics such as 'revert'. */
    optional<local_decl> find_local_decl_from_user_name(name const & n) const;

    optional<local_decl> find_last_local_decl() const;
    local_decl get_last_local_decl() const;

    /** \brief Execute fn for each local declaration created after \c d. */
    void for_each_after(local_decl const & d, std::function<void(local_decl const &)> const & fn) const;

    /** \brief Return a non-none iff other local decls depends on \c d. If the result is not none,
        then it is the name of the local decl that depends on d.
        \pre \c d is in this local context. */
    optional<local_decl> has_dependencies(local_decl const & d, metavar_context const & mctx) const;

    /** \brief Return an unused hypothesis "user name" with the given prefix, the suffix is an
        unsigned >= idx. */
    name get_unused_name(name const & prefix, unsigned & idx) const;
    name get_unused_name(name const & suggestion) const;
    bool uses_user_name(name const & n) const;

    /** \brief Return true iff all locals in this context are in the set \c ls. */
    bool is_subset_of(name_set const & ls) const;
    /** \brief Return true iff all locals in this context are also in \c ctx. */
    bool is_subset_of(local_context const & ctx) const;

    void pop_local_decl();

    /** \brief Traverse local declarations based on the order they were created */
    void for_each(std::function<void(local_decl const &)> const & fn) const;
    optional<local_decl> find_if(std::function<bool(local_decl const &)> const & pred) const; // NOLINT
    optional<local_decl> back_find_if(std::function<bool(local_decl const &)> const & pred) const; // NOLINT

    /** \brief We say a local context is well-formed iff all local declarations only
        contain local_decl references that were defined before them.

        \remark This method is for debugging purposes. */
    bool well_formed() const;

    /** \brief Return true iff \c e is well-formed with respect to this local context.
        That is, all local_decl references in \c e are defined in this context. */
    bool well_formed(expr const & e) const;

    format pp(formatter const & fmt) const; // NOLINT

    /** \brief Replaced assigned metavariables with their values.
        This method is a little bit hackish since it reuses the names and ids of
        the existing local_decls. So, it may affect cached information.

        This method is mainly used in the elaborator for reporting errors,
        and for instantiating metavariables created by the elaborator before
        invoking the tactic framework. */
    local_context instantiate_mvars(metavar_context & ctx) const;

    /** \brief Erase inaccessible annotations from the local context.
        This function is defined in the file library/equations_compiler/util.h.
        It is a little bit hackish (like instantiate_mvars) since it reuses the names
        and ids of existing local_decls. So, it may affect cached information.

        This function is used in the elaborator before invoking the tactic framework. */
    friend local_context erase_inaccessible_annotations(local_context const & lctx);
};

/** \brief Return true iff `e` contains a local_decl_ref that contains a value */
bool contains_let_local_decl(local_context const & lctx, expr const & e);

/** \brief Expand all local_decl_refs (that have values) in `e` */
expr zeta_expand(local_context const & lctx, expr const & e);

void initialize_local_context();
void finalize_local_context();
}
