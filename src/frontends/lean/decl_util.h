/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include "kernel/expr.h"
#include "library/deep_copy.h"
#include "library/equations_compiler/equations.h"
#include "frontends/lean/decl_attributes.h"
namespace lean {
class parser;
class elaborator;

enum class decl_cmd_kind { Theorem, Definition, Example, Instance, Var, Abbreviation };

struct decl_modifiers {
    bool m_is_private{false};
    bool m_is_protected{false};
    bool m_is_meta{false};
    bool m_is_mutual{false};
    bool m_is_noncomputable{false};

    operator bool() const {
        return m_is_private || m_is_protected || m_is_meta || m_is_mutual || m_is_noncomputable;
    }
};

/** \brief In Lean, declarations may contain nested definitions.
    This object is used to propagate relevant flags to
    nested definitions.

    It is used to set/restore the thread local information. */
class declaration_info_scope {
    declaration_info_scope(name const & ns, decl_cmd_kind kind, decl_modifiers const & modifiers);
public:
    declaration_info_scope(parser const & p, decl_cmd_kind kind, decl_modifiers const & modifiers);
    ~declaration_info_scope();
    bool gen_aux_lemmas() const;
};

/** \brief Similar to declaration_info_scope, but it is used to update
    naming prefix for nested definitions. */
class declaration_name_scope {
    name     m_name;
    name     m_actual_name;
    name     m_old_prefix; /* save current user facing prefix */
    name     m_old_actual_prefix; /* save current prefix */
    unsigned m_old_next_match_idx;
    /* Remark: the operation prefix + name in the following constructors and methods tries to avoid propagating
       the string `_main` into names. That is, `foo._main` + `bla` is `foo.bla`. */
public:
    /* Save the current prefix and match_idx, and set m_name to current prefix + n. */
    declaration_name_scope(name const & n);
    /* Save the current prefix and match_idx, and reset get_definition_info().m_next_match_idx. */
    declaration_name_scope();
    /* Set m_name to current prefix + n. This method is used when the constructor declaration_name_scope
       has been used. */
    void set_name(name const & n);
    /* Restore prefix and match_idx. */
    ~declaration_name_scope();
    name const & get_name() const { return m_name; }
    name const & get_actual_name() const { return m_actual_name; }
};

/** \brief Auxiliary scope for setting m_actual_prefix.
    It is used with declaration_name_scope. */
class private_name_scope {
    name     m_old_actual_prefix; /* save current prefix */
    bool     m_old_is_private;
public:
    /* Remark: If is_private == false, then this auxiliary scope is a no-op. */
    private_name_scope(bool is_private, environment & env);
    ~private_name_scope();
};

/** \brief Auxiliary scope to compute the name for a nested match expression.
    In Lean, we create auxiliary declarations for match expressions. */
class match_definition_scope {
    name m_name;
    name m_actual_name;
public:
    match_definition_scope(environment const & env);
    name const & get_name() const { return m_name; }
    name const & get_actual_name() const { return m_actual_name; }
};

/** \brief Auxiliary scope to switch to `meta` mode when processing a
    `by tac` in a regular definition.
    We need this because we may have a match expression nested
    in `tac`, and we should not create equation lemmas for it. */
class meta_definition_scope {
    bool m_old_is_meta;
public:
    meta_definition_scope();
    ~meta_definition_scope();
};

/** \brief Auxiliary scope to switch to the mode specified by the user.
    That is, meta if the `meta` keyword was used, and regular otherwise.
    We need this because of quoted expressions used in tactics. */
class restore_decl_meta_scope {
    bool m_old_is_meta;
public:
    restore_decl_meta_scope();
    ~restore_decl_meta_scope();
};

/** \brief Return true if the current scope used match-expressions */
bool used_match_idx();

/** \brief Parse explict universe parameters of the form:
           {u_1 ... u_k}

    The universe parameters are automatically added to the parser scope. */
bool parse_univ_params(parser & p, buffer<name> & lp_names);

/** \brief Parse a declaration header of the form

         {u_1 ... u_k} id (params) : type

    The result is the local constant (c : type). The explicit universe level parameters are stored
    at lp_names, and the optional parameters at params.

    Both lp_names and params are added to the parser scope.

    \remark Caller is responsible for using: parser::local_scope scope2(p, env); */
expr parse_single_header(parser & p, declaration_name_scope & s, buffer <name> & lp_names, buffer <expr> & params,
                         bool is_example = false, bool is_instance = false);
/** \brief Parse the header of a mutually recursive declaration. It has the form

        {u_1 ... u_k} id_1, ... id_n (params)

    The explicit universe parameters are stored at lp_names,
    The constant names id_i are stored at cs.
    The names are local constants. Position information for a constant cs[i] can be retrieved using
    p.pos_of(cs[i]).

    Both lp_names, params and cs are added to the parser scope.
    \remark Caller is responsible for adding expressions encoding the c_names to the parser
    scope.
    \remark Caller is responsible for using: parser::local_scope scope2(p, env); */
void parse_mutual_header(parser & p, buffer <name> & lp_names, buffer <expr> & cs, buffer <expr> & params);
/** \brief Parse the header for one of the declarations in a mutually recursive declaration.
    It has the form

         with <attrs> id : type

    The result is (type, attrs). */
pair<expr, decl_attributes> parse_inner_header(parser & p, name const & c_expected);

/** \brief Add section/namespace parameters (and universes) used by params and all_exprs.
    We also add parameters included using the command 'include'.
    lp_names and params are input/output. */
void collect_implicit_locals(parser & p, buffer<name> & lp_names, buffer<expr> & params, buffer<expr> const & all_exprs);
void collect_implicit_locals(parser & p, buffer<name> & lp_names, buffer<expr> & params, std::initializer_list<expr> const & all_exprs);
void collect_implicit_locals(parser & p, buffer<name> & lp_names, buffer<expr> & params, expr const & e);

/** \brief Elaborate the types of the parameters \c params, and update the elaborator local context using them.
    Store the elaborated parameters at new_params.

    \post params.size() == new_params.size() */
void elaborate_params(elaborator & elab, buffer<expr> const & params, buffer<expr> & new_params);

/** \brief Create an alias c_name --> (c_real_name.{level_params} params)
    level_params and params are subsets of lp_names and var_params that were
    declared using the parameter command. */
environment add_local_ref(parser & p, environment const & env, name const & c_name, name const & c_real_name,
                          buffer<name> const & lp_names, buffer<expr> const & var_params);

/** \brief Add alias for new declaration. */
environment add_alias(environment const & env, bool is_protected, name const & c_name, name const & c_real_name);

/** \brief Create an equations header for the given function names.
    It uses the information set using declaration_info_scope */
equations_header mk_equations_header(list<name> const & fn_names, list<name> const & fn_actual_names);
equations_header mk_equations_header(name const & fn_name, name const & fn_actual_name);
equations_header mk_match_header(name const & n, name const & actual_n);

expr replace_locals_preserving_pos_info(expr const & e, buffer<expr> const & from, buffer<expr> const & to);
expr replace_local_preserving_pos_info(expr const & e, expr const & from, expr const & to);
}
