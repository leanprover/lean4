/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <utility>
#include <string>
#include <vector>
#include "util/name_map.h"
#include "util/scoped_map.h"
#include "util/script_exception.h"
#include "util/script_state.h"
#include "kernel/expr_maps.h"
#include "kernel/io_state.h"
#include "kernel/environment.h"
#include "library/kernel_bindings.h"
#include "library/tactic/tactic.h"
#include "library/elaborator/elaborator_exception.h"
#include "library/unsolved_metavar_exception.h"
#include "frontends/lean/scanner.h"
#include "frontends/lean/parser_types.h"
#include "frontends/lean/parser_error.h"
#include "frontends/lean/operator_info.h"
#include "frontends/lean/frontend_elaborator.h"

// Lean encodes
//    proj1 i t
// as
//    proj1 (proj2 (proj2 ... t) ...)
// So, a big \c i may make Lean run out of memory.
// The default limit is 10000. I don't believe anybody needs to create a tuple with
// more than 10000 entries
#ifndef LEAN_MAX_PROJECTION
#define LEAN_MAX_PROJECTION 10000
#endif

namespace lean {
class parser_imp;
class calc_proof_parser;

bool get_parser_verbose(options const & opts);
bool get_parser_show_errors(options const & opts);

/** \brief Auxiliary object that stores a reference to the parser object inside the Lua State */
struct set_parser {
    script_state::weak_ref m_state;
    parser_imp *   m_prev;
    set_parser(script_state * S, parser_imp * ptr);
    ~set_parser();
};

/**
    \brief Actual implementation for the default Lean parser

    \remark It is an instance of a Pratt parser
    (http://en.wikipedia.org/wiki/Pratt_parser) described in the paper
    "Top down operator precedence". This algorithm is super simple,
    and it is easy to support user-defined infix/prefix/postfix/mixfix
    operators.
*/
class parser_imp {
    friend class parser;
    friend int mk_cmd_macro(lua_State * L);
    typedef scoped_map<name, unsigned, name_hash, name_eq> local_decls;
    typedef name_map<expr> builtins;
    typedef expr_map<pos_info> expr_pos_info;
    typedef expr_map<tactic>   tactic_hints; // a mapping from placeholder to tactic
    typedef scoped_map<name, name, name_hash, name_eq>      using_decls;
    enum class scope_kind { Scope, Namespace };

    std::weak_ptr<parser_imp>          m_this;
    environment                        m_env;
    io_state                           m_io_state;
    scanner                            m_scanner;
    std::string                        m_strm_name; // input stream name
    frontend_elaborator                m_elaborator;
    macros const *                     m_expr_macros;
    macros const *                     m_cmd_macros;
    macros const *                     m_tactic_macros;
    scanner::token                     m_curr;
    bool                               m_use_exceptions;
    bool                               m_interactive;
    bool                               m_found_errors;
    local_decls                        m_local_decls;
    unsigned                           m_num_local_decls;
    expr_pos_info                      m_expr_pos_info;
    pos_info                           m_last_cmd_pos;
    pos_info                           m_last_script_pos;
    tactic_hints                       m_tactic_hints;
    using_decls                        m_using_decls;
    std::vector<name>                  m_namespace_prefixes;
    std::vector<scope_kind>            m_scope_kinds;
    std::unique_ptr<calc_proof_parser> m_calc_proof_parser;


    // If true then return error when parsing identifiers and it is not local or global.
    // We set this flag off when parsing tactics. The apply_tac may reference
    // a hypothesis in the proof state. This hypothesis is not visible until we
    // execute the tactic.
    bool                m_check_identifiers;

    script_state *      m_script_state;
    set_parser          m_set_parser;

    bool                m_verbose;
    bool                m_show_errors;

    template<typename F>
    typename std::result_of<F(lua_State * L)>::type using_script(F && f) {
        return m_script_state->apply([&](lua_State * L) {
                set_io_state    set1(L, m_io_state);
                set_environment set2(L, m_env);
                return f(L);
            });
    }

    void code_with_callbacks(std::function<void()> && f);

    /**
        \brief Auxiliar struct for creating/destroying a new scope for
        local declarations.
    */
    struct mk_scope {
        parser_imp &          m_fn;
        local_decls::mk_scope m_scope;
        unsigned              m_old_num_local_decls;
        mk_scope(parser_imp & fn);
        ~mk_scope();
    };

    calc_proof_parser & get_calc_proof_parser();

public:
    environment const & get_environment() const { return m_env; }

    /** \brief Return the current position information */
    pos_info pos() const { return mk_pair(m_scanner.get_line(), m_scanner.get_pos()); }

    /** \brief Return the position associated with \c e. If there is none, then return \c default_pos. */
    pos_info pos_of(expr const & e, pos_info default_pos);

    /** \brief Associate position \c p with \c e and return \c e */
    expr save(expr const & e, pos_info p) { m_expr_pos_info[e] = p; return e; }

    /** \brief Read the next token. */
    void scan() { m_curr = m_scanner.scan(); }
    /** \brief Return the current token */
    scanner::token curr() const { return m_curr; }
    /** \brief Read the next token if the current one is not End-of-file. */
    void next() { if (m_curr != scanner::token::Eof) scan(); }

    /** \brief Return the name associated with the current token. */
    name const & curr_name() const { return m_scanner.get_name_val(); }
    /** \brief Return the numeral associated with the current token. */
    mpq const & curr_num() const { return m_scanner.get_num_val(); }
    /** \brief Return the string associated with the current token. */
    std::string const & curr_string() const { return m_scanner.get_str_val(); }
    /**
        \brief Check if the current token is \c t, and move to the
        next one. If the current token is not \c t, it throws a parser error.
    */
    void check_next(scanner::token t, char const * msg);

    /** \brief Return true iff the current token is an identifier */
    bool curr_is_identifier() const { return curr() == scanner::token::Id; }
    /** \brief Return true iff the current token is a '_" */
    bool curr_is_placeholder() const { return curr() == scanner::token::Placeholder; }
    /** \brief Return true iff the current token is a natural number */
    bool curr_is_nat() const { return curr() == scanner::token::IntVal && m_scanner.get_num_val() >= 0; }
    /** \brief Return true iff the current token is a '(' */
    bool curr_is_lparen() const { return curr() == scanner::token::LeftParen; }
    /** \brief Return true iff the current token is a '{' */
    bool curr_is_lcurly() const { return curr() == scanner::token::LeftCurlyBracket; }
    /** \brief Return true iff the current token is a ':' */
    bool curr_is_colon() const { return curr() == scanner::token::Colon; }
    /** \brief Return true iff the current token is a ',' */
    bool curr_is_comma() const { return curr() == scanner::token::Comma; }
    /** \brief Return true iff the current token is a ':=' */
    bool curr_is_assign() const { return curr() == scanner::token::Assign; }
    /** \brief Return true iff the current token is an 'in' token */
    bool curr_is_in() const { return curr() == scanner::token::In; }
    /** \brief Return true iff the current token is '.' */
    bool curr_is_period() const { return curr() == scanner::token::Period; }
    /** \brief Throws a parser error if the current token is not an identifier. */
    void check_identifier(char const * msg) { if (!curr_is_identifier()) throw parser_error(msg, pos()); }
    /**
        \brief Throws a parser error if the current token is not an
        identifier. If it is, move to the next token.
    */
    name check_identifier_next(char const * msg) { check_identifier(msg); name r = curr_name(); next(); return r; }
    /** \brief Throws a parser error if the current token is not '_'. If it is, move to the next token. */
    void check_placeholder_next(char const * msg) { check_next(scanner::token::Placeholder, msg); }
    /** \brief Throws a parser error if the current token is not ':'. If it is, move to the next token. */
    void check_colon_next(char const * msg) { check_next(scanner::token::Colon, msg); }
    /** \brief Throws a parser error if the current token is not ','. If it is, move to the next token. */
    void check_comma_next(char const * msg) { check_next(scanner::token::Comma, msg); }
    /** \brief Throws a parser error if the current token is not ')'. If it is, move to the next token. */
    void check_rparen_next(char const * msg) { check_next(scanner::token::RightParen, msg); }
    /** \brief Throws a parser error if the current token is not '}'. If it is, move to the next token. */
    void check_rcurly_next(char const * msg) { check_next(scanner::token::RightCurlyBracket, msg); }
    /** \brief Throws a parser error if the current token is not ':='. If it is, move to the next token. */
    void check_assign_next(char const * msg) { check_next(scanner::token::Assign, msg); }
    /** \brief Throws a parser error if the current token is not '.'. If it is, move to the next token. */
    void check_period_next(char const * msg) { check_next(scanner::token::Period, msg); }

    std::string check_string_next(char const * msg);

    /**
       @name Error handling
    */
    /*@{*/
private:
    void display_error_pos(unsigned line, unsigned pos);
    void display_error_pos(pos_info const & p);
    void display_error(char const * msg, unsigned line, unsigned pos);

    struct lean_pos_info_provider : public pos_info_provider {
        std::shared_ptr<parser_imp> m_parser;
        pos_info                    m_pos;
        lean_pos_info_provider(std::shared_ptr<parser_imp> const & p, pos_info const & pos):m_parser(p), m_pos(pos) {}
        virtual std::pair<unsigned, unsigned> get_pos_info(expr const & e) const;
        virtual std::pair<unsigned, unsigned> get_some_pos() const { return m_pos; }
        virtual char const * get_file_name() const;
    };

    void display_error(tactic_cmd_error const & ex);
    void display_error(script_exception const & ex);
    void display_error(exception const & ex);
public:
    void protected_call(std::function<void()> && f, std::function<void()> && sync);
    /*@}*/

public:
    unsigned parse_unsigned(char const * msg);
    double parse_double();

private:
    [[ noreturn ]] void not_implemented_yet();
    void updt_options();
    void parse_script(bool as_expr = false);
    void parse_script_expr();


    /**
       @name Parse Universe levels
    */
    /*@{*/
private:
    level parse_level_max();
    level parse_level_nud_id();
    level parse_level_nud_int();
    level parse_level_lparen();
    level parse_level_nud();
    level parse_level_led_plus(level const & left);
    level parse_level_led_cup(level const & left);
    level parse_level_led(level const & left);
    unsigned curr_level_lbp();
public:
    /** \brief Parse a universe level */
    level parse_level(unsigned rbp = 0);
    /*@}*/


    /**
       @name Parse Expressions
    */
    /*@{*/
private:
    unsigned get_implicit_vector_size(expr const & d);
    std::vector<bool> const & get_smallest_implicit_vector(list<expr> const & ds);
    unsigned get_smallest_implicit_vector_size(list<expr> const & ds);
    expr mk_fun(operator_info const & op, pos_info const & pos);
    expr mk_application(operator_info const & op, pos_info const & pos, unsigned num_args, expr const * args);
    expr mk_application(operator_info const & op, pos_info const & pos, std::initializer_list<expr> const & l);
    expr mk_application(operator_info const & op, pos_info const & pos, expr const & arg);
    expr mk_application(operator_info const & op, pos_info const & pos, buffer<expr> const & args);
    expr parse_prefix(operator_info const & op);
    expr parse_postfix(expr const & left, operator_info const & op, pos_info const & op_pos);
    expr parse_infix(expr const & left, operator_info const & op, pos_info const & op_pos);
    expr parse_infixl(expr const & left, operator_info const & op, pos_info const & op_pos);
    expr parse_infixr(expr const & left, operator_info const & op, pos_info const & op_pos);
    void check_op_part(name const & op_part);
    void parse_mixfix_args(list<name> const & ops, unsigned prec, buffer<expr> & args);
    expr parse_mixfixl(operator_info const & op);
    expr parse_mixfixr(expr const & left, operator_info const & op, pos_info const & op_pos);
    expr parse_mixfixo(expr const & left, operator_info const & op, pos_info const & op_pos);
    expr parse_mixfixc(operator_info const & op);
    void propagate_position(expr const & e, pos_info p);
    bool is_curr_begin_expr() const;
    bool is_curr_begin_tactic() const;
    typedef buffer<std::pair<macro_arg_kind, void*>> macro_arg_stack;
    struct macro_result {
        optional<expr>    m_expr;
        optional<tactic>  m_tactic;
        macro_result(expr const & e):m_expr(e) {}
        macro_result(tactic const & t):m_tactic(t) {}
        macro_result() {}
    };
    macro_result parse_macro(list<macro_arg_kind> const & arg_kinds, luaref const & fn, unsigned prec, macro_arg_stack & args,
                             pos_info const & p);
    expr parse_expr_macro(name const & id, pos_info const & p);
    expr parse_led_id(expr const & left);
    expr parse_arrow(expr const & left);
    expr parse_cartesian_product(expr const & left);
    expr parse_lparen();
    void parse_names(buffer<std::pair<pos_info, name>> & result);
    void register_binding(name const & n);
    void parse_simple_parameters(parameter_buffer & result, bool implicit_decl, bool suppress_type);
    expr mk_abstraction(expr_kind k, parameter_buffer const & parameters, expr const & body);
    expr parse_abstraction(expr_kind k);
    expr parse_lambda();
    expr parse_pi();
    expr parse_sig();
    expr parse_exists();
    expr parse_let();
    expr parse_type(bool level_expected);
    expr parse_tuple();
    expr parse_proj(bool first);
    tactic parse_tactic_macro(name tac_id, pos_info const & p);
    expr parse_have_expr();
    expr parse_calc();
    expr parse_nud_id();
    expr parse_nud();
    expr parse_led(expr const & left);
    expr mk_app_left(expr const & left, expr const & arg);
    unsigned curr_lbp();
    expr parse_nat_int();
    expr parse_decimal();
    expr parse_string();
    expr parse_by_expr();
public:
    /**
       \brief Try to find an object (Definition or Postulate) named \c
       id in the frontend/environment. If there isn't one, then tries
       to check if \c id is a builtin symbol. If it is not throws an error.

       If \c implicit_args is true, then we also parse explicit arguments until
       we have a placeholder forall implicit ones.
    */
    expr get_name_ref(name const & id, pos_info const & p, bool implicit_args = true);
    /**
        \brief Parse a sequence of <tt>'(' ID ... ID ':' expr ')'</tt>.

        This is used when parsing lambda, Pi, forall/exists expressions and
        definitions.

        \remark If implicit_decls is true, then we allow declarations
        with curly braces. These declarations are used to tag implicit
        arguments. Such as:
        <code> Definition f {A : Type} (a b : A) : A := ... </code>

        \see parse_simple_parameters
    */
    void parse_parameters(parameter_buffer & result, bool implicit_decls, bool suppress_type);
    /** \brief Parse parameters for expressions such as: lambda, pi, forall, exists */
    void parse_expr_parameters(parameter_buffer & result);
    void parse_var_decl_parameters(parameter_buffer & result);
    void parse_definition_parameters(parameter_buffer & result);
    /** \brief Parse a tactic expression, it can be

        1) A Lua Script Block expression that returns a tactic
        2) '(' expr ')' where expr is a proof term
        3) identifier that is the name of a tactic or proof term.
    */
    tactic parse_tactic_expr();
    /** \brief Parse \c _ a hole that must be filled by the elaborator. */
    expr parse_placeholder();
    /** \brief Parse an expression */
    expr parse_expr(unsigned rbp = 0);
    /*@}*/


    /**
       @name Tactics
    */
    /*@{*/
private:
    /** \brief Return true iff the current token is a tactic command */
    bool curr_is_tactic_cmd() const;
    void display_proof_state(proof_state s);
    void display_proof_state_if_interactive(proof_state s);
    typedef std::vector<proof_state_seq> proof_state_seq_stack;
    std::pair<proof_state, proof_state_seq> apply_tactic(proof_state const & s, tactic const & t, pos_info const & p);
    expr mk_proof_for(proof_state const & s, pos_info const & p, context const & ctx, expr const & expected_type);
    void back_cmd(/* inout */ proof_state_seq_stack & stack, /* inout */ proof_state & s);
    void tactic_cmd(/* inout */ proof_state_seq_stack & stack, /* inout */ proof_state & s);
    expr done_cmd(proof_state const & s, context const & ctx, expr const & expected_type);
    expr parse_tactic_cmds(proof_state s, context const & ctx, expr const & expected_type);
    std::pair<optional<tactic>, pos_info> get_tactic_for(expr const & mvar);
    std::pair<expr, context> get_metavar_ctx_and_type(expr const & mvar, metavar_env const & menv);
    expr apply_tactics(expr const & val, metavar_env & menv);
    /*@}*/

private:
    /**
       @name Parse Commands
    */
    /*@{*/
    static list<name> const & get_command_keywords();
    void register_implicit_arguments(name const & n, parameter_buffer & parameters);
    void check_no_metavar(expr const & e, metavar_env const & menv, char const * msg);
    void check_no_metavar(std::pair<expr, metavar_env> const & p, char const * msg);
    name mk_full_name(name const & n);
    void parse_def_core(bool is_definition);
    void parse_definition();
    void parse_theorem();
    void parse_variable_core(bool is_var);
    void parse_variable();
    void parse_variables();
    void parse_axiom();
    void parse_eval();
    bool is_hidden_object(object const & obj) const;
    void parse_print();
    void parse_check();
    unsigned parse_precedence();
    name parse_op_id();
    void parse_op(fixity fx);
    void parse_notation_decl();
    void parse_set_option();
    void parse_set_opaque();
    optional<std::string> find_lua_file(std::string const & fname);
    void parse_import();
    void parse_help();
    void parse_coercion();
    void reset_env(environment env);
    void parse_scope();
    void parse_pop();
    void parse_cmd_macro(name cmd_id, pos_info const & p);
    void parse_universe();
    void parse_alias();
    void parse_builtin();
    void parse_namespace();
    void parse_end();
    void parse_using();
    void parse_rewrite_set();
    void parse_ids_and_rsid(buffer<name> & ids, name & rsid);
    void parse_add_rewrite();
    void parse_enable_rewrite(bool flag);
    bool parse_command();
    void sync_command();
    /*@}*/

public:
    parser_imp(environment const & env, io_state const & st, std::istream & in, char const * strm_name,
               script_state * S, bool use_exceptions, bool interactive);
    ~parser_imp();
    static void show_prompt(bool interactive, io_state const & ios);
    void show_prompt();
    void show_tactic_prompt();
    /** \brief Parse a sequence of commands. This method also perform error management. */
    bool parse_commands();
    /** \brief Parse an expression. */
    expr parse_expr_main();
};
}
