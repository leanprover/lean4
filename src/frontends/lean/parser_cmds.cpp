/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <limits>
#include <utility>
#include <string>
#include "util/sstream.h"
#include "util/lean_path.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/find_fn.h"
#include "kernel/kernel_exception.h"
#include "kernel/normalizer.h"
#include "kernel/type_checker.h"
#include "library/placeholder.h"
#include "library/io_state_stream.h"
#include "frontends/lean/parser_imp.h"
#include "frontends/lean/frontend.h"
#include "frontends/lean/pp.h"
#include "frontends/lean/environment_scope.h"

namespace lean {
// ==========================================
// Builtin commands
static name g_alias_kwd("alias");
static name g_definition_kwd("definition");
static name g_variable_kwd("variable");
static name g_variables_kwd("variables");
static name g_theorem_kwd("theorem");
static name g_axiom_kwd("axiom");
static name g_universe_kwd("universe");
static name g_eval_kwd("eval");
static name g_check_kwd("check");
static name g_infix_kwd("infix");
static name g_infixl_kwd("infixl");
static name g_infixr_kwd("infixr");
static name g_notation_kwd("notation");
static name g_set_option_kwd("set", "option");
static name g_set_opaque_kwd("set", "opaque");
static name g_options_kwd("options");
static name g_env_kwd("environment");
static name g_import_kwd("import");
static name g_help_kwd("help");
static name g_coercion_kwd("coercion");
static name g_exit_kwd("exit");
static name g_print_kwd("print");
static name g_pop_kwd("pop", "scope");
static name g_scope_kwd("scope");
static name g_builtin_kwd("builtin");
static name g_namespace_kwd("namespace");
static name g_end_kwd("end");
static name g_using_kwd("using");
/** \brief Table/List with all builtin command keywords */
static list<name> g_command_keywords = {g_definition_kwd, g_variable_kwd, g_variables_kwd, g_theorem_kwd, g_axiom_kwd, g_universe_kwd, g_eval_kwd,
                                        g_check_kwd, g_infix_kwd, g_infixl_kwd, g_infixr_kwd, g_notation_kwd,
                                        g_set_option_kwd, g_set_opaque_kwd, g_env_kwd, g_options_kwd, g_import_kwd, g_help_kwd, g_coercion_kwd,
                                        g_exit_kwd, g_print_kwd, g_pop_kwd, g_scope_kwd, g_alias_kwd, g_builtin_kwd,
                                        g_namespace_kwd, g_end_kwd, g_using_kwd};
// ==========================================

list<name> const & parser_imp::get_command_keywords() {
    return g_command_keywords;
}

/**
   \brief Register implicit arguments for the definition or
   postulate named \c n. The fourth element in the tuple parameters
   is a flag indiciating whether the argument is implicit or not.
*/
void parser_imp::register_implicit_arguments(name const & n, parameter_buffer & parameters) {
    bool found = false;
    buffer<bool> imp_args;
    for (unsigned i = 0; i < parameters.size(); i++) {
        imp_args.push_back(parameters[i].m_implicit);
        if (imp_args.back())
            found = true;
    }
    if (found)
        mark_implicit_arguments(m_env, n, imp_args.size(), imp_args.data());
}


/** \brief Throw an exception if \c e contains a metavariable */
void parser_imp::check_no_metavar(expr const & e, metavar_env const & menv, char const * msg) {
    auto m = find(e, [](expr const & e) -> bool { return is_metavar(e); });
    if (m) {
        auto p = get_metavar_ctx_and_type(*m, menv);
        throw metavar_not_synthesized_exception(p.second, *m, p.first, msg);
    }
}

void parser_imp::check_no_metavar(std::pair<expr, metavar_env> const & p, char const * msg) {
    check_no_metavar(p.first, p.second, msg);
}


/**
   \brief Return a fully qualified name (i.e., include current namespace)
*/
name parser_imp::mk_full_name(name const & n) {
    return m_namespace_prefixes.back() + n;
}

/** \brief Auxiliary method used for parsing definitions and theorems. */
void parser_imp::parse_def_core(bool is_definition) {
    next();
    expr pre_type, pre_val;
    name id = check_identifier_next("invalid definition, identifier expected");
    parameter_buffer parameters;
    if (curr_is_colon()) {
        next();
        pre_type = parse_expr();
        if (!is_definition && curr_is_period()) {
            pre_val  = save(mk_placeholder(), pos());
        } else {
            check_assign_next("invalid definition, ':=' expected");
            pre_val  = parse_expr();
        }
    } else if (is_definition && curr_is_assign()) {
        auto p   = pos();
        next();
        pre_type = save(mk_placeholder(), p);
        pre_val  = parse_expr();
    } else {
        mk_scope scope(*this);
        parse_definition_parameters(parameters);
        expr type_body;
        if (curr_is_colon()) {
            next();
            type_body = parse_expr();
        } else {
            auto p = pos();
            type_body = save(mk_placeholder(), p);
        }
        pre_type  = mk_abstraction(false, parameters, type_body);
        if (!is_definition && curr_is_period()) {
            pre_val = mk_abstraction(true, parameters, mk_placeholder());
        } else {
            check_assign_next("invalid definition, ':=' expected");
            expr val_body  = parse_expr();
            pre_val   = mk_abstraction(true, parameters, val_body);
        }
    }
    auto r = m_elaborator(id, pre_type, pre_val);
    expr type = std::get<0>(r);
    expr val  = std::get<1>(r);
    metavar_env menv = std::get<2>(r);
    check_no_metavar(type, menv, "invalid definition, type still contains metavariables after elaboration");
    if (has_metavar(val)) {
        val = apply_tactics(val, menv);
    } else {
        check_no_metavar(val, menv, "invalid definition, value still contains metavariables after elaboration");
    }
    lean_assert(!has_metavar(val));
    name full_id = mk_full_name(id);
    if (is_definition) {
        m_env->add_definition(full_id, type, val);
        if (m_verbose)
            regular(m_io_state) << "  Defined: " << full_id << endl;
    } else {
        m_env->add_theorem(full_id, type, val);
        if (m_verbose)
            regular(m_io_state) << "  Proved: " << full_id << endl;
    }
    register_implicit_arguments(full_id, parameters);
}

/**
   \brief Parse a Definition. It has one of the following two forms:

   1) 'Definition' ID ':' expr ':=' expr

   2) 'Definition' ID parameters ':' expr ':=' expr
*/
void parser_imp::parse_definition() {
    parse_def_core(true);
}

/**
   \brief Parse a Theorem. It has one of the following two forms:

   1) 'Theorem' ID ':' expr ':=' expr

   2) 'Theorem' ID parameters ':' expr ':=' expr
*/
void parser_imp::parse_theorem() {
    parse_def_core(false);
}

/** \brief Auxiliary method for parsing Variable and axiom declarations. */
void parser_imp::parse_variable_core(bool is_var) {
    next();
    name id = check_identifier_next("invalid variable/axiom declaration, identifier expected");
    parameter_buffer parameters;
    expr type;
    if (curr_is_colon()) {
        next();
        auto p = m_elaborator(parse_expr());
        check_no_metavar(p, "invalid declaration, type still contains metavariables after elaboration");
        type = p.first;
    } else {
        mk_scope scope(*this);
        parse_var_decl_parameters(parameters);
        check_colon_next("invalid variable/axiom declaration, ':' expected");
        expr type_body = parse_expr();
        auto p = m_elaborator(mk_abstraction(false, parameters, type_body));
        check_no_metavar(p, "invalid declaration, type still contains metavariables after elaboration");
        type = p.first;
    }
    name full_id = mk_full_name(id);
    if (is_var)
        m_env->add_var(full_id, type);
    else
        m_env->add_axiom(full_id, type);
    if (m_verbose)
        regular(m_io_state) << "  Assumed: " << full_id << endl;
    register_implicit_arguments(full_id, parameters);
}

/** \brief Parse one of the two forms:

    1) 'Variable' ID ':' type

    2) 'Variable' ID parameters ':' type
*/
void parser_imp::parse_variable() {
    parse_variable_core(true);
}

/** \brief Parse the form:
    'Variables' ID+ ':' type
*/
void parser_imp::parse_variables() {
    next();
    mk_scope scope(*this);
    parameter_buffer parameters;
    parse_simple_parameters(parameters, false, false);
    for (auto p : parameters) {
        name full_id = mk_full_name(p.m_name);
        if (m_env->find_object(full_id))
            throw already_declared_exception(m_env, full_id);
    }
    for (auto p : parameters) {
        name full_id = mk_full_name(p.m_name);
        expr const & type = p.m_type;
        m_env->add_var(full_id, type);
        if (m_verbose)
            regular(m_io_state) << "  Assumed: " << full_id << endl;
    }
}

/** \brief Parse one of the two forms:

    1) 'Axiom' ID ':' type

    2) 'Axiom' ID parameters ':' type
*/
void parser_imp::parse_axiom() {
    parse_variable_core(false);
}

/** \brief Parse 'Eval' expr */
void parser_imp::parse_eval() {
    next();
    expr v = m_elaborator(parse_expr()).first;
    normalizer norm(m_env);
    expr r = norm(v, context(), true);
    regular(m_io_state) << r << endl;
}

/** \brief Return true iff \c obj is an object that should be ignored by the Show command */
bool parser_imp::is_hidden_object(object const & obj) const {
    return (obj.is_definition() && is_explicit(m_env, obj.get_name())) || !supported_by_pp(obj);
}

/** \brief Parse
    'print' expr
    'print' Environment [num]
    'print' Environment all
    'print' Options
    'print' [string]
*/
void parser_imp::parse_print() {
    next();
    if (curr() == scanner::token::CommandId) {
        name opt_id = curr_name();
        next();
        if (opt_id == g_env_kwd) {
            buffer<object> to_display;
            bool     all = false;
            unsigned end = m_env->get_num_objects(false);
            unsigned i;
            if (curr_is_nat()) {
                i   = parse_unsigned("invalid argument, value does not fit in a machine integer");
            } else if (curr_is_identifier() && curr_name() == "all") {
                next();
                i   = std::numeric_limits<unsigned>::max();
                all = true;
            } else {
                i = std::numeric_limits<unsigned>::max();
            }
            unsigned it          = end;
            unsigned num_imports = 0;
            while (it != 0 && i != 0) {
                --it;
                auto obj = m_env->get_object(it, false);
                if (is_begin_import(obj)) {
                    lean_assert(num_imports > 0);
                    num_imports--;
                    if (num_imports == 0)
                        to_display.push_back(obj);
                } else if (is_begin_builtin_import(obj)) {
                    lean_assert(num_imports > 0);
                    num_imports--;
                } else if (is_end_import(obj)) {
                    num_imports++;
                } else if (is_hidden_object(obj)) {
                    // skip
                } else if (num_imports == 0 || all) {
                    to_display.push_back(obj);
                    --i;
                }
            }
            std::reverse(to_display.begin(), to_display.end());
            for (auto obj : to_display) {
                if (is_begin_import(obj)) {
                    regular(m_io_state) << "import \"" << *get_imported_module(obj) << "\"" << endl;
                } else {
                    regular(m_io_state) << obj << endl;
                }
            }
        } else if (opt_id == g_options_kwd) {
            regular(m_io_state) << pp(m_io_state.get_options()) << endl;
        } else {
            throw parser_error("invalid Show command, expression, 'Options' or 'Environment' expected", m_last_cmd_pos);
        }
    } else if (curr() == scanner::token::StringVal) {
        std::string msg = curr_string();
        next();
        regular(m_io_state) << msg << endl;
    } else {
        expr v = m_elaborator(parse_expr()).first;
        regular(m_io_state) << v << endl;
    }
}

/** \brief Parse 'Check' expr */
void parser_imp::parse_check() {
    next();
    auto p = m_elaborator(parse_expr());
    check_no_metavar(p, "invalid expression, it still contains metavariables after elaboration");
    expr v = p.first;
    expr t = type_check(v, m_env);
    formatter fmt = m_io_state.get_formatter();
    options opts  = m_io_state.get_options();
    unsigned indent = get_pp_indent(opts);
    format r = group(format{fmt(v, opts), space(), colon(), nest(indent, compose(line(), fmt(t, opts)))});
    regular(m_io_state) << mk_pair(r, opts) << endl;
}

/** \brief Return the (optional) precedence of a user-defined operator. */
unsigned parser_imp::parse_precedence() {
    if (curr_is_nat()) {
        return parse_unsigned("invalid operator definition, precedence does not fit in a machine integer");
    } else {
        return 0;
    }
}

/** \brief Throw an error if the current token is not an identifier. If it is, move to next token. */
name parser_imp::parse_op_id() {
    return check_identifier_next("invalid operator definition, identifier expected");
}

/**
   \brief Parse prefix/postfix/infix/infixl/infixr user operator
   definitions. These definitions have the form:

   - fixity [Num] ID ':' ID
*/
void parser_imp::parse_op(fixity fx) {
    next();
    unsigned prec = parse_precedence();
    name op_id = parse_op_id();
    check_colon_next("invalid operator definition, ':' expected");
    auto name_pos = pos();
    name name_id = check_identifier_next("invalid operator definition, identifier expected");
    expr d       = get_name_ref(name_id, name_pos, false);
    switch (fx) {
    case fixity::Infix:   add_infix(m_env, m_io_state, op_id, prec, d); break;
    case fixity::Infixl:  add_infixl(m_env, m_io_state, op_id, prec, d); break;
    case fixity::Infixr:  add_infixr(m_env, m_io_state, op_id, prec, d); break;
    default: lean_unreachable(); // LCOV_EXCL_LINE
    }
}

/**
   \brief Parse notation declaration unified format

   'Notation' [Num] parts ':' ID
*/
void parser_imp::parse_notation_decl() {
    auto p = pos();
    next();
    unsigned prec = parse_precedence();
    bool first             = true;
    bool prev_placeholder  = false;
    bool first_placeholder = false;
    buffer<name> parts;
    while (true) {
        if (first) {
            if (curr_is_placeholder()) {
                prev_placeholder  = true;
                first_placeholder = true;
                next();
            } else {
                parts.push_back(check_identifier_next("invalid notation declaration, identifier or '_' expected"));
                prev_placeholder  = false;
                first_placeholder = false;
            }
            first = false;
        } else {
            if (curr_is_colon()) {
                next();
                if (parts.size() == 0) {
                    throw parser_error("invalid notation declaration, it must have at least one identifier", p);
                }
                auto id_pos = pos();
                name name_id = check_identifier_next("invalid notation declaration, identifier expected");
                expr d       = get_name_ref(name_id, id_pos, false);
                if (parts.size() == 1) {
                    if (first_placeholder && prev_placeholder) {
                        // infix: _ ID _
                        add_infix(m_env, m_io_state, parts[0], prec, d);
                    } else if (first_placeholder) {
                        // postfix: _ ID
                        add_postfix(m_env, m_io_state, parts[0], prec, d);
                    } else if (prev_placeholder) {
                        // prefix: ID _
                        add_prefix(m_env, m_io_state, parts[0], prec, d);
                    } else {
                        throw parser_error("invalid notation declaration, at least one placeholder expected", p);
                    }
                } else {
                    if (first_placeholder && prev_placeholder) {
                        // mixfixo: _ ID ... ID _
                        add_mixfixo(m_env, m_io_state, parts.size(), parts.data(), prec, d);
                    } else if (first_placeholder) {
                        // mixfixr: _ ID ... ID
                        add_mixfixr(m_env, m_io_state, parts.size(), parts.data(), prec, d);
                    } else if (prev_placeholder) {
                        // mixfixl: ID _ ... ID _
                        add_mixfixl(m_env, m_io_state, parts.size(), parts.data(), prec, d);
                    } else {
                        // mixfixc: ID _ ... _ ID
                        add_mixfixc(m_env, m_io_state, parts.size(), parts.data(), prec, d);
                    }
                }
                return;
            } else {
                if (prev_placeholder) {
                    parts.push_back(check_identifier_next("invalid notation declaration, identifier or ':' expected"));
                    prev_placeholder = false;
                } else {
                    check_placeholder_next("invalid notation declaration, '_' or ':' expected");
                    prev_placeholder = true;
                }
            }
        }
    }
}

/** Parse 'SetOption' [id] [value] */
void parser_imp::parse_set_option() {
    next();
    auto id_pos = pos();
    name id = check_identifier_next("invalid set options, identifier (i.e., option name) expected");
    auto decl_it = get_option_declarations().find(id);
    if (decl_it == get_option_declarations().end()) {
        // add "lean" prefix
        name lean_id = name("lean") + id;
        decl_it = get_option_declarations().find(lean_id);
        if (decl_it == get_option_declarations().end()) {
            throw parser_error(sstream() << "unknown option '" << id << "', type 'Help Options.' for list of available options", id_pos);
        } else {
            id = lean_id;
        }
    }
    option_kind k = decl_it->second.kind();
    switch (curr()) {
    case scanner::token::Id:
        if (k != BoolOption)
            throw parser_error(sstream() << "invalid option value, given option is not Boolean", pos());
        if (curr_name() == "true")
            m_io_state.set_option(id, true);
        else if (curr_name() == "false")
            m_io_state.set_option(id, false);
        else
            throw parser_error("invalid Boolean option value, 'true' or 'false' expected", pos());
        next();
        break;
    case scanner::token::StringVal:
        if (k != StringOption)
            throw parser_error("invalid option value, given option is not a string", pos());
        m_io_state.set_option(id, curr_string());
        next();
        break;
    case scanner::token::IntVal:
        if (k != IntOption && k != UnsignedOption)
            throw parser_error("invalid option value, given option is not an integer", pos());
        m_io_state.set_option(id, parse_unsigned("invalid option value, value does not fit in a machine integer"));
        break;
    case scanner::token::DecimalVal:
        if (k != DoubleOption)
            throw parser_error("invalid option value, given option is not floating point value", pos());
        m_io_state.set_option(id, parse_double());
        break;
    default:
        throw parser_error("invalid option value, 'true', 'false', string, integer or decimal value expected", pos());
    }
    updt_options();
    if (m_verbose)
        regular(m_io_state) << "  Set: " << id << endl;
}

/** Parse 'SetOpaque' [id] [true/false] */
void parser_imp::parse_set_opaque() {
    next();
    name id;
    if (curr() == scanner::token::Forall) {
        id = "forall";
    } else if (curr() == scanner::token::Exists) {
        id = "exists";
    } else {
        check_identifier("invalid set opaque, identifier expected");
        id = curr_name();
    }
    next();
    name full_id = mk_full_name(id);
    auto val_pos = pos();
    name val = check_identifier_next("invalid opaque flag, true/false expected");
    if (val == "true")
        m_env->set_opaque(full_id, true);
    else if (val == "false")
        m_env->set_opaque(full_id, false);
    else
        throw parser_error("invalid opaque flag, true/false expected", val_pos);
}

optional<std::string> parser_imp::find_lua_file(std::string const & fname) {
    try {
        return some(find_file(fname, {".lua"}));
    } catch (...) {
        return optional<std::string>();
    }
}

void parser_imp::parse_import() {
    next();
    std::string fname;
    if (curr_is_identifier()) {
        fname = name_to_file(curr_name());
        next();
    } else {
        fname  = check_string_next("invalid import command, string (i.e., file name) or identifier expected");
    }
    bool r = false;
    if (auto lua_fname = find_lua_file(fname)) {
        if (!m_script_state)
            throw parser_error(sstream() << "failed to import Lua file '" << *lua_fname << "', parser does not have an intepreter",
                               m_last_cmd_pos);
        r = m_script_state->import_explicit(lua_fname->c_str());
    } else {
        r = m_env->import(fname, m_io_state);
    }
    if (m_verbose && r) {
        regular(m_io_state) << "  Imported '" << fname << "'" << endl;
    }
}

void parser_imp::parse_help() {
    next();
    if (curr() == scanner::token::CommandId) {
        name opt_id = curr_name();
        next();
        if (opt_id == g_options_kwd) {
            regular(m_io_state) << "Available options:" << endl;
            for (auto p : get_option_declarations()) {
                auto opt = p.second;
                regular(m_io_state) << "  " << opt.get_name() << " (" << opt.kind() << ") "
                                    << opt.get_description() << " (default: " << opt.get_default_value() << ")" << endl;
            }
        } else {
            throw parser_error("invalid help command", m_last_cmd_pos);
        }
    } else {
        regular(m_io_state) << "Available commands:" << endl
                            << "  alias [id] : [expr]      define an alias for the given expression" << endl
                            << "  axiom [id] : [type]      assert/postulate a new axiom" << endl
                            << "  check [expr]             type check the given expression" << endl
                            << "  definition [id] : [type] := [expr]   define a new element" << endl
                            << "  end                      end the current scope/namespace" << endl
                            << "  eval [expr]              evaluate the given expression" << endl
                            << "  exit                     exit" << endl
                            << "  help                     display this message" << endl
                            << "  help options             display available options" << endl
                            << "  help notation            describe commands for defining infix, mixfix, postfix operators" << endl
                            << "  import [string]          load the given file" << endl
                            << "  pop::scope               discard the current scope" << endl
                            << "  print [expr]             pretty print the given expression" << endl
                            << "  print Options            print current the set of assigned options" << endl
                            << "  print [string]           print the given string" << endl
                            << "  print Environment        print objects in the environment, if [Num] provided, then show only the last [Num] objects" << endl
                            << "  print Environment [num]  show the last num objects in the environment" << endl
                            << "  scope                    create a scope" << endl
                            << "  set::option [id] [value] set option [id] with value [value]" << endl
                            << "  set::opaque [id] [bool]  set the given definition as opaque/transparent" << endl
                            << "  theorem [id] : [type] := [expr]    define a new theorem" << endl
                            << "  variable [id] : [type]   declare/postulate an element of the given type" << endl
                            << "  universe [id] >= [level] declare a new universe constraint" << endl
                            << "  using [id]_1 [id]_2?     create an alias for object starting with the prefix [id]_1 using the [id]_2" << endl;
#if !defined(LEAN_WINDOWS)
        regular(m_io_state) << "Type Ctrl-D to exit" << endl;
#endif
}
}

/** \brief Parse 'Coercion' expr */
void parser_imp::parse_coercion() {
    next();
    expr coercion = parse_expr();
    add_coercion(m_env, coercion);
    if (m_verbose)
        regular(m_io_state) << "  Coercion " << coercion << endl;
}

void parser_imp::reset_env(environment env) {
    m_env = env;
    m_elaborator.reset(env);
    m_io_state.set_formatter(mk_pp_formatter(env));
}

void parser_imp::parse_cmd_macro(name cmd_id, pos_info const & p) {
    lean_assert(m_cmd_macros && m_cmd_macros->find(cmd_id) != m_cmd_macros->end());
    next();
    auto m = m_cmd_macros->find(cmd_id)->second;
    macro_arg_stack args;
    parse_macro(m.m_arg_kinds, m.m_fn, m.m_precedence, args, p);
}

static name g_geq_unicode("\u2265"); // ≥
static name g_geq(">=");

void parser_imp::parse_universe() {
    next();
    name id   = check_identifier_next("invalid universe constraint, identifier expected");
    if (curr_is_identifier()) {
        name geq  = check_identifier_next("invalid universe constraint, '>=' expected");
        if (geq != g_geq && geq != g_geq_unicode)
            throw parser_error("invalid universe constraint, '>=' expected", m_last_cmd_pos);
        level lvl = parse_level();
        m_env->add_uvar_cnstr(id, lvl);
    } else {
        m_env->add_uvar_cnstr(id);
    }
}

void parser_imp::parse_alias() {
    next();
    name id   = check_identifier_next("invalid alias declaration, identifier expected");
    check_colon_next("invalid alias declaration, ':' expected");
    expr e    = parse_expr();
    add_alias(m_env, id, e);
}

void parser_imp::parse_builtin() {
    next();
    auto id_pos = pos();
    name id = check_identifier_next("invalid builtin declaration, identifier expected");
    name full_id = mk_full_name(id);
    auto d  = get_builtin(full_id);
    if (!d)
        throw parser_error(sstream() << "unknown builtin '" << full_id << "'", id_pos);
    expr b = d->first;
    if (d->second) {
        m_env->add_builtin_set(b);
        return;
    }
    parameter_buffer parameters;
    expr type;
    if (curr_is_colon()) {
        next();
        auto p = m_elaborator(parse_expr());
        check_no_metavar(p, "invalid builtin declaration, type still contains metavariables after elaboration");
        type = p.first;
    } else {
        mk_scope scope(*this);
        parse_var_decl_parameters(parameters);
        check_colon_next("invalid builtin declaration, ':' expected");
        expr type_body = parse_expr();
        auto p = m_elaborator(mk_abstraction(false, parameters, type_body));
        check_no_metavar(p, "invalid declaration, type still contains metavariables after elaboration");
        type = p.first;
    }
    if (to_value(b).get_type() != type) {
        diagnostic(m_io_state) << "Error, builtin expected type: " << to_value(b).get_type() << ", given: " << type << "\n";
        throw parser_error(sstream() << "given type does not match builtin type", id_pos);
    }
    m_env->add_builtin(d->first);
    if (m_verbose)
        regular(m_io_state) << "  Added: " << full_id << endl;
    register_implicit_arguments(full_id, parameters);
}

void parser_imp::parse_scope() {
    next();
    m_scope_kinds.push_back(scope_kind::Scope);
    reset_env(m_env->mk_child());
    m_using_decls.push();
}

void parser_imp::parse_pop() {
    next();
    if (m_scope_kinds.empty())
        throw parser_error("main scope cannot be removed", m_last_cmd_pos);
    if (m_scope_kinds.back() != scope_kind::Scope)
        throw parser_error("invalid pop command, it is not inside of a scope", m_last_cmd_pos);
    if (!m_env->has_parent())
        throw parser_error("main scope cannot be removed", m_last_cmd_pos);
    m_scope_kinds.pop_back();
    reset_env(m_env->parent());
    m_using_decls.pop();
    m_script_state->apply([&](lua_State * L) { lua_gc(L, LUA_GCCOLLECT, 0); });
}

void parser_imp::parse_namespace() {
    next();
    name id   = check_identifier_next("invalid namespace declaration, identifier expected");
    m_scope_kinds.push_back(scope_kind::Namespace);
    m_namespace_prefixes.push_back(m_namespace_prefixes.back() + id);
    m_using_decls.push();
}

void parser_imp::parse_end() {
    next();
    if (m_scope_kinds.empty())
        throw parser_error("invalid 'end', not inside of a scope or namespace", m_last_cmd_pos);
    scope_kind k = m_scope_kinds.back();
    m_scope_kinds.pop_back();
    m_script_state->apply([&](lua_State * L) { lua_gc(L, LUA_GCCOLLECT, 0); });
    switch (k) {
    case scope_kind::Scope: {
        if (!m_env->has_parent())
            throw parser_error("main scope cannot be removed", m_last_cmd_pos);
        auto new_objects = export_local_objects(m_env);
        reset_env(m_env->parent());
        for (auto const & obj : new_objects) {
            if (obj.is_theorem())
                m_env->add_theorem(obj.get_name(), obj.get_type(), obj.get_value());
            else
                m_env->add_definition(obj.get_name(), obj.get_type(), obj.get_value(), obj.is_opaque());
        }
        break;
    }
    case scope_kind::Namespace:
        if (m_namespace_prefixes.size() <= 1)
            throw parser_error("invalid end namespace command, there are no open namespaces", m_last_cmd_pos);
        m_namespace_prefixes.pop_back();
    }
    m_using_decls.pop();
}

static name replace_prefix(name const & n, name const & prefix, name const & new_prefix) {
    if (n == prefix)
        return new_prefix;
    name p = replace_prefix(n.get_prefix(), prefix, new_prefix);
    if (n.is_string())
        return name(p, n.get_string());
    else
        return name(p, n.get_numeral());
}

void parser_imp::parse_using() {
    next();
    name prefix = check_identifier_next("invalid using command, identifier expected");
    name new_prefix;
    if (curr_is_identifier()) {
        new_prefix = curr_name();
        next();
    }
    buffer<std::pair<name, expr>> to_add;
    for (auto it = m_env->begin_objects(); it != m_env->end_objects(); ++it) {
        if (it->has_type() && it->has_name() && !is_hidden_object(*it) && is_prefix_of(prefix, it->get_name())) {
            auto n = replace_prefix(it->get_name(), prefix, new_prefix);
            if (!n.is_anonymous())
                to_add.emplace_back(n, mk_constant(it->get_name()));
        }
    }
    for (auto p : to_add) {
        auto n  = p.first;
        if (m_verbose) {
            auto it = m_using_decls.find(n);
            if (it != m_using_decls.end())
                diagnostic(m_io_state) << "warning: " << n << " will shadow " << it->second << endl;
            auto obj = m_env->find_object(n);
            if (obj)
                diagnostic(m_io_state) << "warning: " << n << " will shadow " << obj->get_name() << endl;
        }
        m_using_decls.insert(n, p.second);
    }
    if (m_verbose)
        regular(m_io_state) << "  Using: " << prefix;
    if (new_prefix)
        regular(m_io_state) << " as " << new_prefix;
    regular(m_io_state) << endl;
}

/** \brief Parse a Lean command. */
bool parser_imp::parse_command() {
    m_elaborator.clear();
    m_expr_pos_info.clear();
    m_tactic_hints.clear();
    m_last_cmd_pos = pos();
    name const & cmd_id = curr_name();
    if (cmd_id == g_definition_kwd) {
        parse_definition();
    } else if (cmd_id == g_variable_kwd) {
        parse_variable();
    } else if (cmd_id == g_variables_kwd) {
        parse_variables();
    } else if (cmd_id == g_theorem_kwd) {
        parse_theorem();
    } else if (cmd_id == g_axiom_kwd) {
        parse_axiom();
    } else if (cmd_id == g_eval_kwd) {
        parse_eval();
    } else if (cmd_id == g_print_kwd) {
        parse_print();
    } else if (cmd_id == g_check_kwd) {
        parse_check();
    } else if (cmd_id == g_infix_kwd) {
        parse_op(fixity::Infix);
    } else if (cmd_id == g_infixl_kwd) {
        parse_op(fixity::Infixl);
    } else if (cmd_id == g_infixr_kwd) {
        parse_op(fixity::Infixr);
    } else if (cmd_id == g_notation_kwd) {
        parse_notation_decl();
    } else if (cmd_id == g_set_option_kwd) {
        parse_set_option();
    } else if (cmd_id == g_set_opaque_kwd) {
        parse_set_opaque();
    } else if (cmd_id == g_import_kwd) {
        parse_import();
    } else if (cmd_id == g_help_kwd) {
        parse_help();
    } else if (cmd_id == g_coercion_kwd) {
        parse_coercion();
    } else if (cmd_id == g_exit_kwd) {
        next();
        return false;
    } else if (cmd_id == g_scope_kwd) {
        parse_scope();
    } else if (cmd_id == g_pop_kwd) {
        parse_pop();
    } else if (cmd_id == g_universe_kwd) {
        parse_universe();
    } else if (cmd_id == g_alias_kwd) {
        parse_alias();
    } else if (cmd_id == g_builtin_kwd) {
        parse_builtin();
    } else if (cmd_id == g_namespace_kwd) {
        parse_namespace();
    } else if (cmd_id == g_end_kwd) {
        parse_end();
    } else if (cmd_id == g_using_kwd) {
        parse_using();
    } else if (m_cmd_macros && m_cmd_macros->find(cmd_id) != m_cmd_macros->end()) {
        parse_cmd_macro(cmd_id, m_last_cmd_pos);
    } else {
        next();
        throw parser_error(sstream() << "invalid command '" << cmd_id << "'", m_last_cmd_pos);
    }
    return true;
}
}
