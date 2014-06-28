/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include <limits>
#include <vector>
#include "util/interrupt.h"
#include "util/script_exception.h"
#include "util/sstream.h"
#include "util/flet.h"
#include "util/lean_path.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/parser_nested_exception.h"
#include "library/aliases.h"
#include "library/private.h"
#include "library/choice.h"
#include "library/placeholder.h"
#include "library/deep_copy.h"
#include "library/module.h"
#include "library/scoped_ext.h"
#include "library/error_handling/error_handling.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/notation_cmd.h"
#include "frontends/lean/elaborator.h"

#ifndef LEAN_DEFAULT_PARSER_SHOW_ERRORS
#define LEAN_DEFAULT_PARSER_SHOW_ERRORS true
#endif

namespace lean {
// ==========================================
// Parser configuration options
static name g_parser_show_errors {"lean", "parser", "show_errors"};

RegisterBoolOption(g_parser_show_errors, LEAN_DEFAULT_PARSER_SHOW_ERRORS, "(lean parser) display error messages in the regular output channel");

bool     get_parser_show_errors(options const & opts)  { return opts.get_bool(g_parser_show_errors, LEAN_DEFAULT_PARSER_SHOW_ERRORS); }
// ==========================================

parser::local_scope::local_scope(parser & p):
    m_p(p), m_env(p.env()) {
    p.push_local_scope();
}
parser::local_scope::~local_scope() {
    m_p.pop_local_scope();
    m_p.m_env = m_env;
}

parser::param_universe_scope::param_universe_scope(parser & p):m_p(p), m_old(m_p.m_type_use_placeholder) {
    m_p.m_type_use_placeholder = false;
}
parser::param_universe_scope::~param_universe_scope() {
    m_p.m_type_use_placeholder = m_old;
}

parser::placeholder_universe_scope::placeholder_universe_scope(parser & p):m_p(p), m_old(m_p.m_type_use_placeholder) {
    m_p.m_type_use_placeholder = true;
}
parser::placeholder_universe_scope::~placeholder_universe_scope() {
    m_p.m_type_use_placeholder = m_old;
}

parser::no_undef_id_error_scope::no_undef_id_error_scope(parser & p):m_p(p), m_old(m_p.m_no_undef_id_error) {
    m_p.m_no_undef_id_error = true;
}
parser::no_undef_id_error_scope::~no_undef_id_error_scope() {
    m_p.m_no_undef_id_error = m_old;
}

static char g_parser_key;
void set_global_parser(lua_State * L, parser * p) {
    lua_pushlightuserdata(L, static_cast<void *>(&g_parser_key));
    lua_pushlightuserdata(L, static_cast<void *>(p));
    lua_settable(L, LUA_REGISTRYINDEX);
}

parser * get_global_parser_ptr(lua_State * L) {
    lua_pushlightuserdata(L, static_cast<void *>(&g_parser_key));
    lua_gettable(L, LUA_REGISTRYINDEX);
    if (!lua_islightuserdata(L, -1))
        return nullptr;
    parser * p = static_cast<parser*>(const_cast<void*>(lua_topointer(L, -1)));
    lua_pop(L, 1);
    return p;
}

parser & get_global_parser(lua_State * L) {
    parser * p = get_global_parser_ptr(L);
    if (p == nullptr)
        throw exception("there is no Lean parser on the Lua stack");
    return *p;
}

struct scoped_set_parser {
    lua_State * m_state;
    parser *    m_old;
    scoped_set_parser(lua_State * L, parser & p):m_state(L) {
        m_old = get_global_parser_ptr(L);
        set_global_parser(L, &p);
    }
    ~scoped_set_parser() {
        set_global_parser(m_state, m_old);
    }
};

static name g_tmp_prefix = name::mk_internal_unique_name();

parser::parser(environment const & env, io_state const & ios,
               std::istream & strm, char const * strm_name,
               bool use_exceptions, unsigned num_threads,
               local_level_decls const & lds, local_expr_decls const & eds,
               unsigned line):
    m_env(env), m_ios(ios), m_ngen(g_tmp_prefix),
    m_verbose(true), m_use_exceptions(use_exceptions),
    m_scanner(strm, strm_name), m_local_level_decls(lds), m_local_decls(eds),
    m_pos_table(std::make_shared<pos_info_table>()) {
    m_scanner.set_line(line);
    m_num_threads = num_threads;
    m_type_use_placeholder = true;
    m_no_undef_id_error    = false;
    m_found_errors = false;
    updt_options();
    m_next_tag_idx = 0;
    m_curr = scanner::token_kind::Identifier;
    protected_call([&]() { scan(); },
                   [&]() { sync_command(); });
}

void parser::updt_options() {
    m_verbose = get_verbose(m_ios.get_options());
    m_show_errors = get_parser_show_errors(m_ios.get_options());
}

void parser::display_error_pos(unsigned line, unsigned pos) {
    regular_stream() << get_stream_name() << ":" << line << ":";
    if (pos != static_cast<unsigned>(-1))
        regular_stream() << pos << ":";
    regular_stream() << " error:";
}
void parser::display_error_pos(pos_info p) { display_error_pos(p.first, p.second); }

void parser::display_error(char const * msg, unsigned line, unsigned pos) {
    display_error_pos(line, pos);
    regular_stream() << " " << msg << endl;
}

void parser::display_error(char const * msg, pos_info p) {
    display_error(msg, p.first, p.second);
}

void parser::display_error(exception const & ex) {
    parser_pos_provider pos_provider(m_pos_table, get_stream_name(), m_last_cmd_pos);
    ::lean::display_error(regular_stream(), &pos_provider, ex);
}

void parser::throw_parser_exception(char const * msg, pos_info p) {
    throw parser_exception(msg, get_stream_name().c_str(), p.first, p.second);
}

void parser::throw_nested_exception(exception & ex, pos_info p) {
    throw parser_nested_exception(std::shared_ptr<exception>(ex.clone()),
                                  std::make_shared<parser_pos_provider>(m_pos_table, get_stream_name(), p));
}

#define CATCH(ShowError, ThrowError)                    \
m_found_errors = true;                                  \
if (!m_use_exceptions && m_show_errors) { ShowError ; } \
sync();                                                 \
if (m_use_exceptions) { ThrowError ; }

void parser::protected_call(std::function<void()> && f, std::function<void()> && sync) {
    try {
        f();
    // } catch (tactic_cmd_error & ex) {
    //     CATCH(display_error(ex),
    //           throw parser_exception(ex.what(), m_strm_name.c_str(), ex.m_pos.first, ex.m_pos.second));
    } catch (parser_exception & ex) {
        CATCH(regular_stream() << ex.what() << endl,
              throw);
    } catch (parser_error & ex) {
        CATCH(display_error(ex.what(), ex.m_pos),
              throw_parser_exception(ex.what(), ex.m_pos));
    } catch (interrupted & ex) {
        reset_interrupt();
        if (m_verbose)
            regular_stream() << "!!!Interrupted!!!" << endl;
        sync();
        if (m_use_exceptions)
            throw;
    } catch (script_exception & ex) {
        reset_interrupt();
        CATCH(display_error(ex), throw_nested_exception(ex, m_last_script_pos));
    } catch (exception & ex) {
        reset_interrupt();
        CATCH(display_error(ex), throw_nested_exception(ex, m_last_cmd_pos));
    }
}

void parser::sync_command() {
    // Keep consuming tokens until we find a Command or End-of-file
    while (curr() != scanner::token_kind::CommandKeyword && curr() != scanner::token_kind::Eof)
        next();
}

tag parser::get_tag(expr e) {
    tag t = e.get_tag();
    if (t == nulltag) {
        t = m_next_tag_idx;
        e.set_tag(t);
        m_next_tag_idx++;
    }
    return t;
}

expr parser::save_pos(expr e, pos_info p) {
    m_pos_table->insert(mk_pair(get_tag(e), p));
    return e;
}

expr parser::rec_save_pos(expr const & e, pos_info p) {
    unsigned m = std::numeric_limits<unsigned>::max();
    pos_info dummy(m, 0);
    for_each(e, [&](expr const & e, unsigned) {
            if (pos_of(e, dummy).first == m) {
                save_pos(e, p);
                return true;
            }  else {
                return false;
            }
        });
    return e;
}

/** \brief Create a copy of \c e, and the position of new expression with p */
expr parser::copy_with_new_pos(expr const & e, pos_info p) {
    switch (e.kind()) {
    case expr_kind::Sort: case expr_kind::Constant: case expr_kind::Meta:
    case expr_kind::Local: case expr_kind::Var:
        return save_pos(copy(e), p);
    case expr_kind::App:
        return save_pos(::lean::mk_app(copy_with_new_pos(app_fn(e), p),
                                       copy_with_new_pos(app_arg(e), p)),
                        p);
    case expr_kind::Lambda: case expr_kind::Pi:
        return save_pos(update_binding(e,
                                       copy_with_new_pos(binding_domain(e), p),
                                       copy_with_new_pos(binding_body(e), p)),
                        p);
    case expr_kind::Macro: {
        buffer<expr> args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            args.push_back(copy_with_new_pos(macro_arg(e, i), p));
        return save_pos(update_macro(e, args.size(), args.data()), p);
    }}
    lean_unreachable(); // LCOV_EXCL_LINE
}

/** \brief Add \c ls to constants occurring in \c e. */
expr parser::propagate_levels(expr const & e, levels const & ls) {
    if (is_nil(ls)) {
        return e;
    } else {
        return replace(e, [&](expr const & e, unsigned) {
                if (is_constant(e)) {
                    auto it = m_env.find(const_name(e));
                    if (it) {
                        level_param_names const & univ_ps = it->get_univ_params();
                        levels const & old_ls = const_levels(e);
                        if (length(old_ls) + length(ls) <= length(univ_ps))
                            return some_expr(update_constant(e, append(old_ls, ls)));
                    }
                }
                return none_expr();
            });
    }
}

pos_info parser::pos_of(expr const & e, pos_info default_pos) {
    auto it = m_pos_table->find(get_tag(e));
    if (it == m_pos_table->end())
        return default_pos;
    else
        return it->second;
}

bool parser::curr_is_token(name const & tk) const {
    return
        (curr() == scanner::token_kind::Keyword || curr() == scanner::token_kind::CommandKeyword) &&
        get_token_info().value() == tk;
}

bool parser::curr_is_token_or_id(name const & tk) const {
    if (curr() == scanner::token_kind::Keyword || curr() == scanner::token_kind::CommandKeyword)
        return get_token_info().value() == tk;
    else if (curr() == scanner::token_kind::Identifier)
        return get_name_val() == tk;
    else
        return false;
}

void parser::check_token_next(name const & tk, char const * msg) {
    if (!curr_is_token(tk))
        throw parser_error(msg, pos());
    next();
}

name parser::check_id_next(char const * msg) {
    if (!curr_is_identifier())
        throw parser_error(msg, pos());
    name r = get_name_val();
    next();
    return r;
}

expr parser::mk_app(expr fn, expr arg, pos_info const & p) {
    return save_pos(::lean::mk_app(fn, arg), p);
}

expr parser::mk_app(std::initializer_list<expr> const & args, pos_info const & p) {
    lean_assert(args.size() >= 2);
    auto it = args.begin();
    expr r = *it;
    it++;
    for (; it != args.end(); it++)
        r = mk_app(r, *it, p);
    return r;
}

void parser::push_local_scope() {
    if (m_type_use_placeholder)
        m_local_level_decls.push();
    m_local_decls.push();
}

void parser::pop_local_scope() {
    if (m_type_use_placeholder)
        m_local_level_decls.pop();
    m_local_decls.pop();
}

void parser::add_local_level(name const & n, level const & l) {
    if (m_env.is_universe(n))
        throw exception(sstream() << "invalid universe declaration, '" << n << "' shadows a global universe");
    if (m_local_level_decls.contains(n))
        throw exception(sstream() << "invalid universe declaration, '" << n << "' shadows a local universe");
    m_local_level_decls.insert(n, l);
}

void parser::add_local_expr(name const & n, parameter const & p) {
    m_local_decls.insert(n, p);
}

void parser::add_local_expr(name const & n, expr const & e, binder_info const & bi) {
    add_local_expr(n, parameter(e, bi));
}

void parser::add_local(expr const & e, binder_info const & bi) {
    lean_assert(is_local(e));
    add_local_expr(local_pp_name(e), e, bi);
}

unsigned parser::get_local_level_index(name const & n) const {
    return m_local_level_decls.find_idx(n);
}

unsigned parser::get_local_index(name const & n) const {
    return m_local_decls.find_idx(n);
}

optional<parameter> parser::get_local(name const & n) const {
    if (auto it = m_local_decls.find(n))
        return optional<parameter>(*it);
    else
        return optional<parameter>();
}

/** \brief Parse a sequence of identifiers <tt>ID*</tt>. Store the result in \c result. */
void parser::parse_names(buffer<std::pair<pos_info, name>> & result) {
    while (curr_is_identifier()) {
        result.emplace_back(pos(), get_name_val());
        next();
    }
}

static name g_period(".");
static name g_colon(":");
static name g_lparen("(");
static name g_rparen(")");
static name g_llevel_curly(".{");
static name g_lcurly("{");
static name g_rcurly("}");
static name g_ldcurly("⦃");
static name g_rdcurly("⦄");
static name g_lbracket("[");
static name g_rbracket("]");
static name g_add("+");
static name g_max("max");
static name g_imax("imax");
static name g_cup("\u2294");
static name g_import("import");
static unsigned g_level_add_prec = 10;
static unsigned g_level_cup_prec = 5;

unsigned parser::get_small_nat() {
    mpz val = get_num_val().get_numerator();
    lean_assert(val >= 0);
    if (!val.is_unsigned_int())
        throw parser_error("invalid level expression, value does not fit in a machine integer", pos());
    return val.get_unsigned_int();
}

unsigned parser::parse_small_nat() {
    if (!curr_is_numeral())
        throw parser_error("(small) natural number expected", pos());
    unsigned r = get_small_nat();
    next();
    return r;
}

double parser::parse_double() {
    if (curr() != scanner::token_kind::Decimal)
        throw parser_error("decimal value expected", pos());
    return get_num_val().get_double();
}

static level lift(level l, unsigned k) {
    while (k > 0) {
        k--;
        l = mk_succ(l);
    }
    return l;
}

unsigned parser::curr_level_lbp() const {
    if (curr_is_token(g_cup))
        return g_level_cup_prec;
    else if (curr_is_token(g_add))
        return g_level_add_prec;
    else
        return 0;
}

level parser::parse_max_imax(bool is_max) {
    auto p = pos();
    next();
    buffer<level> lvls;
    while (curr_is_identifier() || curr_is_numeral() || curr_is_token(g_lparen)) {
        lvls.push_back(parse_level());
    }
    if (lvls.size() < 2)
        throw parser_error("invalid level expression, max must have at least two arguments", p);
    unsigned i = lvls.size() - 1;
    level r = lvls[i];
    while (i > 0) {
        --i;
        if (is_max)
            r = mk_max(lvls[i], r);
        else
            r = mk_imax(lvls[i], r);
    }
    return r;
}

level parser::parse_level_id() {
    auto p  = pos();
    name id = get_name_val();
    next();
    if (auto it = m_local_level_decls.find(id))
        return *it;
    if (m_env.is_universe(id))
        return mk_global_univ(id);
    if (auto it = get_alias_level(m_env, id))
        return *it;
    throw parser_error(sstream() << "unknown universe '" << id << "'", p);
}

level parser::parse_level_nud() {
    if (curr_is_token_or_id(g_max)) {
        return parse_max_imax(true);
    } else if (curr_is_token_or_id(g_imax)) {
        return parse_max_imax(false);
    } else if (curr_is_token(g_lparen)) {
        next();
        level l = parse_level();
        check_token_next(g_rparen, "invalid level expression, ')' expected");
        return l;
    } else if (curr_is_numeral()) {
        unsigned k = parse_small_nat();
        return lift(level(), k);
    } else if (curr_is_identifier()) {
        return parse_level_id();
    } else {
        throw parser_error("invalid level expression", pos());
    }
}

level parser::parse_level_led(level left) {
    auto p = pos();
    if (curr_is_token(g_cup)) {
        next();
        level right = parse_level(g_level_cup_prec);
        return mk_max(left, right);
    } else if (curr_is_token(g_add)) {
        next();
        if (curr_is_numeral()) {
            unsigned k = parse_small_nat();
            return lift(left, k);
        } else {
            throw parser_error("invalid level expression, right hand side of '+' (aka universe lift operator) must be a numeral", p);
        }
    } else {
        throw parser_error("invalid level expression", p);
    }
}

level parser::parse_level(unsigned rbp) {
    level left = parse_level_nud();
    while (rbp < curr_level_lbp()) {
        left = parse_level_led(left);
    }
    return left;
}

expr parser::mk_Type() {
    if (m_type_use_placeholder) {
        return mk_sort(mk_level_placeholder());
    } else {
        unsigned i = 1;
        name l("l");
        name r = l.append_after(i);
        while (m_local_level_decls.contains(r) || m_env.is_universe(r)) {
            i++;
            r = l.append_after(i);
        }
        level lvl = mk_param_univ(r);
        add_local_level(r, lvl);
        return mk_sort(lvl);
    }
}

expr parser::elaborate(expr const & e) {
    return ::lean::elaborate(m_env, m_ios, e);
}

expr parser::elaborate(environment const & env, expr const & e) {
    return ::lean::elaborate(env, m_ios, e);
}

std::pair<expr, expr> parser::elaborate(name const & n, expr const & t, expr const & v) {
    return ::lean::elaborate(m_env, m_ios, n, t, v);
}

/** \brief Parse <tt>ID ':' expr</tt>, where the expression represents the type of the identifier. */
parameter parser::parse_binder_core(binder_info const & bi) {
    auto p  = pos();
    if (!curr_is_identifier())
        throw parser_error("invalid binder, identifier expected", p);
    name id = get_name_val();
    next();
    expr type;
    if (curr_is_token(g_colon)) {
        next();
        type = parse_expr();
    } else {
        type = save_pos(mk_expr_placeholder(), p);
    }
    return parameter(save_pos(mk_local(id, type), p), bi);
}

parameter parser::parse_binder() {
    if (curr_is_identifier()) {
        return parse_binder_core(binder_info());
    } else if (curr_is_token(g_lparen)) {
        next();
        auto p = parse_binder_core(binder_info());
        check_token_next(g_rparen, "invalid binder, ')' expected");
        return p;
    } else if (curr_is_token(g_lcurly)) {
        next();
        if (curr_is_token(g_lcurly)) {
            next();
            auto p = parse_binder_core(mk_strict_implicit_binder_info());
            check_token_next(g_rcurly, "invalid binder, '}' expected");
            check_token_next(g_rcurly, "invalid binder, '}' expected");
            return p;
        } else {
            auto p = parse_binder_core(mk_implicit_binder_info());
            check_token_next(g_rcurly, "invalid binder, '}' expected");
            return p;
        }
    } else if (curr_is_token(g_lbracket)) {
        next();
        auto p = parse_binder_core(mk_cast_binder_info());
        check_token_next(g_rbracket, "invalid binder, ']' expected");
        return p;
    } else if (curr_is_token(g_ldcurly)) {
        next();
        auto p = parse_binder_core(mk_strict_implicit_binder_info());
        check_token_next(g_rdcurly, "invalid binder, '⦄' expected");
        return p;
    } else {
        throw parser_error("invalid binder, '(', '{', '[', '{{', '⦃' or identifier expected", pos());
    }
}

/**
   \brief Parse <tt>ID ... ID ':' expr</tt>, where the expression
   represents the type of the identifiers.
*/
void parser::parse_binder_block(buffer<parameter> & r, binder_info const & bi) {
    buffer<std::pair<pos_info, name>> names;
    parse_names(names);
    if (names.empty())
        throw parser_error("invalid binder, identifier expected", pos());
    optional<expr> type;
    if (curr_is_token(g_colon)) {
        next();
        type = parse_expr();
    }
    for (auto p : names) {
        expr arg_type = type ? *type : save_pos(mk_expr_placeholder(), p.first);
        expr local = save_pos(mk_local(p.second, arg_type), p.first);
        add_local_expr(p.second, parameter(local, bi));
        r.push_back(parameter(local, bi));
    }
}

void parser::parse_binders_core(buffer<parameter> & r) {
    if (curr_is_identifier()) {
        parse_binder_block(r, binder_info());
    } else if (curr_is_token(g_lparen)) {
        next();
        if (!parse_local_notation_decl())
            parse_binder_block(r, binder_info());
        check_token_next(g_rparen, "invalid binder, ')' expected");
    } else if (curr_is_token(g_lcurly)) {
        next();
        if (curr_is_token(g_lcurly)) {
            next();
            parse_binder_block(r, mk_strict_implicit_binder_info());
            check_token_next(g_rcurly, "invalid binder, '}' expected");
            check_token_next(g_rcurly, "invalid binder, '}' expected");
        } else {
            parse_binder_block(r, mk_implicit_binder_info());
            check_token_next(g_rcurly, "invalid binder, '}' expected");
        }
    } else if (curr_is_token(g_lbracket)) {
        next();
        parse_binder_block(r, mk_cast_binder_info());
        check_token_next(g_rbracket, "invalid binder, ']' expected");
    } else if (curr_is_token(g_ldcurly)) {
        next();
        parse_binder_block(r, mk_strict_implicit_binder_info());
        check_token_next(g_rdcurly, "invalid binder, '⦄' expected");
    } else {
        return;
    }
    parse_binders_core(r);
}

local_environment parser::parse_binders(buffer<parameter> & r) {
    flet<environment> save(m_env, m_env); // save environment
    local_expr_decls::mk_scope scope(m_local_decls);
    unsigned old_sz = r.size();
    parse_binders_core(r);
    if (old_sz == r.size())
        throw parser_error("invalid binder, '(', '{', '[', '{{', '⦃' or identifier expected", pos());
    return local_environment(m_env);
}

bool parser::parse_local_notation_decl() {
    if (curr_is_notation_decl(*this)) {
        buffer<token_entry> new_tokens;
        auto ne = ::lean::parse_notation(*this, false, new_tokens);
        for (auto const & te : new_tokens)
            m_env = add_token(m_env, te);
        m_env = add_notation(m_env, ne);
        return true;
    } else {
        return false;
    }
}

expr parser::parse_notation(parse_table t, expr * left) {
    lean_assert(curr() == scanner::token_kind::Keyword);
    auto p = pos();
    buffer<expr>      args;
    buffer<parameter> ps;
    local_environment lenv(m_env);
    pos_info binder_pos;
    if (left)
        args.push_back(*left);
    while (true) {
        if (curr() != scanner::token_kind::Keyword)
            break;
        auto r = t.find(get_token_info().value());
        if (!r)
            break;
        next();
        notation::action const & a = r->first;
        switch (a.kind()) {
        case notation::action_kind::Skip:
            break;
        case notation::action_kind::Expr:
            args.push_back(parse_expr(a.rbp()));
            break;
        case notation::action_kind::Exprs: {
            buffer<expr> r_args;
            r_args.push_back(parse_expr(a.rbp()));
            while (curr_is_token(a.get_sep())) {
                next();
                r_args.push_back(parse_expr(a.rbp()));
            }
            expr r = instantiate_rev(a.get_initial(), args.size(), args.data());
            if (a.is_fold_right()) {
                unsigned i = r_args.size();
                while (i > 0) {
                    --i;
                    args.push_back(r_args[i]);
                    args.push_back(r);
                    r = instantiate_rev(a.get_rec(), args.size(), args.data());
                    args.pop_back(); args.pop_back();
                }
            } else {
                for (unsigned i = 0; i < r_args.size(); i++) {
                    args.push_back(r_args[i]);
                    args.push_back(r);
                    r = instantiate_rev(a.get_rec(), args.size(), args.data());
                    args.pop_back(); args.pop_back();
                }
            }
            args.push_back(r);
            break;
        }
        case notation::action_kind::Binder:
            binder_pos = pos();
            ps.push_back(parse_binder());
            break;
        case notation::action_kind::Binders:
            binder_pos = pos();
            lenv = parse_binders(ps);
            break;
        case notation::action_kind::ScopedExpr: {
            expr r = parse_scoped_expr(ps, lenv, a.rbp());
            if (is_var(a.get_rec(), 0)) {
                r = abstract(ps, r, a.use_lambda_abstraction(), binder_pos);
            } else {
                unsigned i = ps.size();
                while (i > 0) {
                    --i;
                    expr const & l = ps[i].m_local;
                    if (a.use_lambda_abstraction())
                        r = save_pos(Fun(l, r, ps[i].m_bi), binder_pos);
                    else
                        r = save_pos(Pi(l, r, ps[i].m_bi), binder_pos);
                    args.push_back(r);
                    r = instantiate_rev(a.get_rec(), args.size(), args.data());
                    args.pop_back();
                }
            }
            args.push_back(r);
            break;
        }
        case notation::action_kind::LuaExt:
            m_last_script_pos = p;
            using_script([&](lua_State * L) {
                    scoped_set_parser scope(L, *this);
                    lua_getglobal(L, a.get_lua_fn().c_str());
                    if (!lua_isfunction(L, -1))
                        throw parser_error(sstream() << "failed to use notation implemented in Lua, Lua state does not contain function '"
                                           << a.get_lua_fn() << "'", p);
                    lua_pushinteger(L, p.first);
                    lua_pushinteger(L, p.second);
                    for (unsigned i = 0; i < args.size(); i++)
                        push_expr(L, args[i]);
                    pcall(L, args.size() + 2, 1, 0);
                    if (!is_expr(L, -1))
                        throw parser_error(sstream() << "failed to use notation implemented in Lua, value returned by function '"
                                           << a.get_lua_fn() << "' is not an expression", p);
                    args.push_back(rec_save_pos(to_expr(L, -1), p));
                    lua_pop(L, 1);
                });
            break;
        case notation::action_kind::Ext:
            args.push_back(a.get_parse_fn()(*this, args.size(), args.data(), p));
            break;
        }

        t = r->second;
    }
    list<expr> const & as = t.is_accepting();
    if (is_nil(as)) {
        if (p == pos())
            throw parser_error(sstream() << "invalid expression", pos());
        else
            throw parser_error(sstream() << "invalid expression starting at " << p.first << ":" << p.second, pos());
    }
    buffer<expr> cs;
    for (expr const & a : as) {
        expr r = instantiate_rev(copy_with_new_pos(a, p), args.size(), args.data());
        cs.push_back(r);
    }
    return save_pos(mk_choice(cs.size(), cs.data()), p);
}

expr parser::parse_nud_notation() {
    return parse_notation(nud(), nullptr);
}

expr parser::parse_led_notation(expr left) {
    if (led().find(get_token_info().value()))
        return parse_notation(led(), &left);
    else
        return mk_app(left, parse_nud_notation(), pos_of(left));
}

expr parser::id_to_expr(name const & id, pos_info const & p) {
    buffer<level> lvl_buffer;
    levels ls;
    if (curr_is_token(g_llevel_curly)) {
        next();
        while (!curr_is_token(g_rcurly)) {
            lvl_buffer.push_back(parse_level());
        }
        next();
        ls = to_list(lvl_buffer.begin(), lvl_buffer.end());
    }
    // locals
    if (auto it1 = m_local_decls.find(id))
        return copy_with_new_pos(propagate_levels(it1->m_local, ls), p);
    optional<expr> r;
    // globals
    if (m_env.find(id))
        r = save_pos(mk_constant(id, ls), p);
    // aliases
    auto as = get_alias_exprs(m_env, id);
    if (!is_nil(as)) {
        buffer<expr> new_as;
        if (r)
            new_as.push_back(*r);
        for (auto const & e : as) {
            new_as.push_back(copy_with_new_pos(propagate_levels(e, ls), p));
        }
        r = save_pos(mk_choice(new_as.size(), new_as.data()), p);
    }
    if (m_no_undef_id_error)
        r = save_pos(mk_constant(get_namespace(m_env) + id, ls), p);
    if (!r)
        throw parser_error(sstream() << "unknown identifier '" << id << "'", p);
    return *r;
}

expr parser::parse_id() {
    auto p  = pos();
    name id = get_name_val();
    next();
    return id_to_expr(id, p);
}

expr parser::parse_numeral_expr() {
    // TODO(Leo)
    return expr();
}

expr parser::parse_decimal_expr() {
    // TODO(Leo)
    return expr();
}

expr parser::parse_string_expr() {
    // TODO(Leo)
    return expr();
}

expr parser::parse_nud() {
    switch (curr()) {
    case scanner::token_kind::Keyword:     return parse_nud_notation();
    case scanner::token_kind::Identifier:  return parse_id();
    case scanner::token_kind::Numeral:     return parse_numeral_expr();
    case scanner::token_kind::Decimal:     return parse_decimal_expr();
    case scanner::token_kind::String:      return parse_string_expr();
    default: throw parser_error("invalid expression, unexpected token", pos());
    }
}

expr parser::parse_led(expr left) {
    switch (curr()) {
    case scanner::token_kind::Keyword:     return parse_led_notation(left);
    case scanner::token_kind::Identifier:  return mk_app(left, parse_id(), pos_of(left));
    case scanner::token_kind::Numeral:     return mk_app(left, parse_numeral_expr(), pos_of(left));
    case scanner::token_kind::Decimal:     return mk_app(left, parse_decimal_expr(), pos_of(left));
    case scanner::token_kind::String:      return mk_app(left, parse_string_expr(), pos_of(left));
    default:                               return left;
    }
}

unsigned parser::curr_lbp() const {
    switch (curr()) {
    case scanner::token_kind::Keyword:
        return get_token_info().precedence();
    case scanner::token_kind::CommandKeyword: case scanner::token_kind::Eof:
    case scanner::token_kind::ScriptBlock:
        return 0;
    case scanner::token_kind::Identifier:     case scanner::token_kind::Numeral:
    case scanner::token_kind::Decimal:        case scanner::token_kind::String:
    case scanner::token_kind::QuotedSymbol:
        return std::numeric_limits<unsigned>::max();
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

expr parser::parse_expr(unsigned rbp) {
    expr left = parse_nud();
    while (rbp < curr_lbp()) {
        left = parse_led(left);
    }
    return left;
}

expr parser::parse_scoped_expr(unsigned num_params, parameter const * ps, local_environment const & lenv, unsigned rbp) {
    local_scope scope(*this);
    m_env = lenv;
    for (unsigned i = 0; i < num_params; i++)
        add_local(ps[i].m_local, ps[i].m_bi);
    return parse_expr(rbp);
}

expr parser::abstract(unsigned num_params, parameter const * ps, expr const & e, bool lambda, pos_info const & p) {
    buffer<expr> locals;
    for (unsigned i = 0; i < num_params; i++)
        locals.push_back(ps[i].m_local);
    expr r = ::lean::abstract(e, locals.size(), locals.data());
    unsigned i = num_params;
    while (i > 0) {
        --i;
        expr const & l = ps[i].m_local;
        name const & n = local_pp_name(l);
        expr type  = ::lean::abstract(mlocal_type(l), i, locals.data());
        if (lambda)
            r = mk_lambda(n, type, r, ps[i].m_bi);
        else
            r = mk_pi(n, type, r, ps[i].m_bi);
        r = save_pos(r, p);
    }
    return r;
}

tactic parser::parse_tactic(unsigned /* rbp */) {
    if (curr_is_token(g_lparen)) {
        next();
        auto r = parse_tactic();
        check_token_next(g_rparen, "invalid tactic, ')' expected");
        return r;
    } else if (curr_is_identifier()) {
        auto p  = pos();
        name id = get_name_val();
        next();
        if (auto it = tactic_cmds().find(id)) {
            return it->get_fn()(*this);
        } else {
            throw parser_error(sstream() << "unknown tactic '" << id << "'", p);
        }
    } else {
        throw parser_error("invalid tactic, '(' or tactic name expected", pos());
    }
}

void parser::save_hint(expr const & e, tactic const & t) {
    m_hints.insert(mk_pair(get_tag(e), t));
}

void parser::parse_command() {
    lean_assert(curr() == scanner::token_kind::CommandKeyword);
    m_last_cmd_pos = pos();
    name const & cmd_name = get_token_info().value();
    if (auto it = cmds().find(cmd_name)) {
        next();
        m_env = it->get_fn()(*this);
    } else {
        auto p = pos();
        next();
        throw parser_error(sstream() << "unknown command '" << cmd_name << "'", p);
    }
}

void parser::parse_script(bool as_expr) {
    m_last_script_pos = pos();
    std::string script_code = m_scanner.get_str_val();
    if (as_expr)
        script_code = "return " + script_code;
    next();
    using_script([&](lua_State * L) {
            dostring(L, script_code.c_str());
        });
}

static optional<std::string> find_file(name const & f, char const * ext) {
    try {
        return optional<std::string>(find_file(f, {ext}));
    } catch (...) {
        return optional<std::string>();
    }
}

static std::string g_lua_module_key("lua_module");
static void lua_module_reader(deserializer & d, module_idx, shared_environment &,
                              std::function<void(asynch_update_fn const &)> &,
                              std::function<void(delayed_update_fn const &)> & add_delayed_update) {
    std::string fname;
    d >> fname;
    add_delayed_update([=](environment const & env, io_state const &) -> environment {
            system_import(fname.c_str());
            return env;
        });
}
register_module_object_reader_fn g_lua_module_reader(g_lua_module_key, lua_module_reader);

void parser::parse_imports() {
    buffer<std::string> olean_files;
    buffer<std::string> lua_files;
    while (curr_is_token(g_import)) {
        m_last_cmd_pos = pos();
        next();
        while (curr_is_identifier()) {
            name f            = get_name_val();
            if (auto it = find_file(f, ".lua")) {
                lua_files.push_back(*it);
            } else if (auto it = find_file(f, ".olean")) {
                olean_files.push_back(*it);
            } else {
                throw parser_error(sstream() << "invalid import, unknow module '" << f << "'", pos());
            }
            next();
        }
    }
    m_env = import_modules(m_env, olean_files.size(), olean_files.data(), m_num_threads, true, m_ios);
    for (auto const & f : lua_files) {
        system_import(f.c_str());
        m_env = module::add(m_env, g_lua_module_key, [=](serializer & s) {
                s << f;
            });
    }
}

bool parser::parse_commands() {
    // We disable hash-consing while parsing to make sure the pos-info are correct.
    scoped_expr_caching disable(false);
    try {
        bool done = false;
        parse_imports();
        while (!done) {
            protected_call([&]() {
                    check_interrupted();
                    switch (curr()) {
                    case scanner::token_kind::CommandKeyword:
                        parse_command();
                        break;
                    case scanner::token_kind::ScriptBlock:
                        parse_script();
                        break;
                    case scanner::token_kind::Eof:
                        done = true;
                        break;
                    case scanner::token_kind::Keyword:
                        if (curr_is_token(g_period)) {
                            next();
                            break;
                        }
                    default:
                        throw parser_error("command expected", pos());
                    }
                },
                [&]() { sync_command(); });
        }
    } catch (interrupt_parser) {}
    return !m_found_errors;
}

bool parse_commands(environment & env, io_state & ios, std::istream & in, char const * strm_name, bool use_exceptions,
                    unsigned num_threads) {
    parser p(env, ios, in, strm_name, use_exceptions, num_threads);
    bool r = p();
    ios = p.ios();
    env = p.env();
    return r;
}

bool parse_commands(environment & env, io_state & ios, char const * fname, bool use_exceptions, unsigned num_threads) {
    std::ifstream in(fname);
    if (in.bad() || in.fail())
        throw exception(sstream() << "failed to open file '" << fname << "'");
    return parse_commands(env, ios, in, fname, use_exceptions, num_threads);
}

static unsigned to_rbp(lua_State * L, int idx) {
    int nargs = lua_gettop(L);
    return idx < nargs ? 0 : lua_tointeger(L, idx);
}

typedef std::pair<local_environment, std::vector<parameter>> local_scope_cell;
typedef std::shared_ptr<local_scope_cell> local_scope;
DECL_UDATA(local_scope);
static const struct luaL_Reg local_scope_m[] = {
    {"__gc",  local_scope_gc},
    {0, 0}
};
int push_local_scope_ext(lua_State * L, local_environment const & lenv, buffer<parameter> const & ps) {
    local_scope r = std::make_shared<local_scope_cell>();
    r->first = lenv;
    for (auto const & p : ps)
        r->second.push_back(p);
    return push_local_scope(L, r);
}

static void open_local_scope(lua_State * L) {
    luaL_newmetatable(L, local_scope_mt);
    lua_pushvalue(L, -1);
    lua_setfield(L, -2, "__index");
    setfuncs(L, local_scope_m, 0);

    SET_GLOBAL_FUN(local_scope_pred, "is_local_scope");
}

#define gparser get_global_parser(L)

static int parse_level(lua_State * L) {  return push_level(L, gparser.parse_level(to_rbp(L, 1))); }
static int parse_expr(lua_State * L) { return push_expr(L, gparser.parse_expr(to_rbp(L, 1))); }
static int parse_led(lua_State * L) { return push_expr(L, gparser.parse_led(to_expr(L, 1))); }
static int parse_binders(lua_State * L) {
    buffer<parameter> ps;
    auto lenv = gparser.parse_binders(ps);
    return push_local_scope_ext(L, lenv, ps);
}
static int parse_binder(lua_State * L) {
    buffer<parameter> ps;
    ps.push_back(gparser.parse_binder());
    return push_local_scope_ext(L, gparser.env(), ps);
}
static int parse_scoped_expr(lua_State * L) {
    local_scope const & s = to_local_scope(L, 1);
    unsigned rbp    = to_rbp(L, 2);
    return push_expr(L, gparser.parse_scoped_expr(s->second.size(), s->second.data(), s->first, rbp));
}
static int lambda_abstract(lua_State * L) {
    int nargs = lua_gettop(L);
    local_scope const & s = to_local_scope(L, 1);
    expr const & e = to_expr(L, 2);
    expr r;
    if (nargs == 2)
        r = gparser.abstract(s->second.size(), s->second.data(), e, true, gparser.pos_of(e));
    else
        r = gparser.abstract(s->second.size(), s->second.data(), e, true, pos_info(lua_tointeger(L, 3), lua_tointeger(L, 4)));
    return push_expr(L, r);
}
static int next(lua_State * L) { gparser.next(); return 0; }
static int curr(lua_State * L) { return push_integer(L, static_cast<unsigned>(gparser.curr())); }
static int curr_is_token(lua_State * L) { return push_boolean(L, gparser.curr_is_token(to_name_ext(L, 1))); }
static int curr_is_token_or_id(lua_State * L) { return push_boolean(L, gparser.curr_is_token_or_id(to_name_ext(L, 1))); }
static int curr_is_identifier(lua_State * L) { return push_boolean(L, gparser.curr_is_identifier()); }
static int curr_is_numeral(lua_State * L) { return push_boolean(L, gparser.curr_is_numeral()); }
static int curr_is_string(lua_State * L) { return push_boolean(L, gparser.curr_is_string()); }
static int curr_is_keyword(lua_State * L) { return push_boolean(L, gparser.curr_is_keyword()); }
static int curr_is_command(lua_State * L) { return push_boolean(L, gparser.curr_is_command()); }
static int curr_is_quoted_symbol(lua_State * L) { return push_boolean(L, gparser.curr_is_quoted_symbol()); }
static int check_token_next(lua_State * L) { gparser.check_token_next(to_name_ext(L, 1), lua_tostring(L, 2)); return 0; }
static int check_id_next(lua_State * L) { return push_name(L, gparser.check_id_next(lua_tostring(L, 1))); }
static int pos(lua_State * L) {
    auto pos = gparser.pos();
    push_integer(L, pos.first);
    push_integer(L, pos.second);
    return 2;
}
static int save_pos(lua_State * L) {
    return push_expr(L, gparser.save_pos(to_expr(L, 1), pos_info(lua_tointeger(L, 2), lua_tointeger(L, 3))));
}
static int pos_of(lua_State * L) {
    int nargs = lua_gettop(L);
    pos_info pos;
    if (nargs == 1)
        pos = gparser.pos_of(to_expr(L, 1));
    else
        pos = gparser.pos_of(to_expr(L, 1), pos_info(lua_tointeger(L, 2), lua_tointeger(L, 3)));
    push_integer(L, pos.first);
    push_integer(L, pos.second);
    return 2;
}
static int env(lua_State * L) { return push_environment(L, gparser.env()); }
static int ios(lua_State * L) { return push_io_state(L, gparser.ios()); }

void open_parser(lua_State * L) {
    open_local_scope(L);

    lua_newtable(L);
    SET_FUN(parse_expr,            "parse_expr");
    SET_FUN(parse_level,           "parse_level");
    SET_FUN(parse_led,             "parse_led");
    SET_FUN(parse_binders,         "parse_binders");
    SET_FUN(parse_binder,          "parse_binder");
    SET_FUN(parse_scoped_expr,     "parse_scoped_expr");
    SET_FUN(lambda_abstract,       "lambda_abstract");
    SET_FUN(lambda_abstract,       "abstract");
    SET_FUN(next,                  "next");
    SET_FUN(curr,                  "curr");
    SET_FUN(curr_is_token,         "curr_is_token");
    SET_FUN(curr_is_token_or_id,   "curr_is_token_or_id");
    SET_FUN(curr_is_identifier,    "curr_is_identifier");
    SET_FUN(curr_is_numeral,       "curr_is_numeral");
    SET_FUN(curr_is_string,        "curr_is_string");
    SET_FUN(curr_is_keyword,       "curr_is_keyword");
    SET_FUN(curr_is_command,       "curr_is_command");
    SET_FUN(curr_is_quoted_symbol, "curr_is_quoted_symbol");
    SET_FUN(check_token_next,      "check_token_next");
    SET_FUN(check_id_next,         "check_id_next");
    SET_FUN(pos,                   "pos");
    SET_FUN(save_pos,              "save_pos");
    SET_FUN(pos_of,                "pos_of");
    SET_FUN(env,                   "env");
    SET_FUN(ios,                   "ios");
    lua_setglobal(L, "parser");

    lua_newtable(L);
    SET_ENUM("Keyword",         scanner::token_kind::Keyword);
    SET_ENUM("CommandKeyword",  scanner::token_kind::CommandKeyword);
    SET_ENUM("ScriptBlock",     scanner::token_kind::ScriptBlock);
    SET_ENUM("Identifier",      scanner::token_kind::Identifier);
    SET_ENUM("Numeral",         scanner::token_kind::Numeral);
    SET_ENUM("Decimal",         scanner::token_kind::Decimal);
    SET_ENUM("String",          scanner::token_kind::String);
    SET_ENUM("QuotedSymbol",    scanner::token_kind::QuotedSymbol);
    lua_setglobal(L, "token_kind");
}
}
