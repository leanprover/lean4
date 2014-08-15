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
#include "kernel/error_msgs.h"
#include "library/parser_nested_exception.h"
#include "library/aliases.h"
#include "library/private.h"
#include "library/choice.h"
#include "library/placeholder.h"
#include "library/deep_copy.h"
#include "library/module.h"
#include "library/scoped_ext.h"
#include "library/explicit.h"
#include "library/num.h"
#include "library/string.h"
#include "library/error_handling/error_handling.h"
#include "library/tactic/expr_to_tactic.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/parser_bindings.h"
#include "frontends/lean/notation_cmd.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/pp_options.h"
#include "frontends/lean/sorry.h"

#ifndef LEAN_DEFAULT_PARSER_SHOW_ERRORS
#define LEAN_DEFAULT_PARSER_SHOW_ERRORS true
#endif

#ifndef LEAN_DEFAULT_PARSER_PARALLEL_IMPORT
#define LEAN_DEFAULT_PARSER_PARALLEL_IMPORT false
#endif

namespace lean {
// ==========================================
// Parser configuration options
static name g_parser_show_errors     {"parser", "show_errors"};
static name g_parser_parallel_import {"parser", "parallel_import"};

RegisterBoolOption(g_parser_show_errors, LEAN_DEFAULT_PARSER_SHOW_ERRORS, "(lean parser) display error messages in the regular output channel");
RegisterBoolOption(g_parser_parallel_import, LEAN_DEFAULT_PARSER_PARALLEL_IMPORT, "(lean parser) import modules in parallel");

bool     get_parser_show_errors(options const & opts)  { return opts.get_bool(g_parser_show_errors, LEAN_DEFAULT_PARSER_SHOW_ERRORS); }
bool     get_parser_parallel_import(options const & opts)  { return opts.get_bool(g_parser_parallel_import, LEAN_DEFAULT_PARSER_PARALLEL_IMPORT); }
// ==========================================

parser::local_scope::local_scope(parser & p):
    m_p(p), m_env(p.env()) {
    p.push_local_scope();
}
parser::local_scope::~local_scope() {
    m_p.pop_local_scope();
    m_p.m_env = m_env;
}

parser::no_undef_id_error_scope::no_undef_id_error_scope(parser & p):m_p(p), m_old(m_p.m_no_undef_id_error) {
    m_p.m_no_undef_id_error = true;
}
parser::no_undef_id_error_scope::~no_undef_id_error_scope() {
    m_p.m_no_undef_id_error = m_old;
}

static name g_tmp_prefix = name::mk_internal_unique_name();

parser::parser(environment const & env, io_state const & ios,
               std::istream & strm, char const * strm_name,
               bool use_exceptions, unsigned num_threads,
               local_level_decls const & lds, local_expr_decls const & eds,
               unsigned line, snapshot_vector * sv, info_manager * im):
    m_env(env), m_ios(ios), m_ngen(g_tmp_prefix),
    m_verbose(true), m_use_exceptions(use_exceptions),
    m_scanner(strm, strm_name, line), m_local_level_decls(lds), m_local_decls(eds),
    m_theorem_queue(*this, num_threads > 1 ? num_threads - 1 : 0),
    m_snapshot_vector(sv), m_info_manager(im), m_cache(nullptr) {
    m_num_threads = num_threads;
    m_no_undef_id_error    = false;
    m_found_errors = false;
    m_used_sorry = false;
    updt_options();
    m_next_tag_idx = 0;
    m_curr = scanner::token_kind::Identifier;
    protected_call([&]() { scan(); },
                   [&]() { sync_command(); });
}

parser::~parser() {
    try {
        if (!m_theorem_queue.done()) {
            m_theorem_queue.interrupt();
            m_theorem_queue.join();
        }
    } catch (...) {}
}

void parser::cache_definition(name const & n, expr const & pre_type, expr const & pre_value,
                              level_param_names const & ls, expr const & type, expr const & value) {
    if (m_cache)
        m_cache->add(n, pre_type, pre_value, ls, type, value);
}

optional<std::tuple<level_param_names, expr, expr>> parser::find_cached_definition(name const & n, expr const & pre_type, expr const & pre_value) {
    if (m_cache)
        return m_cache->find(n, pre_type, pre_value);
    else
        return optional<std::tuple<level_param_names, expr, expr>>();
}

void parser::add_decl_index(name const & n, pos_info const & pos) {
    if (m_index)
        m_index->add_decl(get_stream_name(), pos, n);
}

void parser::add_ref_index(name const & n, pos_info const & pos) {
    if (m_index)
        m_index->add_ref(get_stream_name(), pos, n);
}

expr parser::mk_sorry(pos_info const & p) {
    m_used_sorry = true;
    {
        flycheck_warning wrn(regular_stream());
        display_warning_pos(p.first, p.second);
        regular_stream() << " using 'sorry'" << endl;
    }
    return get_sorry_constant();
}

void parser::declare_sorry() {
    m_used_sorry = true;
    m_env = ::lean::declare_sorry(m_env);
}

bool parser::has_tactic_decls() {
    if (!m_has_tactic_decls)
        m_has_tactic_decls = ::lean::has_tactic_decls(m_env);
    return *m_has_tactic_decls;
}

expr parser::mk_by(expr const & t, pos_info const & pos) {
    if (!has_tactic_decls())
        throw parser_error("invalid 'by' expression, tactic module has not been imported", pos);
    return save_pos(::lean::mk_by(t), pos);
}

void parser::updt_options() {
    m_verbose = get_verbose(m_ios.get_options());
    m_show_errors = get_parser_show_errors(m_ios.get_options());
}

void parser::display_warning_pos(unsigned line, unsigned pos) {
    ::lean::display_warning_pos(regular_stream(), get_stream_name().c_str(), line, pos);
}
void parser::display_warning_pos(pos_info p) { display_warning_pos(p.first, p.second); }

void parser::display_error_pos(unsigned line, unsigned pos) {
    ::lean::display_error_pos(regular_stream(), get_stream_name().c_str(), line, pos);
}
void parser::display_error_pos(pos_info p) { display_error_pos(p.first, p.second); }

void parser::display_error(char const * msg, unsigned line, unsigned pos) {
    flycheck_error err(regular_stream());
    display_error_pos(line, pos);
    regular_stream() << " " << msg << endl;
}

void parser::display_error(char const * msg, pos_info p) { display_error(msg, p.first, p.second); }

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
save_pre_info_data();                                   \
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
        CATCH(flycheck_error err(regular_stream()); regular_stream() << ex.what() << endl,
              throw);
    } catch (parser_error & ex) {
        CATCH(display_error(ex.what(), ex.m_pos),
              throw_parser_exception(ex.what(), ex.m_pos));
    } catch (interrupted & ex) {
        save_pre_info_data();
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
    auto t = get_tag(e);
    if (!m_pos_table.contains(t))
        m_pos_table.insert(t, p);
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
        return replace(e, [&](expr const & e) {
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
    if (auto it = m_pos_table.find(get_tag(e)))
        return *it;
    else
        return default_pos;
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

name parser::check_atomic_id_next(char const * msg) {
    auto p  = pos();
    name id = check_id_next(msg);
    if (!id.is_atomic())
        throw parser_error(msg, p);
    return id;
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
    m_local_level_decls.push();
    m_local_decls.push();
}

void parser::pop_local_scope() {
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

void parser::add_local_expr(name const & n, expr const & p) {
    m_local_decls.insert(n, p);
}

unsigned parser::get_local_level_index(name const & n) const {
    return m_local_level_decls.find_idx(n);
}

unsigned parser::get_local_index(name const & n) const {
    return m_local_decls.find_idx(n);
}

static name g_period("."), g_colon(":"), g_lparen("("), g_rparen(")"), g_llevel_curly(".{");
static name g_lcurly("{"), g_rcurly("}"), g_ldcurly("⦃"), g_rdcurly("⦄"), g_lbracket("["), g_rbracket("]");
static name g_bar("|"), g_comma(","), g_add("+"), g_max("max"), g_imax("imax"), g_cup("\u2294");
static name g_import("import"), g_show("show"), g_have("have"), g_assume("assume"), g_take("take"), g_fun("fun");
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
    if (auto it = get_level_alias(m_env, id))
        return mk_global_univ(*it);
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

elaborator_context parser::mk_elaborator_context(pos_info_provider const &  pp, bool check_unassigned) {
    return elaborator_context(m_env, m_ios, m_local_level_decls, &pp, m_info_manager, check_unassigned);
}

elaborator_context parser::mk_elaborator_context(environment const & env, pos_info_provider const & pp) {
    return elaborator_context(env, m_ios, m_local_level_decls, &pp, m_info_manager, true);
}

elaborator_context parser::mk_elaborator_context(environment const & env, local_level_decls const & lls, pos_info_provider const & pp) {
    return elaborator_context(env, m_ios, lls, &pp, m_info_manager, true);
}

std::tuple<expr, level_param_names> parser::elaborate_relaxed(expr const & e, list<expr> const & ctx) {
    bool relax            = true;
    bool check_unassigned = false;
    bool ensure_type      = false;
    parser_pos_provider pp = get_pos_provider();
    elaborator_context env = mk_elaborator_context(pp, check_unassigned);
    auto r = ::lean::elaborate(env, ctx, e, relax, ensure_type);
    m_pre_info_data.clear();
    return r;
}

std::tuple<expr, level_param_names> parser::elaborate_type(expr const & e, list<expr> const & ctx) {
    bool relax            = false;
    bool check_unassigned = true;
    bool ensure_type      = true;
    parser_pos_provider pp = get_pos_provider();
    elaborator_context env = mk_elaborator_context(pp, check_unassigned);
    auto r = ::lean::elaborate(env, ctx, e, relax, ensure_type);
    m_pre_info_data.clear();
    return r;
}

std::tuple<expr, level_param_names> parser::elaborate_at(environment const & env, expr const & e) {
    bool relax            = false;
    parser_pos_provider pp = get_pos_provider();
    elaborator_context eenv = mk_elaborator_context(env, pp);
    auto r = ::lean::elaborate(eenv, list<expr>(), e, relax);
    m_pre_info_data.clear();
    return r;
}

std::tuple<expr, expr, level_param_names> parser::elaborate_definition(name const & n, expr const & t, expr const & v,
                                                                       bool is_opaque) {
    parser_pos_provider pp = get_pos_provider();
    elaborator_context eenv = mk_elaborator_context(pp);
    auto r = ::lean::elaborate(eenv, n, t, v, is_opaque);
    m_pre_info_data.clear();
    return r;
}

std::tuple<expr, expr, level_param_names> parser::elaborate_definition_at(environment const & env, local_level_decls const & lls,
                                                                          name const & n, expr const & t, expr const & v, bool is_opaque) {
    parser_pos_provider pp = get_pos_provider();
    elaborator_context eenv = mk_elaborator_context(env, lls, pp);
    auto r = ::lean::elaborate(eenv, n, t, v, is_opaque);
    m_pre_info_data.clear();
    return r;
}

[[ noreturn ]] void throw_invalid_open_binder(pos_info const & pos) {
    throw parser_error("invalid binder, '(', '{', '[', '{{', '⦃' or identifier expected", pos);
}

/**
   \brief Return an optional binder_info object based on the current token
      - '('           : default
      - '{'          : implicit
      - '{{' or '⦃'  : strict implicit
      - '['          : cast
*/
optional<binder_info> parser::parse_optional_binder_info() {
    if (curr_is_token(g_lparen)) {
        next();
        return some(binder_info());
    } else if (curr_is_token(g_lcurly)) {
        next();
        if (curr_is_token(g_lcurly)) {
            next();
            return some(mk_strict_implicit_binder_info());
        } else {
            return some(mk_implicit_binder_info());
        }
    } else if (curr_is_token(g_lbracket)) {
        next();
        return some(mk_cast_binder_info());
    } else if (curr_is_token(g_ldcurly)) {
        next();
        return some(mk_strict_implicit_binder_info());
    } else {
        return optional<binder_info>();
    }
}

/**
   \brief Return binder_info object based on the current token, it fails if the current token
   is not '(', '{', '{{', '⦃', or '['

   \see parse_optional_binder_info
*/
binder_info parser::parse_binder_info() {
    auto p = pos();
    if (auto bi = parse_optional_binder_info()) {
        return *bi;
    } else {
        throw_invalid_open_binder(p);
    }
}

/**
   \brief Consume the next token based on the value of \c bi
     - none            : do not consume anything
     - default         : consume ')'
     - implicit        : consume '}'
     - strict implicit : consume '}}' or '⦄'
     - cast            : consume ']'
*/
void parser::parse_close_binder_info(optional<binder_info> const & bi) {
    if (!bi) {
        return;
    } else if (bi->is_implicit()) {
        check_token_next(g_rcurly, "invalid declaration, '}' expected");
    } else if (bi->is_cast()) {
        check_token_next(g_rbracket, "invalid declaration, ']' expected");
    } else if (bi->is_strict_implicit()) {
        if (curr_is_token(g_rcurly)) {
            next();
            check_token_next(g_rcurly, "invalid declaration, '}' expected");
        } else {
            check_token_next(g_rdcurly, "invalid declaration, '⦄' expected");
        }
    } else {
        check_token_next(g_rparen, "invalid declaration, ')' expected");
    }
}

/** \brief Parse <tt>ID ':' expr</tt>, where the expression represents the type of the identifier. */
expr parser::parse_binder_core(binder_info const & bi) {
    auto p  = pos();
    name id = check_atomic_id_next("invalid binder, atomic identifier expected");
    expr type;
    if (curr_is_token(g_colon)) {
        next();
        type = parse_expr();
    } else {
        type = save_pos(mk_expr_placeholder(), p);
    }
    return save_pos(mk_local(id, type, bi), p);
}

expr parser::parse_binder() {
    if (curr_is_identifier()) {
        return parse_binder_core(binder_info());
    } else {
        binder_info bi = parse_binder_info();
        auto r = parse_binder_core(bi);
        parse_close_binder_info(bi);
        return r;
    }
}

/**
   \brief Parse <tt>ID ... ID ':' expr</tt>, where the expression
   represents the type of the identifiers.
*/
void parser::parse_binder_block(buffer<expr> & r, binder_info const & bi) {
    buffer<std::pair<pos_info, name>> names;
    while (curr_is_identifier()) {
        auto p = pos();
        names.emplace_back(p, check_atomic_id_next("invalid binder, atomic identifier expected"));
    }
    if (names.empty())
        throw parser_error("invalid binder, identifier expected", pos());
    optional<expr> type;
    if (curr_is_token(g_colon)) {
        next();
        type = parse_expr();
    }
    for (auto p : names) {
        expr arg_type = type ? *type : save_pos(mk_expr_placeholder(), p.first);
        expr local = save_pos(mk_local(p.second, arg_type, bi), p.first);
        add_local(local);
        r.push_back(local);
    }
}

void parser::parse_binders_core(buffer<expr> & r, buffer<notation_entry> * nentries) {
    while (true) {
        if (curr_is_identifier()) {
            parse_binder_block(r, binder_info());
        } else {
            optional<binder_info> bi = parse_optional_binder_info();
            if (bi) {
                if (!parse_local_notation_decl(nentries))
                    parse_binder_block(r, *bi);
                parse_close_binder_info(bi);
            } else {
                return;
            }
        }
    }
}

local_environment parser::parse_binders(buffer<expr> & r, buffer<notation_entry> * nentries) {
    flet<environment> save(m_env, m_env); // save environment
    local_expr_decls::mk_scope scope(m_local_decls);
    unsigned old_sz = r.size();
    parse_binders_core(r, nentries);
    if (old_sz == r.size())
        throw_invalid_open_binder(pos());
    return local_environment(m_env);
}

bool parser::parse_local_notation_decl(buffer<notation_entry> * nentries) {
    if (curr_is_notation_decl(*this)) {
        buffer<token_entry> new_tokens;
        auto ne = ::lean::parse_notation(*this, false, new_tokens);
        for (auto const & te : new_tokens)
            m_env = add_token(m_env, te);
        if (nentries) nentries->push_back(ne);
        m_env = add_notation(m_env, ne);
        return true;
    } else {
        return false;
    }
}

expr parser::parse_notation(parse_table t, expr * left) {
    lean_assert(curr() == scanner::token_kind::Keyword);
    auto p = pos();
    buffer<expr>  args;
    buffer<expr>  ps;
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
            auto terminator = a.get_terminator();
            if (!terminator || !curr_is_token(*terminator)) {
                r_args.push_back(parse_expr(a.rbp()));
                while (curr_is_token(a.get_sep())) {
                    next();
                    r_args.push_back(parse_expr(a.rbp()));
                }
            }
            if (terminator) {
                if (curr_is_token(*terminator)) {
                    next();
                } else {
                    throw parser_error(sstream() << "invalid composite expression, '" << *terminator << "' expected", pos());
                }
            }
            expr r   = instantiate_rev(copy_with_new_pos(a.get_initial(), p), args.size(), args.data());
            expr rec = copy_with_new_pos(a.get_rec(), p);
            if (a.is_fold_right()) {
                unsigned i = r_args.size();
                while (i > 0) {
                    --i;
                    args.push_back(r_args[i]);
                    args.push_back(r);
                    r = instantiate_rev(rec, args.size(), args.data());
                    args.pop_back(); args.pop_back();
                }
            } else {
                for (unsigned i = 0; i < r_args.size(); i++) {
                    args.push_back(r_args[i]);
                    args.push_back(r);
                    r = instantiate_rev(rec, args.size(), args.data());
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
            expr r   = parse_scoped_expr(ps, lenv, a.rbp());
            if (is_var(a.get_rec(), 0)) {
                if (a.use_lambda_abstraction())
                    r = Fun(ps, r);
                else
                    r = Pi(ps, r);
                r = rec_save_pos(r, binder_pos);
            } else {
                expr rec = copy_with_new_pos(a.get_rec(), p);
                unsigned i = ps.size();
                while (i > 0) {
                    --i;
                    expr const & l = ps[i];
                    if (a.use_lambda_abstraction())
                        r = Fun(l, r);
                    else
                        r = Pi(l, r);
                    r = save_pos(r, binder_pos);
                    args.push_back(r);
                    r = instantiate_rev(rec, args.size(), args.data());
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
    expr r = save_pos(mk_choice(cs.size(), cs.data()), p);
    save_overload(r);
    save_type_info(r);
    return r;
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

    if (id.is_atomic()) {
        // locals
        if (auto it1 = m_local_decls.find(id)) {
            auto r = copy_with_new_pos(propagate_levels(*it1, ls), p);
            save_type_info(r);
            return r;
        }
    } else {
        lean_assert(!id.is_atomic());
        name new_id = remove_root_prefix(id);
        if (m_env.find(new_id)) {
            auto r = save_pos(mk_constant(new_id, ls), p);
            save_type_info(r);
            add_ref_index(new_id, p);
            return r;
        } else {
            for (name const & ns : get_namespaces(m_env)) {
                auto new_id = ns + id;
                if (m_env.find(new_id)) {
                    auto r = save_pos(mk_constant(new_id, ls), p);
                    save_type_info(r);
                    add_ref_index(new_id, p);
                    return r;
                }
            }
        }
    }

    optional<expr> r;
    // globals
    if (m_env.find(id))
        r = save_pos(mk_constant(id, ls), p);
    // aliases
    auto as = get_expr_aliases(m_env, id);
    if (!is_nil(as)) {
        buffer<expr> new_as;
        if (r)
            new_as.push_back(*r);
        for (auto const & e : as) {
            new_as.push_back(copy_with_new_pos(mk_constant(e, ls), p));
        }
        r = save_pos(mk_choice(new_as.size(), new_as.data()), p);
        if (is_constant(*r))
            add_ref_index(const_name(*r), p);
        save_overload(*r);
    }
    if (!r && m_no_undef_id_error)
        r = save_pos(mk_constant(get_namespace(m_env) + id, ls), p);
    if (!r)
        throw parser_error(sstream() << "unknown identifier '" << id << "'", p);
    save_type_info(*r);
    return *r;
}

name parser::check_constant_next(char const * msg) {
    auto p  = pos();
    name id = check_id_next(msg);
    expr e  = id_to_expr(id, p);

    if (in_section(m_env) && is_implicit(e)) {
        e = get_app_fn(get_implicit_arg(e));
        if (is_explicit(e))
            e = get_explicit_arg(e);
    }

    if (is_constant(e)) {
        return const_name(e);
    } else {
        throw parser_error(msg, p);
    }
}

expr parser::parse_id() {
    auto p  = pos();
    name id = get_name_val();
    next();
    return id_to_expr(id, p);
}

expr parser::parse_numeral_expr() {
    auto p = pos();
    mpz n = get_num_val().get_numerator();
    next();
    if (!m_has_num)
        m_has_num = has_num_decls(m_env);
    if (!*m_has_num)
        throw parser_error("numeral cannot be encoded as expression, environment does not contain the type 'num' "
                           "(solution: use 'import num')", p);
    return from_num(n);
}

expr parser::parse_decimal_expr() {
    // TODO(Leo)
    next();  // to avoid loop
    return expr();
}

expr parser::parse_string_expr() {
    auto p = pos();
    std::string v = get_str_val();
    next();
    if (!m_has_string)
        m_has_string = has_string_decls(m_env);
    if (!*m_has_string)
        throw parser_error("string cannot be encoded as expression, environment does not contain the type 'string' "
                           "(solution: use 'import string')", p);
    return from_string(v);
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
    case scanner::token_kind::ScriptBlock:    case scanner::token_kind::QuotedSymbol:
        return 0;
    case scanner::token_kind::Identifier:     case scanner::token_kind::Numeral:
    case scanner::token_kind::Decimal:        case scanner::token_kind::String:
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

expr parser::parse_scoped_expr(unsigned num_ps, expr const * ps, local_environment const & lenv, unsigned rbp) {
    local_scope scope(*this);
    m_env = lenv;
    for (unsigned i = 0; i < num_ps; i++)
        add_local(ps[i]);
    return parse_expr(rbp);
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

static optional<std::string> try_file(name const & f, char const * ext) {
    try {
        return optional<std::string>(find_file(f, {ext}));
    } catch (...) {
        return optional<std::string>();
    }
}

static optional<std::string> try_file(std::string const & base, optional<unsigned> const & k, name const & f, char const * ext) {
    try {
        return optional<std::string>(find_file(base, k, f, ext));
    } catch (...) {
        return optional<std::string>();
    }
}

static std::string g_lua_module_key("lua_module");
static void lua_module_reader(deserializer & d, module_idx, shared_environment &,
                              std::function<void(asynch_update_fn const &)> &,
                              std::function<void(delayed_update_fn const &)> & add_delayed_update) {
    name fname;
    d >> fname;
    add_delayed_update([=](environment const & env, io_state const &) -> environment {
            std::string rname = find_file(fname, {".lua"});
            system_import(rname.c_str());
            return env;
        });
}
register_module_object_reader_fn g_lua_module_reader(g_lua_module_key, lua_module_reader);

void parser::parse_imports() {
    buffer<module_name> olean_files;
    buffer<name>        lua_files;
    std::string base = dirname(get_stream_name().c_str());
    while (curr_is_token(g_import)) {
        m_last_cmd_pos = pos();
        next();
        while (true) {
            optional<unsigned> k;
            while (curr_is_token(g_period)) {
                next();
                if (!k)
                    k = 0;
                else
                    k = *k + 1;
            }
            if (!curr_is_identifier())
                break;
            name f            = get_name_val();
            if (auto it = try_file(f, ".lua")) {
                if (k)
                    throw parser_error(sstream() << "invalid import, failed to import '" << f
                                       << "', relative paths are not supported for .lua files", pos());
                lua_files.push_back(f);
            } else if (auto it = try_file(base, k, f, ".olean")) {
                olean_files.push_back(module_name(k, f));
            } else {
                m_found_errors = true;
                if (!m_use_exceptions && m_show_errors) {
                    flycheck_error err(regular_stream());
                    display_error_pos(pos());
                    regular_stream() << " invalid import, unknown module '" << f << "'" << endl;
                }
                if (m_use_exceptions)
                    throw parser_error(sstream() << "invalid import, unknown module '" << f << "'", pos());
            }
            next();
        }
    }
    unsigned num_threads = 0;
    if (get_parser_parallel_import(m_ios.get_options()))
        num_threads = m_num_threads;
    m_env = import_modules(m_env, base, olean_files.size(), olean_files.data(), num_threads, true, m_ios);
    for (auto const & f : lua_files) {
        std::string rname = find_file(f, {".lua"});
        system_import(rname.c_str());
        m_env = module::add(m_env, g_lua_module_key, [=](serializer & s) {
                s << f;
            });
    }
}

bool parser::parse_commands() {
    // We disable hash-consing while parsing to make sure the pos-info are correct.
    scoped_expr_caching disable(false);
    scoped_set_distinguishing_pp_options set(get_distinguishing_pp_options());
    try {
        bool done = false;
        protected_call([&]() {
                parse_imports();
            },
            [&]() { sync_command(); });
        if (has_sorry(m_env)) {
            flycheck_warning wrn(regular_stream());
            display_warning_pos(pos());
            regular_stream() << " imported file uses 'sorry'" << endl;
        }
        while (!done) {
            protected_call([&]() {
                    check_interrupted();
                    switch (curr()) {
                    case scanner::token_kind::CommandKeyword:
                        parse_command();
                        save_snapshot();
                        break;
                    case scanner::token_kind::ScriptBlock:
                        parse_script();
                        save_snapshot();
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
        if (has_open_scopes(m_env)) {
            m_found_errors = true;
            if (!m_use_exceptions && m_show_errors)
                display_error("invalid end of module, expecting 'end'", pos());
            else if (m_use_exceptions)
                throw_parser_exception("invalid end of module, expecting 'end'", pos());
        }
    } catch (interrupt_parser) {}
    save_snapshot();
    for (certified_declaration const & thm : m_theorem_queue.join()) {
        m_env.replace(thm);
    }
    return !m_found_errors;
}

void parser::add_delayed_theorem(environment const & env, name const & n, level_param_names const & ls, expr const & t, expr const & v) {
    m_theorem_queue.add(env, n, ls, get_local_level_decls(), t, v);
}

void parser::save_snapshot() {
    m_pre_info_data.clear();
    if (!m_snapshot_vector)
        return;
    if (m_snapshot_vector->empty() || static_cast<int>(m_snapshot_vector->back().m_line) != m_scanner.get_line())
        m_snapshot_vector->push_back(snapshot(m_env, m_local_level_decls, m_local_decls, m_ios.get_options(), m_scanner.get_line()));
}

void parser::save_pre_info_data() {
    // if elaborator failed, then m_pre_info_data contains type information before elaboration.
    if (m_info_manager) {
        m_info_manager->append(m_pre_info_data, false);
        m_pre_info_data.clear();
    }
}

void parser::save_overload(expr const & e) {
    if (!m_info_manager || !is_choice(e))
        return;
    auto p = pos_of(e);
    m_info_manager->add(std::unique_ptr<info_data>(new overload_info_data(p.first, p.second, e)));
}

void parser::save_type_info(expr const & e) {
    if (!m_info_manager)
        return;
    if (is_explicit(e)) {
        save_type_info(get_explicit_arg(e));
    } else if (is_implicit(e)) {
        save_type_info(get_implicit_arg(e));
    } else if (is_choice(e)) {
        for (unsigned i = 0; i < get_num_choices(e); i++)
            save_type_info(get_choice(e, i));
    } else if (is_app(e)) {
        save_type_info(get_app_fn(e));
    } else if (is_constant(e)) {
        auto d = m_env.find(const_name(e));
        if (!d)
            return;
        auto p = pos_of(e);
        m_pre_info_data.push_back(type_info_data(p.first, p.second, d->get_type()));
    } else if (is_local(e)) {
        auto p = pos_of(e);
        expr t = mlocal_type(e);
        if (is_meta(t))
            return;
        m_pre_info_data.push_back(type_info_data(p.first, p.second, t));
    }
}

bool parse_commands(environment & env, io_state & ios, std::istream & in, char const * strm_name, bool use_exceptions,
                    unsigned num_threads, definitions_cache * cache, declaration_index * index) {
    parser p(env, ios, in, strm_name, use_exceptions, num_threads);
    p.set_cache(cache);
    p.set_index(index);
    bool r = p();
    ios = p.ios();
    env = p.env();
    return r;
}

bool parse_commands(environment & env, io_state & ios, char const * fname, bool use_exceptions, unsigned num_threads,
                    definitions_cache * cache, declaration_index * index) {
    std::ifstream in(fname);
    if (in.bad() || in.fail())
        throw exception(sstream() << "failed to open file '" << fname << "'");
    return parse_commands(env, ios, in, fname, use_exceptions, num_threads, cache, index);
}
}
