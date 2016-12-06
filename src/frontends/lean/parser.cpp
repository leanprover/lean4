/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <utility>
#include <string>
#include <limits>
#include <vector>
#include "util/utf8.h"
#include "util/interrupt.h"
#include "util/sstream.h"
#include "util/flet.h"
#include "util/lean_path.h"
#include "util/sexpr/option_declarations.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/find_fn.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/error_msgs.h"
#include "library/st_task_queue.h"
#include "library/module_mgr.h"
#include "library/export_decl.h"
#include "library/trace.h"
#include "library/exception.h"
#include "library/aliases.h"
#include "library/constants.h"
#include "library/annotation.h"
#include "library/private.h"
#include "library/locals.h"
#include "library/local_context.h"
#include "library/protected.h"
#include "library/choice.h"
#include "library/placeholder.h"
#include "library/deep_copy.h"
#include "library/module.h"
#include "library/scoped_ext.h"
#include "library/explicit.h"
#include "library/typed_expr.h"
#include "library/num.h"
#include "library/string.h"
#include "library/sorry.h"
#include "library/documentation.h"
#include "library/pp_options.h"
#include "library/noncomputable.h"
#include "library/scope_pos_info_provider.h"
#include "library/type_context.h"
#include "library/pattern_attribute.h"
#include "library/equations_compiler/equations.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/builtin_exprs.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/notation_cmd.h"
#include "frontends/lean/parser_pos_provider.h"
#include "frontends/lean/update_environment_exception.h"
#include "frontends/lean/local_ref_info.h"
#include "frontends/lean/opt_cmd.h"
#include "frontends/lean/builtin_cmds.h"
#include "frontends/lean/prenum.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/local_context_adapter.h"

#ifndef LEAN_DEFAULT_PARSER_SHOW_ERRORS
#define LEAN_DEFAULT_PARSER_SHOW_ERRORS true
#endif

#ifndef LEAN_DEFAULT_PARSER_PARALLEL_IMPORT
#define LEAN_DEFAULT_PARSER_PARALLEL_IMPORT false
#endif

namespace lean {
// ==========================================
// Parser configuration options
static name * g_parser_show_errors;
static name * g_parser_parallel_import;

bool get_parser_show_errors(options const & opts) {
    return opts.get_bool(*g_parser_show_errors, LEAN_DEFAULT_PARSER_SHOW_ERRORS);
}

// ==========================================

static name * g_anonymous_inst_name_prefix = nullptr;

parser::local_scope::local_scope(parser & p, bool save_options):
    m_p(p), m_env(p.env()) {
    m_p.push_local_scope(save_options);
}
parser::local_scope::local_scope(parser & p, environment const & env):
    m_p(p), m_env(p.env()) {
    m_p.m_env = env;
    m_p.push_local_scope();
}
parser::local_scope::local_scope(parser & p, optional<environment> const & env):
    m_p(p), m_env(p.env()) {
    if (env)
        m_p.m_env = *env;
    m_p.push_local_scope();
}
parser::local_scope::~local_scope() {
    m_p.pop_local_scope();
    m_p.m_env = m_env;
}

parser::quote_scope::quote_scope(parser & p, bool q):
    m_p(p), m_id_behavior(m_p.m_id_behavior), m_in_quote(q),
    m_saved_in_pattern(p.m_in_pattern) {
    m_p.m_in_pattern = false;
    if (q) {
        lean_assert(!m_p.m_in_quote);
        m_p.m_id_behavior = id_behavior::AllLocal;
        m_p.m_in_quote = true;
        m_p.push_local_scope(false);
        m_p.m_quote_stack = cons(m_p.mk_parser_scope(), m_p.m_quote_stack);
        m_p.clear_locals();
    } else {
        lean_assert(m_p.m_in_quote);
        lean_assert(m_p.m_quote_stack);
        m_p.m_id_behavior = id_behavior::ErrorIfUndef;
        m_p.push_local_scope(false);
        m_p.m_in_quote = false;
        m_p.restore_parser_scope(head(m_p.m_quote_stack));
    }
}

parser::quote_scope::~quote_scope() {
    m_p.m_in_pattern = m_saved_in_pattern;
    if (m_in_quote) {
        lean_assert(m_p.m_in_quote);
        m_p.m_in_quote = false;
        m_p.pop_local_scope();
        m_p.m_quote_stack = tail(m_p.m_quote_stack);
    } else {
        lean_assert(!m_p.m_in_quote);
        m_p.m_in_quote = true;
        m_p.pop_local_scope();
    }
    m_p.m_id_behavior = m_id_behavior;
}

parser::undef_id_to_const_scope::undef_id_to_const_scope(parser & p):
    flet<id_behavior>(p.m_id_behavior, id_behavior::AssumeConstantIfUndef) {}
parser::undef_id_to_local_scope::undef_id_to_local_scope(parser & p):
    flet<id_behavior>(p.m_id_behavior, id_behavior::AssumeLocalIfUndef) {}
parser::error_if_undef_scope::error_if_undef_scope(parser & p):
    flet<id_behavior>(p.m_id_behavior, id_behavior::ErrorIfUndef) {}
parser::all_id_local_scope::all_id_local_scope(parser & p):
    flet<id_behavior>(p.m_id_behavior, id_behavior::AllLocal) {}

static name * g_tmp_prefix = nullptr;

void parser::enable_show_goal(pos_info const & pos) {
    m_stop_at = true;
    m_stop_at_line = pos.first;
    m_ios.set_options(set_show_goal(m_ios.get_options(), pos.first, pos.second));
}

void parser::enable_show_info(pos_info const & pos) {
    m_stop_at = true;
    m_stop_at_line = pos.first;
    m_info_at = true;
    m_info_at_line = pos.first;
    m_info_at_col = pos.second;
    m_ios.set_options(set_show_info(m_ios.get_options(), pos.first, pos.second));
}

parser::parser(environment const & env, io_state const & ios,
               module_loader const & import_fn,
               std::istream & strm, std::string const & file_name,
               bool use_exceptions,
               std::shared_ptr<snapshot const> const & s, snapshot_vector * sv):
    m_env(env), m_ios(ios), m_verbose(true),
    m_use_exceptions(use_exceptions),
    m_import_fn(import_fn),
    m_file_name(file_name),
    m_scanner(strm, m_file_name.c_str(), s ? s->m_pos : pos_info(1, 0)),
    m_imports_parsed(false),
    m_snapshot_vector(sv) {
    if (s) {
        m_env                = s->m_env;
        m_ios.set_options(s->m_options);
        m_old_buckets_from_snapshot = s->m_sub_buckets;
        m_local_level_decls  = s->m_lds;
        m_local_decls        = s->m_eds;
        m_level_variables    = s->m_lvars;
        m_variables          = s->m_vars;
        m_include_vars       = s->m_include_vars;
        m_imports_parsed     = s->m_imports_parsed;
        m_parser_scope_stack = s->m_parser_scope_stack;
    }
    m_ignore_noncomputable = false;
    m_profile     = ios.get_options().get_bool("profiler", false);
    m_in_quote = false;
    m_in_pattern = false;
    m_has_params = false;
    m_id_behavior  = id_behavior::ErrorIfUndef;
    m_found_errors = false;
    m_used_sorry   = false;
    m_info_at = false;
    m_stop_at = false;
    updt_options();
    m_next_tag_idx  = 0;
    m_next_inst_idx = 1;
    m_curr = scanner::token_kind::Identifier;
    protected_call([&]() { scan(); },
                   [&]() { sync_command(); });
}

parser::~parser() {
}

void parser::scan() {
    if (m_info_at) {
        m_curr = m_scanner.scan(m_env);
        pos_info p = pos();
        if (p.first == m_info_at_line) {
            if (curr_is_identifier()) {
                name const & id = get_name_val();
                if (p.second <= m_info_at_col && m_info_at_col < p.second + id.utf8_size()) {
                    auto out = mk_message(INFORMATION);
                    bool ok = true;
                    try {
                        bool show_value = false;
                        ok = print_id_info(*this, out, id, show_value, p);
                    } catch (exception &) {
                        ok = false;
                    }
                    if (!ok)
                        out << "unknown identifier '" << id << "'\n";
                    out.report();
                    m_info_at = false;
                }
            } else if (curr_is_keyword()) {
                name const & tk = get_token_info().token();
                if (p.second <= m_info_at_col && m_info_at_col < p.second + tk.utf8_size()) {
                    auto out = mk_message(INFORMATION);
                    try {
                        print_token_info(*this, out, tk);
                    } catch (exception &) {}
                    out.report();
                    m_info_at = false;
                }
            } else if (curr_is_command()) {
                name const & tk = get_token_info().token();
                if (p.second <= m_info_at_col && m_info_at_col < p.second + tk.utf8_size()) {
                    (mk_message(INFORMATION) << "'" << tk << "' is a command").report();
                    m_info_at = false;
                }
            }
        }
    } else {
        m_curr = m_scanner.scan(m_env);
    }
}

expr parser::mk_sorry(pos_info const & p) {
    m_used_sorry = true;
    m_ignore_noncomputable = true;
    {
#ifndef LEAN_IGNORE_SORRY
        // TODO(Leo): remove the #ifdef.
        // The compilation option LEAN_IGNORE_SORRY is a temporary hack for the nightly builds
        // We use it to avoid a buch of warnings on cdash.
        (mk_message(p, WARNING) << "using 'sorry'").report();
#endif
    }
    return save_pos(::lean::mk_sorry(), p);
}

void parser::updt_options() {
    m_verbose        = get_verbose(m_ios.get_options());
    m_show_errors    = get_parser_show_errors(m_ios.get_options());
}

void parser::throw_parser_exception(char const * msg, pos_info p) {
    throw parser_exception(msg, get_stream_name().c_str(), p.first, p.second);
}

void parser::throw_nested_exception(throwable const & ex, pos_info p) {
    throw parser_nested_exception(std::shared_ptr<throwable>(ex.clone()),
                                  std::make_shared<parser_pos_provider>(m_pos_table, get_stream_name(), p));
}

#define CATCH(ShowError, ThrowError)                    \
m_found_errors = true;                                  \
if (!m_use_exceptions && m_show_errors) { ShowError ; } \
sync();                                                 \
if (m_use_exceptions) { ThrowError ; }

void parser::protected_call(std::function<void()> && f, std::function<void()> && sync) {
    try {
        try {
            f();
        } catch (update_environment_exception & ex) {
            m_env = ex.get_env();
            ex.get_exception().rethrow();
        }
    } catch (show_goal_exception) {
        throw;
    } catch (parser_exception & ex) {
        CATCH(report_message(ex), throw);
    } catch (parser_error & ex) {
        CATCH((mk_message(ex.m_pos, ERROR) << ex.get_msg()).report(),
              throw_parser_exception(ex.what(), ex.m_pos));
    } catch (interrupted) {
        throw;
    } catch (throwable & ex) {
        CATCH(mk_message(m_last_cmd_pos, ERROR).set_exception(ex).report(),
              throw_nested_exception(ex, m_last_cmd_pos));
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

name parser::mk_anonymous_inst_name() {
    name n = g_anonymous_inst_name_prefix->append_after(m_next_inst_idx);
    m_next_inst_idx++;
    return n;
}

bool parser::is_anonymous_inst_name(name const & n) const {
    return
        n.is_atomic() &&
        n.is_string() &&
        strlen(n.get_string()) >= strlen(g_anonymous_inst_name_prefix->get_string()) &&
        memcmp(n.get_string(), g_anonymous_inst_name_prefix->get_string(), strlen(g_anonymous_inst_name_prefix->get_string())) == 0;
}

expr parser::save_pos(expr e, pos_info p) {
    auto t = get_tag(e);
    if (!m_pos_table.contains(t))
        m_pos_table.insert(t, p);
    return e;
}

expr parser::update_pos(expr e, pos_info p) {
    auto t = get_tag(e);
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
    case expr_kind::Let:
        return save_pos(update_let(e,
                                   copy_with_new_pos(let_type(e), p),
                                   copy_with_new_pos(let_value(e), p),
                                   copy_with_new_pos(let_body(e), p)),
                        p);
    case expr_kind::Macro: {
        buffer<expr> args;
        for (unsigned i = 0; i < macro_num_args(e); i++)
            args.push_back(copy_with_new_pos(macro_arg(e, i), p));
        return save_pos(update_macro(e, args.size(), args.data()), p);
    }}
    lean_unreachable(); // LCOV_EXCL_LINE
}

pos_info parser::pos_of(expr const & e, pos_info default_pos) const {
    tag t = e.get_tag();
    if (t == nulltag)
        return default_pos;
    if (auto it = m_pos_table.find(t))
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

void parser::check_token_or_id_next(name const & tk, char const * msg) {
    if (!curr_is_token_or_id(tk))
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

static void check_not_internal(name const & id, pos_info const & p) {
    if (is_internal_name(id))
        throw parser_error(sstream() << "invalid declaration name '" << id << "', identifiers starting with '_' are reserved to the system", p);
}

name parser::check_decl_id_next(char const * msg) {
    auto p  = pos();
    name id = check_id_next(msg);
    check_not_internal(id, p);
    return id;
}

name parser::check_atomic_id_next(char const * msg) {
    auto p  = pos();
    name id = check_id_next(msg);
    if (!id.is_atomic())
        throw parser_error(msg, p);
    return id;
}

name parser::check_atomic_decl_id_next(char const * msg) {
    auto p  = pos();
    name id = check_atomic_id_next(msg);
    check_not_internal(id, p);
    return id;
}

expr parser::mk_app(expr fn, expr arg, pos_info const & p) {
    return save_pos(::lean::mk_app(fn, arg), p);
}

expr parser::mk_app(expr fn, buffer<expr> const & args, pos_info const & p) {
    expr r = fn;
    for (expr const & arg : args) {
        r = mk_app(r, arg, p);
    }
    return r;
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

parser_scope parser::mk_parser_scope(optional<options> const & opts) {
    return parser_scope(opts, m_level_variables, m_variables, m_include_vars,
                        m_undef_ids.size(), m_next_inst_idx, m_has_params,
                        m_local_level_decls, m_local_decls);
}

void parser::restore_parser_scope(parser_scope const & s) {
    if (s.m_options) {
        m_ios.set_options(*s.m_options);
        updt_options();
    }
    m_local_level_decls  = s.m_local_level_decls;
    m_local_decls        = s.m_local_decls;
    m_level_variables    = s.m_level_variables;
    m_variables          = s.m_variables;
    m_include_vars       = s.m_include_vars;
    m_has_params         = s.m_has_params;
    m_next_inst_idx      = s.m_next_inst_idx;
}

void parser::push_local_scope(bool save_options) {
    optional<options> opts;
    if (save_options)
        opts = m_ios.get_options();
    m_parser_scope_stack = cons(mk_parser_scope(opts), m_parser_scope_stack);
}

void parser::pop_local_scope() {
    if (!m_parser_scope_stack) {
        throw parser_error("invalid 'end', there is no open namespace/section", pos());
    }
    auto s = head(m_parser_scope_stack);
    restore_parser_scope(s);
    m_undef_ids.shrink(s.m_num_undef_ids);
    m_parser_scope_stack = tail(m_parser_scope_stack);
}

void parser::clear_locals() {
    m_local_level_decls = local_level_decls();
    m_local_decls       = local_expr_decls();
}

void parser::add_local_level(name const & n, level const & l, bool is_variable) {
    if (m_env.is_universe(n))
        throw exception(sstream() << "invalid universe declaration, '" << n << "' shadows a global universe");
    if (m_local_level_decls.contains(n))
        throw exception(sstream() << "invalid universe declaration, '" << n << "' shadows a local universe");
    m_local_level_decls.insert(n, l);
    if (is_variable) {
        lean_assert(is_param(l));
        m_level_variables.insert(n);
    }
}

void parser::add_local_expr(name const & n, expr const & p, bool is_variable) {
    m_local_decls.insert(n, p);
    if (is_variable) {
        lean_assert(is_local(p));
        m_variables.insert(local_pp_name(p));
    }
}

environment parser::add_local_ref(environment const & env, name const & n, expr const & ref) {
    add_local_expr(n, ref, false);
    if (is_as_atomic(ref)) {
        buffer<expr> args;
        expr f = get_app_args(get_as_atomic_arg(ref), args);
        if (is_explicit(f))
            f = get_explicit_arg(f);
        if (is_constant(f)) {
            return save_local_ref_info(env, const_name(f), ref);
        } else {
            return env;
        }
    } else if (is_constant(ref) && const_levels(ref)) {
        return save_local_ref_info(env, const_name(ref), ref);
    } else {
        return env;
    }
}

static void check_no_metavars(name const & n, expr const & e) {
    lean_assert(is_local(e));
    if (has_metavar(e)) {
        throw generic_exception(none_expr(), [=](formatter const & fmt) {
                format r("failed to add declaration '");
                r += format(n);
                r += format("' to local context, type has metavariables");
                r += pp_until_meta_visible(fmt, mlocal_type(e));
                return r;
            });
    }
}

void parser::add_variable(name const & n, expr const & v) {
    lean_assert(is_local(v));
    check_no_metavars(n, v);
    add_local_expr(n, v, true);
}

void parser::add_parameter(name const & n, expr const & p) {
    lean_assert(is_local(p));
    check_no_metavars(n, p);
    add_local_expr(n, p, false);
    m_has_params = true;
}

bool parser::update_local_binder_info(name const & n, binder_info const & bi) {
    auto it = get_local(n);
    if (!it || !is_local(*it)) return false;

    buffer<pair<name, expr>> entries;
    to_buffer(m_local_decls.get_entries(), entries);
    std::reverse(entries.begin(), entries.end());
    unsigned idx = m_local_decls.find_idx(n);
    lean_assert(idx > 0);
    lean_assert_eq(entries[idx-1].second, *it);

    buffer<expr> old_locals;
    buffer<expr> new_locals;
    old_locals.push_back(*it);
    expr new_l = update_local(*it, bi);
    entries[idx-1].second = new_l;
    new_locals.push_back(new_l);

    for (unsigned i = idx; i < entries.size(); i++) {
        expr const & curr_e = entries[i].second;
        expr r = is_local(curr_e) ? mlocal_type(curr_e) : curr_e;
        if (std::any_of(old_locals.begin(), old_locals.end(), [&](expr const & l) { return depends_on(r, l); })) {
            r  = replace_locals(r, old_locals, new_locals);
            if (is_local(curr_e)) {
                expr new_e = update_mlocal(curr_e, r);
                entries[i].second = new_e;
                old_locals.push_back(curr_e);
                new_locals.push_back(new_e);
            } else {
                entries[i].second = r;
            }
        }
    }
    auto new_entries = m_local_decls.get_entries();
    unsigned sz_to_updt = entries.size() - idx + 1;
    for (unsigned i = 0; i < sz_to_updt; i++)
        new_entries = tail(new_entries); // remove entries that will be updated
    for (unsigned i = idx-1; i < entries.size(); i++)
        new_entries = cons(entries[i], new_entries);
    m_local_decls.update_entries(new_entries);
    return true;
}

unsigned parser::get_local_index(name const & n) const {
    return m_local_decls.find_idx(n);
}

void parser::get_include_variables(buffer<expr> & vars) const {
    m_include_vars.for_each([&](name const & n) {
            vars.push_back(*get_local(n));
        });
}

list<expr> parser::locals_to_context() const {
    return map_filter<expr>(m_local_decls.get_entries(),
                            [](pair<name, expr> const & p, expr & out) {
                                out = p.second;
                                return is_local(p.second);
                            });
}

static unsigned g_level_add_prec = 10;

unsigned parser::get_small_nat() {
    mpz val = get_num_val().get_numerator();
    lean_assert(val >= 0);
    if (!val.is_unsigned_int())
        throw parser_error("invalid level expression, value does not fit in a machine integer", pos());
    return val.get_unsigned_int();
}

std::string parser::parse_string_lit() {
    std::string v = get_str_val();
    next();
    return v;
}

name_map<std::string> parser::parse_kv_pairs() {
    name_map<std::string> pairs;
    return pairs;
    // check_token_next(get_lparen_tk(), "invalid attribute options, '(' expected");
    // bool comma = false;
    // while (!p.curr_is_token(get_rparen_tk())) {
    //     p.next();
    //     if (comma) {
    //         check_token_next(get_comma_tk(), "invalid attribute options, ',' expected");
    //     } else {
    //         comma = true;
    //     }
    //
    //     std::string k = parse_string_lit();
    //     std::cout << "parsed: " << k << std::endl;
    // }
    // check_token_next(get_rparen_tk(), "invalid attribute options, ')' expected");
    // return pairs;
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
    double r =get_num_val().get_double();
    next();
    return r;
}

static level lift(level l, unsigned k) {
    while (k > 0) {
        k--;
        l = mk_succ(l);
    }
    return l;
}

unsigned parser::curr_level_lbp() const {
    if (curr_is_token(get_add_tk()))
        return g_level_add_prec;
    else
        return 0;
}

level parser::parse_max_imax(bool is_max) {
    auto p = pos();
    next();
    buffer<level> lvls;
    while (curr_is_identifier() || curr_is_numeral() || curr_is_token(get_lparen_tk())) {
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

    for (name const & ns : get_namespaces(m_env)) {
        auto new_id = ns + id;
        if (!ns.is_anonymous() && m_env.is_universe(new_id))
            return mk_global_univ(new_id);
    }

    if (m_env.is_universe(id))
        return mk_global_univ(id);
    if (auto it = get_level_alias(m_env, id))
        return mk_global_univ(*it);
    throw parser_error(sstream() << "unknown universe '" << id << "'", p);
}

level parser::parse_level_nud() {
    if (curr_is_token_or_id(get_max_tk())) {
        return parse_max_imax(true);
    } else if (curr_is_token_or_id(get_imax_tk())) {
        return parse_max_imax(false);
    } else if (curr_is_token_or_id(get_placeholder_tk())) {
        next();
        return mk_level_placeholder();
    } else if (curr_is_token(get_lparen_tk())) {
        next();
        level l = parse_level();
        check_token_next(get_rparen_tk(), "invalid level expression, ')' expected");
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
    if (curr_is_token(get_add_tk())) {
        next();
        if (curr_is_numeral()) {
            unsigned k = parse_small_nat();
            return lift(left, k);
        } else {
            throw parser_error("invalid level expression, right hand side of '+' "
                               "(aka universe lift operator) must be a numeral", p);
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

pair<expr, level_param_names> parser::elaborate(metavar_context & mctx, local_context_adapter const & adapter,
                                                expr const & e, bool check_unassigned) {
    expr tmp_e  = adapter.translate_to(e);
    pair<expr, level_param_names> r =
        ::lean::elaborate(m_env, get_options(), mctx, adapter.lctx(), tmp_e, check_unassigned);
    expr new_e = r.first;
    new_e      = adapter.translate_from(new_e);
    return mk_pair(new_e, r.second);
}

pair<expr, level_param_names> parser::elaborate(metavar_context & mctx, list<expr> const & lctx, expr const & e, bool check_unassigned) {
    local_context_adapter adapter(lctx);
    return elaborate(mctx, adapter, e, check_unassigned);
}

pair<expr, level_param_names> parser::elaborate(metavar_context & mctx, expr const & e, bool check_unassigned) {
    local_context_adapter adapter(m_local_decls);
    return elaborate(mctx, adapter, e, check_unassigned);
}

pair<expr, level_param_names> parser::elaborate(expr const & e) {
    metavar_context mctx;
    return elaborate(mctx, list<expr>(), e, true);
}

pair<expr, level_param_names> parser::elaborate(list<expr> const & ctx, expr const & e) {
    metavar_context mctx;
    return elaborate(mctx, ctx, e, true);
}

pair<expr, level_param_names> parser::elaborate_type(list<expr> const & ctx, expr const & e) {
    metavar_context mctx;
    expr Type  = copy_tag(e, mk_sort(mk_level_placeholder()));
    expr new_e = copy_tag(e, mk_typed_expr(Type, e));
    return elaborate(mctx, ctx, new_e, true);
}

pair<expr, level_param_names> parser::elaborate_type(metavar_context & mctx, expr const & e) {
    expr Type  = copy_tag(e, mk_sort(mk_level_placeholder()));
    expr new_e = copy_tag(e, mk_typed_expr(Type, e));
    return elaborate(mctx, new_e, true);
}

[[ noreturn ]] void throw_invalid_open_binder(pos_info const & pos) {
    throw parser_error("invalid binder, '(', '{', '[', '{{', '⦃' or identifier expected", pos);
}

/**
   \brief Return an optional binder_info object based on the current token
      - '('          : default
      - '{'          : implicit
      - '{{' or '⦃'  : strict implicit
      - '['          : inst_implicit (i.e., implicit argument that should be
                       synthesized using type class resolution)

   If simple_only, then only `(` is considered
*/
optional<binder_info> parser::parse_optional_binder_info(bool simple_only) {
    if (curr_is_token(get_lparen_tk())) {
        next();
        return some(binder_info());
    } else if (simple_only) {
        return optional<binder_info>();
    } else if (curr_is_token(get_lcurly_tk())) {
        next();
        if (curr_is_token(get_lcurly_tk())) {
            next();
            return some(mk_strict_implicit_binder_info());
        } else {
            return some(mk_implicit_binder_info());
        }
    } else if (curr_is_token(get_lbracket_tk())) {
        next();
        return some(mk_inst_implicit_binder_info());
    } else if (curr_is_token(get_ldcurly_tk())) {
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
binder_info parser::parse_binder_info(bool simple_only) {
    auto p = pos();
    if (auto bi = parse_optional_binder_info(simple_only)) {
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
     - inst implicit   : consume ']'
*/
void parser::parse_close_binder_info(optional<binder_info> const & bi) {
    if (!bi) {
        return;
    } else if (bi->is_implicit()) {
        check_token_next(get_rcurly_tk(), "invalid declaration, '}' expected");
    } else if (bi->is_inst_implicit()) {
        check_token_next(get_rbracket_tk(), "invalid declaration, ']' expected");
    } else if (bi->is_strict_implicit()) {
        if (curr_is_token(get_rcurly_tk())) {
            next();
            check_token_next(get_rcurly_tk(), "invalid declaration, '}' expected");
        } else {
            check_token_next(get_rdcurly_tk(), "invalid declaration, '⦄' expected");
        }
    } else {
        check_token_next(get_rparen_tk(), "invalid declaration, ')' expected");
    }
}

/** \brief Parse <tt>ID ':' expr</tt>, where the expression represents the type of the identifier. */
expr parser::parse_binder_core(binder_info const & bi, unsigned rbp) {
    auto p  = pos();
    name id = check_atomic_id_next("invalid binder, atomic identifier expected");
    expr type;
    if (curr_is_token(get_colon_tk())) {
        next();
        type = parse_expr(rbp);
    } else {
        type = save_pos(mk_expr_placeholder(), p);
    }
    return save_pos(mk_local(id, type, bi), p);
}

expr parser::parse_binder(unsigned rbp) {
    if (curr_is_identifier()) {
        return parse_binder_core(binder_info(), rbp);
    } else {
        bool simple_only = false;
        binder_info bi = parse_binder_info(simple_only);
        rbp = 0;
        auto r = parse_binder_core(bi, rbp);
        parse_close_binder_info(bi);
        return r;
    }
}

/* Lean allow binders of the form <tt>ID_1 ... ID_n 'op' S</tt>
   Where 'op' is an infix operator, and s an expression (i.e., "collection").
   This notation expands to:
     (ID_1 ... ID_n : _) (H_1 : ID_1 'op' S) ... (H_n : ID_n 'op' S)

   This method return true if the next token is an infix operator,
   and populates r with the locals above.
*/
bool parser::parse_binder_collection(buffer<pair<pos_info, name>> const & names, binder_info const & bi, buffer<expr> & r) {
    if (!curr_is_keyword())
        return false;
    name tk = get_token_info().value();
    list<pair<notation::transition, parse_table>> trans_list = led().find(tk);
    if (length(trans_list) != 1)
        return false;
    pair<notation::transition, parse_table> const & p = head(trans_list);
    list<notation::accepting> const & acc_lst = p.second.is_accepting();
    if (length(acc_lst) != 1)
        return false; // no overloading
    notation::accepting const & acc = head(acc_lst);
    lean_assert(!acc.get_postponed());
    expr pred     = acc.get_expr();
    unsigned rbp  = p.first.get_action().rbp();
    next(); // consume tk
    expr S        = parse_expr(rbp);
    unsigned old_sz = r.size();
    /* Add (ID_1 ... ID_n : _) to r */
    for (auto p : names) {
        expr arg_type = save_pos(mk_expr_placeholder(), p.first);
        expr local = save_pos(mk_local(p.second, arg_type, bi), p.first);
        add_local(local);
        r.push_back(local);
    }
    /* Add (H_1 : ID_1 'op' S) ... (H_n : ID_n 'op' S) */
    unsigned i = old_sz;
    for (auto p : names) {
        expr ID      = r[i];
        expr args[2] = {ID, S};
        expr ID_op_S = instantiate_rev(pred, 2, args);
        expr local = save_pos(mk_local("H", ID_op_S, bi), p.first);
        add_local(local);
        r.push_back(local);
        i++;
    }
    return true;
}

/**
   \brief Parse <tt>ID ... ID ':' expr</tt>, where the expression
   represents the type of the identifiers.
*/
void parser::parse_binder_block(buffer<expr> & r, binder_info const & bi, unsigned rbp) {
    buffer<pair<pos_info, name>> names;
    while (curr_is_identifier()) {
        auto p = pos();
        names.emplace_back(p, check_atomic_id_next("invalid binder, atomic identifier expected"));
    }
    if (names.empty())
        throw parser_error("invalid binder, identifier expected", pos());
    optional<expr> type;
    if (curr_is_token(get_colon_tk())) {
        next();
        type = parse_expr(rbp);
    } else if (parse_binder_collection(names, bi, r)) {
        return;
    }
    for (auto p : names) {
        expr arg_type = type ? *type : save_pos(mk_expr_placeholder(), p.first);
        expr local = save_pos(mk_local(p.second, arg_type, bi), p.first);
        add_local(local);
        r.push_back(local);
    }
}

expr parser::parse_inst_implicit_decl() {
    binder_info bi = mk_inst_implicit_binder_info();
    auto id_pos = pos();
    name id;
    expr type;
    if (curr_is_identifier()) {
        id = get_name_val();
        next();
        if (curr_is_token(get_colon_tk())) {
            next();
            type = parse_expr();
        } else {
            expr left    = id_to_expr(id, id_pos);
            id           = mk_anonymous_inst_name();
            unsigned rbp = 0;
            while (rbp < curr_lbp()) {
                left = parse_led(left);
            }
            type = left;
        }
    } else {
        id   = mk_anonymous_inst_name();
        type = parse_expr();
    }
    expr local = save_pos(mk_local(id, type, bi), id_pos);
    add_local(local);
    return local;
}


void parser::parse_inst_implicit_decl(buffer<expr> & r) {
    expr local = parse_inst_implicit_decl();
    r.push_back(local);
}

void parser::parse_binders_core(buffer<expr> & r, buffer<notation_entry> * nentries,
                                bool & last_block_delimited, unsigned rbp, bool simple_only) {
    while (true) {
        if (curr_is_identifier()) {
            parse_binder_block(r, binder_info(), rbp);
            last_block_delimited = false;
        } else {
            optional<binder_info> bi = parse_optional_binder_info(simple_only);
            if (bi) {
                rbp = 0;
                last_block_delimited = true;
                if (bi->is_inst_implicit()) {
                    parse_inst_implicit_decl(r);
                } else {
                    if (simple_only || !parse_local_notation_decl(nentries))
                        parse_binder_block(r, *bi, rbp);
                }
                parse_close_binder_info(bi);
            } else {
                return;
            }
        }
    }
}

local_environment parser::parse_binders(buffer<expr> & r, buffer<notation_entry> * nentries,
                                        bool & last_block_delimited, bool allow_empty, unsigned rbp,
                                        bool simple_only) {
    flet<environment>      save1(m_env, m_env); // save environment
    flet<local_expr_decls> save2(m_local_decls, m_local_decls);
    unsigned old_sz = r.size();
    parse_binders_core(r, nentries, last_block_delimited, rbp, simple_only);
    if (!allow_empty && old_sz == r.size())
        throw_invalid_open_binder(pos());
    return local_environment(m_env);
}

bool parser::parse_local_notation_decl(buffer<notation_entry> * nentries) {
    if (curr_is_notation_decl(*this)) {
        parser::in_notation_ctx ctx(*this);
        buffer<token_entry> new_tokens;
        bool overload    = false;
        bool allow_local = true;
        auto ne = ::lean::parse_notation(*this, overload, new_tokens, allow_local);
        for (auto const & te : new_tokens)
            m_env = add_token(m_env, te);
        if (nentries) nentries->push_back(ne);
        m_env = add_notation(m_env, ne);
        return true;
    } else {
        return false;
    }
}

void parser::process_postponed(buffer<expr> const & args, bool is_left,
                               buffer<notation::action_kind> const & kinds,
                               buffer<list<expr>> const & nargs,
                               buffer<expr> const & ps,
                               buffer<pair<unsigned, pos_info>> const & scoped_info,
                               list<notation::action> const & postponed,
                               pos_info const & p,
                               buffer<expr> & new_args) {
    unsigned args_idx = 0;
    if (is_left) {
        new_args.push_back(args[0]);
        args_idx = 1;
    }
    unsigned kinds_idx  = 0;
    unsigned nargs_idx  = 0;
    unsigned scoped_idx = 0;
    list<notation::action> it = postponed;
    for (; kinds_idx < kinds.size(); kinds_idx++, args_idx++) {
        auto k = kinds[kinds_idx];
        switch (k) {
        case notation::action_kind::Exprs: {
            if (!it || head(it).kind() != k || nargs_idx >= nargs.size())
                throw exception("ill-formed parsing tables");
            notation::action const & a = head(it);
            buffer<expr> r_args;
            to_buffer(nargs[nargs_idx], r_args);
            nargs_idx++;
            expr rec = copy_with_new_pos(a.get_rec(), p);
            expr r;
            if (a.is_fold_right()) {
                if (a.get_initial()) {
                    r = instantiate_rev(copy_with_new_pos(*a.get_initial(), p), new_args.size(), new_args.data());
                } else {
                    r = r_args.back();
                    r_args.pop_back();
                }
                unsigned i = r_args.size();
                while (i > 0) {
                    --i;
                    new_args.push_back(r_args[i]);
                    new_args.push_back(r);
                    r = instantiate_rev(rec, new_args.size(), new_args.data());
                    new_args.pop_back(); new_args.pop_back();
                }
            } else {
                unsigned fidx = 0;
                if (a.get_initial()) {
                    r = instantiate_rev(copy_with_new_pos(*a.get_initial(), p), new_args.size(), new_args.data());
                } else {
                    r = r_args[0];
                    fidx++;
                }
                for (unsigned i = fidx; i < r_args.size(); i++) {
                    new_args.push_back(r_args[i]);
                    new_args.push_back(r);
                    r = instantiate_rev(rec, new_args.size(), new_args.data());
                    new_args.pop_back(); new_args.pop_back();
                }
            }
            new_args.push_back(r);
            it = tail(it);
            break;
        }
        case notation::action_kind::ScopedExpr: {
            if (!it || head(it).kind() != k || scoped_idx >= scoped_info.size())
                throw exception("ill-formed parsing tables");
            expr r = args[args_idx];
            notation::action const & a = head(it);
            bool no_cache = false;
            unsigned ps_sz      = scoped_info[scoped_idx].first;
            pos_info binder_pos = scoped_info[scoped_idx].second;
            scoped_idx++;
            if (is_var(a.get_rec(), 0)) {
                if (a.use_lambda_abstraction())
                    r = Fun(ps_sz, ps.data(), r, no_cache);
                else
                    r = Pi(ps_sz, ps.data(), r, no_cache);
                r = rec_save_pos(r, binder_pos);
            } else {
                expr rec = copy_with_new_pos(a.get_rec(), p);
                unsigned i = ps_sz;
                while (i > 0) {
                    --i;
                    expr const & l = ps[i];
                    if (a.use_lambda_abstraction())
                        r = Fun(l, r, no_cache);
                    else
                        r = Pi(l, r, no_cache);
                    r = save_pos(r, binder_pos);
                    new_args.push_back(r);
                    r = instantiate_rev(rec, new_args.size(), new_args.data());
                    new_args.pop_back();
                }
            }
            new_args.push_back(r);
            it = tail(it);
            break;
        }
        default:
            new_args.push_back(args[args_idx]);
            break;
        }
    }
}

// Return true iff the current token is the terminator of some Exprs action, and store the matching pair in r
static bool curr_is_terminator_of_exprs_action(parser const & p, list<pair<notation::transition, parse_table>> const & lst, pair<notation::transition, parse_table> const * & r) {
    for (auto const & pr : lst) {
        notation::action const & a = pr.first.get_action();
        if (a.kind() == notation::action_kind::Exprs &&
            a.get_terminator() &&
            p.curr_is_token(name(utf8_trim(a.get_terminator()->to_string())))) {
            r = &pr;
            return true;
        }
    }
    return false;
}

// Return true iff \c lst contains a Skip action, and store the matching pair in r.
static bool has_skip(list<pair<notation::transition, parse_table>> const & lst, pair<notation::transition, parse_table> const * & r) {
    for (auto const & p : lst) {
        notation::action const & a = p.first.get_action();
        if (a.kind() == notation::action_kind::Skip) {
            r = &p;
            return true;
        }
    }
    return false;
}

static pair<notation::transition, parse_table> const * get_non_skip(list<pair<notation::transition, parse_table>> const & lst) {
    for (auto const & p : lst) {
        notation::action const & a = p.first.get_action();
        if (a.kind() != notation::action_kind::Skip)
            return &p;
    }
    return nullptr;
}

expr parser::parse_notation(parse_table t, expr * left) {
    lean_assert(curr() == scanner::token_kind::Keyword);
    auto p = pos();
    buffer<expr>                     args;
    buffer<notation::action_kind>    kinds;
    buffer<list<expr>>               nargs; // nary args
    buffer<expr>                     ps;
    buffer<pair<unsigned, pos_info>> scoped_info; // size of ps and binder_pos for scoped_exprs
    // Invariants:
    //  args.size()  == kinds.size() if not left
    //  args.size()  == kinds.size()+1 if left
    //  nargs.size() == number of Exprs in kinds
    //  scoped_info.size() == number of Scoped_Exprs in kinds
    bool has_Exprs = false;
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
        pair<notation::transition, parse_table> const * curr_pair = nullptr;
        if (tail(r)) {
            // There is more than one possible actions.
            // In the current implementation, we support the following possible cases (Skip, Expr), (Skip, Exprs) amd (Skip, ScopedExpr)
            next();
            if (curr_is_terminator_of_exprs_action(*this, r, curr_pair)) {
                lean_assert(curr_pair->first.get_action().kind() == notation::action_kind::Exprs);
            } else if (has_skip(r, curr_pair) && !curr_starts_expr()) {
                lean_assert(curr_pair->first.get_action().kind() == notation::action_kind::Skip);
            } else {
                curr_pair = get_non_skip(r);
            }
        } else {
            // there is only one possible action
            curr_pair = &head(r);
            if (curr_pair->first.get_action().kind() != notation::action_kind::Ext)
                next();
        }
        lean_assert(curr_pair);
        notation::action const & a = curr_pair->first.get_action();
        switch (a.kind()) {
        case notation::action_kind::Skip:
            break;
        case notation::action_kind::Expr:
            args.push_back(parse_expr(a.rbp()));
            kinds.push_back(a.kind());
            break;
        case notation::action_kind::Exprs: {
            buffer<expr> r_args;
            auto terminator = a.get_terminator();
            if (terminator)
                terminator = some(name(utf8_trim(terminator->to_string()))); // remove padding
            if (!terminator || !curr_is_token(*terminator)) {
                r_args.push_back(parse_expr(a.rbp()));
                name sep = utf8_trim(a.get_sep().to_string()); // remove padding
                while (curr_is_token(sep)) {
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
            has_Exprs = true;
            args.push_back(expr()); // placeholder
            kinds.push_back(a.kind());
            nargs.push_back(to_list(r_args));
            break;
        }
        case notation::action_kind::Binder:
            binder_pos = pos();
            ps.push_back(parse_binder(a.rbp()));
            break;
        case notation::action_kind::Binders:
            binder_pos = pos();
            lenv = parse_binders(ps, a.rbp());
            break;
        case notation::action_kind::ScopedExpr: {
            expr r   = parse_scoped_expr(ps, lenv, a.rbp());
            args.push_back(r);
            kinds.push_back(a.kind());
            scoped_info.push_back(mk_pair(ps.size(), binder_pos));
            break;
        }
        case notation::action_kind::Ext:
            args.push_back(a.get_parse_fn()(*this, args.size(), args.data(), p));
            kinds.push_back(a.kind());
            break;
        }
        t = curr_pair->second;
    }
    list<notation::accepting> const & as = t.is_accepting();
    if (is_nil(as)) {
        if (p == pos())
            throw parser_error(sstream() << "invalid expression", pos());
        else
            throw parser_error(sstream() << "invalid expression starting at " << p.first << ":" << p.second, pos());
    }
    lean_assert(left  || args.size() == kinds.size());
    lean_assert(!left || args.size() == kinds.size() + 1);
    /*
      IF there are multiple choices and Exprs was not used, we create a lambda for each choice.
      In this case, we copy args to actual_args and store local constants in args. */
    buffer<expr> actual_args;
    buffer<expr> cs;
    bool create_lambdas = length(as) > 1 && !has_Exprs;
    if (create_lambdas) {
        name x("x");
        unsigned idx = 1;
        for (expr & arg : args) {
            actual_args.push_back(arg);
            arg = mk_local(mk_fresh_name(), x.append_after(idx), mk_expr_placeholder(), binder_info());
            idx++;
        }
    }
    for (notation::accepting const & a : as) {
        expr r = copy_with_new_pos(a.get_expr(), p);
        list<notation::action> const & postponed = a.get_postponed();
        if (postponed) {
            buffer<expr> new_args;
            process_postponed(args, left, kinds, nargs, ps, scoped_info, postponed, p, new_args);
            lean_assert(!args.empty());
            r = instantiate_rev(r, new_args.size(), new_args.data());
        } else {
            lean_assert(nargs.empty() && scoped_info.empty());
            r = instantiate_rev(r, args.size(), args.data());
        }
        if (create_lambdas) {
            bool no_cache = false;
            r = rec_save_pos(eta_reduce(Fun(args, r, no_cache)), p);
        }
        cs.push_back(r);
    }
    expr r = save_pos(mk_choice(cs.size(), cs.data()), p);
    if (create_lambdas) {
        r = rec_save_pos(::lean::mk_app(r, actual_args), p);
    }
    return r;
}

expr parser::parse_nud_notation() {
    return parse_notation(nud(), nullptr);
}

expr parser::parse_inaccessible() {
    auto p = pos();
    next();
    expr t = parse_expr(get_max_prec());
    return save_pos(mk_inaccessible(t), p);
}

expr parser::parse_placeholder() {
    auto p = pos();
    next();
    return save_pos(mk_explicit_expr_placeholder(), p);
}

expr parser::parse_anonymous_var_pattern() {
    auto p = pos();
    next();
    expr t = mk_local(mk_fresh_name(), "_x", mk_expr_placeholder(), binder_info());
    return save_pos(t, p);
}

expr parser::parse_led_notation(expr left) {
    if (led().find(get_token_info().value())) {
        return parse_notation(led(), &left);
    } else {
        return mk_app(left, parse_expr(get_max_prec()), pos_of(left));
    }
}

/**
   \brief Auxiliary object for converting pattern_or_expr into a pattern.
   The main points are:

   1- Collect all pattern variables. Each pattern variable can only be
      "declared" once. That is, the following equation is not valid

        definition f : nat -> nat -> nat
        | a a := a

   2- We do not collect pattern variables inside inaccessible term such as:
              .(f a)


      Remark: An inaccessible term may contain a reference to a variable defined
      later. Here is an example:

      inductive imf {A B : Type} (f : A → B) : B → Type
      | mk : ∀ (a : A), imf (f a)

      definition inv {A B : Type} (f : A → B) : ∀ (b : B), imf f b → A
      | .(f a) (imf.mk .f a)  := a

      The 'a' in .(f a) is a reference to the variable 'a' being declared at
      (imf.mk .f a)

   3- The type in type ascriptions is implicitly marked as inaccessible.

   4- An inaccessible term cannot be the function in an application.
      Example: (.f a) is not allowed.

   5- In a pattern (f a), f must be a constructor or a constant tagged with the
      [pattern] attribute */
struct to_pattern_fn {
    parser &       m_parser;
    buffer<expr> & m_new_locals;
    name_map<expr> m_locals_map; // local variable name --> its interpretation
    expr_map<expr> m_anonymous_vars; // for _


    to_pattern_fn(parser & p, buffer<expr> & new_locals):
        m_parser(p), m_new_locals(new_locals) {}

    environment const & env() { return m_parser.env(); }

    /* Return true iff the constant n may occur in a pattern */
    bool is_pattern_constant(name const & n) {
        if (inductive::is_intro_rule(env(), n))
            return true;
        if (has_pattern_attribute(env(), n))
            return true;
        return false;
    }

    void collect_new_local(expr const & e) {
        name const & n = local_pp_name(e);
        bool resolve_only = true;
        expr new_e = m_parser.id_to_expr(n, m_parser.pos_of(e), resolve_only);
        if (is_as_atomic(new_e)) {
            new_e = get_app_fn(get_as_atomic_arg(new_e));
            if (is_explicit(new_e))
                new_e = get_explicit_arg(new_e);
        }

        if (is_constant(new_e) && is_pattern_constant(const_name(new_e))) {
            m_locals_map.insert(n, new_e);
            return;
        } else if (is_choice(new_e)) {
            bool all_pattern_constant = true;
            bool has_pattern_constant = false;
            for (unsigned i = 0; i < get_num_choices(new_e); i++) {
                expr const & c = get_choice(new_e, i);
                if (is_constant(c) && is_pattern_constant(const_name(c)))
                    has_pattern_constant = true;
                else
                    all_pattern_constant = false;
            }
            if (all_pattern_constant) {
                m_locals_map.insert(n, new_e);
                return;
            } else if (has_pattern_constant) {
                throw parser_error(sstream() << "invalid pattern, '" << e << "' is overloaded, "
                                   << "and some interpretations may occur in patterns and others not "
                                   << "(solution: use fully qualified names)",
                                   m_parser.pos_of(e));
            } else {
                // assume e is a variable shadowing overloaded constants
            }
        }
        if (!n.is_atomic()) {
            throw parser_error("invalid pattern: variable, constructor or constant tagged as pattern expected",
                               m_parser.pos_of(e));
        }
        if (m_locals_map.contains(n)) {
            throw parser_error(sstream() << "invalid pattern, '" << n << "' already appeared in this pattern",
                               m_parser.pos_of(e));
        }
        m_locals_map.insert(n, e);
        m_new_locals.push_back(e);
    }

    void collect_new_locals(expr const & e, bool skip_main_fn) {
        if (is_typed_expr(e)) {
            collect_new_locals(get_typed_expr_expr(e), false);
        } else if (is_prenum(e) || is_string_macro(e)) {
            // do nothing
        } else if (is_inaccessible(e)) {
            // do nothing
        } else if (is_placeholder(e)) {
            expr r = copy_tag(e, mk_local(mk_fresh_name(), "_x", copy_tag(e, mk_expr_placeholder()), binder_info()));
            m_new_locals.push_back(r);
            m_anonymous_vars.insert(mk_pair(e, r));
        } else if (is_app(e)) {
            collect_new_locals(app_fn(e), skip_main_fn);
            collect_new_locals(app_arg(e), false);
        } else if (is_local(e)) {
            if (skip_main_fn) {
                // do nothing
            } else {
                collect_new_local(e);
            }
        } else if (is_anonymous_constructor(e)) {
            buffer<expr> args;
            get_app_args(get_annotation_arg(e), args);
            for (expr const & arg : args)
                collect_new_locals(arg, skip_main_fn);
        } else if (is_annotation(e)) {
            collect_new_locals(get_annotation_arg(e), skip_main_fn);
        } else if (is_constant(e) && is_pattern_constant(const_name(e))) {
            // do nothing
        } else {
            throw parser_error("invalid pattern, must be an application, "
                               "constant, variable, type ascription or inaccessible term",
                               m_parser.pos_of(e));
        }
    }

    expr to_expr(expr const & e) {
        return replace(e, [&](expr const & e, unsigned) {
                if (is_local(e)) {
                    if (auto r = m_locals_map.find(local_pp_name(e)))
                        return some_expr(*r);
                    else
                        return some_expr(m_parser.patexpr_to_expr(e));
                }
                return none_expr();
            });
    }

    expr visit(expr const & e) {
        if (is_typed_expr(e)) {
            expr new_v = visit(get_typed_expr_expr(e));
            expr new_t = to_expr(get_typed_expr_type(e));
            return copy_tag(e, mk_typed_expr(new_t, new_v));
        } else if (is_prenum(e) || is_string_macro(e)) {
            return e;
        } else if (is_inaccessible(e)) {
            return to_expr(e);
        } else if (is_placeholder(e)) {
            return m_anonymous_vars.find(e)->second;
        } else if (is_app(e)) {
            if (is_inaccessible(app_fn(e))) {
                throw parser_error("invalid inaccessible annotation, it cannot be used around functions in applications",
                                   m_parser.pos_of(e));
            }
            expr new_f = visit(app_fn(e));
            expr new_a = visit(app_arg(e));
            return update_app(e, new_f, new_a);
        } else if (is_local(e)) {
            if (auto r = m_locals_map.find(local_pp_name(e)))
                return *r;
            else
                return e;
        } else if (is_anonymous_constructor(e)) {
            buffer<expr> args;
            expr a  = get_annotation_arg(e);
            expr fn = get_app_args(a, args);
            lean_assert(is_placeholder(fn));
            for (expr & arg : args)
                arg = visit(arg);
            expr r = copy_tag(a, mk_app(fn, args));
            return copy_tag(e, mk_anonymous_constructor(r));
        } else if (is_annotation(e)) {
            return copy_tag(e, mk_annotation(get_annotation_kind(e), visit(get_annotation_arg(e))));
        } else if (is_constant(e) && is_pattern_constant(const_name(e))) {
            return e;
        } else {
            throw parser_error("invalid pattern, must be an application, "
                               "constant, variable, type ascription or inaccessible term",
                               m_parser.pos_of(e));
        }
    }

    expr operator()(expr const & e, bool skip_main_fn) {
        collect_new_locals(e, skip_main_fn);
        expr r = visit(e);
        return r;
    }
};

expr parser::patexpr_to_pattern(expr const & pat_or_expr, bool skip_main_fn, buffer<expr> & new_locals) {
    undef_id_to_local_scope scope(*this);
    return to_pattern_fn(*this, new_locals)(pat_or_expr, skip_main_fn);
}

expr parser::parse_pattern_or_expr(unsigned rbp) {
    all_id_local_scope scope(*this);
    flet<bool> set_in_pattern(m_in_pattern, true);
    return parse_expr(rbp);
}

expr parser::parse_pattern(std::function<expr(parser &)> const & fn, buffer<expr> & new_locals) {
    all_id_local_scope scope(*this);
    flet<bool> set_in_pattern(m_in_pattern, true);
    expr r = fn(*this);
    return patexpr_to_pattern(r, false, new_locals);
}

expr parser::patexpr_to_expr(expr const & pat_or_expr) {
    error_if_undef_scope scope(*this);
    return replace(pat_or_expr, [&](expr const & e, unsigned) {
            if (is_local(e)) {
                return some_expr(id_to_expr(local_pp_name(e), pos_of(e), true));
            } else if (is_inaccessible(e) && is_placeholder(get_annotation_arg(e))) {
                return some_expr(get_annotation_arg(e));
            } else {
                return none_expr();
            }
        });
}

expr parser::id_to_expr(name const & id, pos_info const & p, bool resolve_only) {
    buffer<level> lvl_buffer;
    levels ls;
    bool explicit_levels = false;
    if (!resolve_only && curr_is_token(get_llevel_curly_tk())) {
        next();
        explicit_levels = true;
        while (!curr_is_token(get_rcurly_tk())) {
            lvl_buffer.push_back(parse_level());
        }
        next();
        ls = to_list(lvl_buffer.begin(), lvl_buffer.end());
    }

    if (!explicit_levels && m_id_behavior == id_behavior::AllLocal) {
        return save_pos(mk_local(id, save_pos(mk_expr_placeholder(), p)), p);
    }

    // locals
    if (auto it1 = m_local_decls.find(id)) {
        if (ls && m_id_behavior != id_behavior::AssumeConstantIfUndef)
            throw parser_error("invalid use of explicit universe parameter, identifier is a variable, "
                               "parameter or a constant bound to parameters in a section", p);
        return copy_with_new_pos(*it1, p);
    }

    for (name const & ns : get_namespaces(m_env)) {
        auto new_id = ns + id;
        if (!ns.is_anonymous() && m_env.find(new_id) &&
            (!id.is_atomic() || !is_protected(m_env, new_id))) {
            return save_pos(mk_constant(new_id, ls), p);
        }
    }

    if (!id.is_atomic()) {
        name new_id = id;
        new_id = remove_root_prefix(new_id);
        if (m_env.find(new_id)) {
            return save_pos(mk_constant(new_id, ls), p);
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
    }
    if (!r) {
        if (m_id_behavior == id_behavior::AssumeConstantIfUndef) {
            r = save_pos(mk_constant(get_namespace(m_env) + id, ls), p);
        } else if (m_id_behavior == id_behavior::AssumeLocalIfUndef) {
            expr local = mk_local(id, save_pos(mk_expr_placeholder(), p));
            if (!resolve_only)
                m_undef_ids.push_back(local);
            r = save_pos(local, p);
        }
    }
    if (!r)
        throw parser_error(sstream() << "unknown identifier '" << id << "'", p);
    return *r;
}

list<name> parser::to_constants(name const & id, char const * msg, pos_info const & p) const {
    buffer<name> rs;

    std::function<void(expr const & e)> extract_names = [&](expr const & e) {
        if (in_section(m_env) && is_as_atomic(e)) {
            extract_names(get_app_fn(get_as_atomic_arg(e)));
        } else if (is_explicit(e)) {
            extract_names(get_explicit_arg(e));
        } else if (is_choice(e)) {
            for (unsigned i = 0; i < get_num_choices(e); i++)
                extract_names(get_choice(e, i));
        } else if (is_constant(e)) {
            rs.push_back(const_name(e));
        } else {
            throw parser_error(msg, p);
        }
    };

    // locals
    if (auto it1 = m_local_decls.find(id)) {
        extract_names(*it1);
        return to_list(rs);
    }

    for (name const & ns : get_namespaces(m_env)) {
        auto new_id = ns + id;
        if (!ns.is_anonymous() && m_env.find(new_id) &&
            (!id.is_atomic() || !is_protected(m_env, new_id))) {
            return to_list(new_id);
        }
    }

    if (!id.is_atomic()) {
        name new_id = id;
        new_id = remove_root_prefix(new_id);
        if (m_env.find(new_id))
            return to_list(new_id);
    }

    buffer<expr> alts;
    // globals
    if (m_env.find(id))
        rs.push_back(id);
    // aliases
    auto as = get_expr_aliases(m_env, id);
    for (name const & n : as) {
        rs.push_back(n);
    }

    if (rs.empty()) {
        throw parser_error(sstream() << "unknown identifier '" << id << "'", p);
    }

    return to_list(rs);
}

name parser::to_constant(name const & id, char const * msg, pos_info const & p) {
    return head(to_constants(id, msg, p));
}

name parser::check_constant_next(char const * msg) {
    auto p  = pos();
    name id = check_id_next(msg);
    return to_constant(id, msg, p);
}

expr parser::parse_id() {
    auto p  = pos();
    name id = get_name_val();
    next();
    return id_to_expr(id, p);
}

expr parser::parse_numeral_expr(bool user_notation) {
    auto p = pos();
    mpz n = get_num_val().get_numerator();
    next();
    list<expr> vals;
    if (user_notation)
        vals = get_mpz_notation(m_env, n);
    if (!vals) {
        return save_pos(mk_prenum(n), p);
    } else {
        buffer<expr> cs;
        cs.push_back(save_pos(mk_prenum(n), p));
        for (expr const & c : vals)
            cs.push_back(copy_with_new_pos(c, p));
        if (cs.size() == 1)
            return cs[0];
        else
            return save_pos(mk_choice(cs.size(), cs.data()), p);
    }
}

expr parser::parse_decimal_expr() {
    auto p  = pos();
    mpq val = get_num_val();
    next();
    expr num = save_pos(mk_prenum(val.get_numerator()), p);
    if (val.get_denominator() == 1) {
        return num;
    } else {
        expr den = save_pos(mk_prenum(val.get_denominator()), p);
        expr div = save_pos(mk_constant(get_div_name()), p);
        return save_pos(lean::mk_app(div, num, den), p);
    }
}

expr parser::parse_string_expr() {
    std::string v = get_str_val();
    next();
    return from_string(v);
}

expr parser::parse_char_expr() {
    auto p = pos();
    std::string v = get_str_val();
    lean_assert(v.size() == 1);
    next();
    return mk_app(save_pos(mk_constant(get_char_of_nat_name()), p),
                  save_pos(mk_prenum(mpz(static_cast<unsigned>(v[0]))), p),
                  p);
}

expr parser::parse_nud() {
    switch (curr()) {
    case scanner::token_kind::Keyword:
        if (m_in_pattern && curr_is_token(get_period_tk()))
            return parse_inaccessible();
        else if (curr_is_token(get_placeholder_tk()))
            return parse_placeholder();
        else
            return parse_nud_notation();
    case scanner::token_kind::Identifier:  return parse_id();
    case scanner::token_kind::Numeral:     return parse_numeral_expr();
    case scanner::token_kind::Decimal:     return parse_decimal_expr();
    case scanner::token_kind::String:      return parse_string_expr();
    case scanner::token_kind::Char:        return parse_char_expr();
    default: throw parser_error("invalid expression, unexpected token", pos());
    }
}

// Return true if the current token can be the beginning of an expression
bool parser::curr_starts_expr() {
    switch (curr()) {
    case scanner::token_kind::Keyword:
        return !is_nil(nud().find(get_token_info().value()));
    case scanner::token_kind::Identifier:
    case scanner::token_kind::Numeral:
    case scanner::token_kind::Decimal:
    case scanner::token_kind::String:
    default:
        return false;
    }
}

expr parser::parse_led(expr left) {
    if (is_sort(left) && is_one_placeholder(sort_level(left)) &&
        (curr_is_numeral() || curr_is_identifier() || curr_is_token(get_lparen_tk()) || curr_is_token(get_placeholder_tk()))) {
        level l = parse_level(get_max_prec());
        return copy_tag(left, update_sort(left, l));
    } else {
        switch (curr()) {
        case scanner::token_kind::Keyword: return parse_led_notation(left);
        default: return mk_app(left, parse_expr(get_max_prec()), pos_of(left));
        }
    }
}

unsigned parser::curr_lbp() const {
    switch (curr()) {
    case scanner::token_kind::Keyword:
        if (m_in_pattern && curr_is_token(get_period_tk()))
            return get_max_prec();
        else
            return get_token_info().expr_precedence();
    case scanner::token_kind::CommandKeyword: case scanner::token_kind::Eof:
    case scanner::token_kind::QuotedSymbol:   case scanner::token_kind::DocBlock:
    case scanner::token_kind::ModDocBlock:
        return 0;
    case scanner::token_kind::Identifier:     case scanner::token_kind::Numeral:
    case scanner::token_kind::Decimal:        case scanner::token_kind::String:
    case scanner::token_kind::Char:
        return get_max_prec();
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

pair<optional<name>, expr> parser::parse_id_tk_expr(name const & tk, unsigned rbp) {
    if (curr_is_identifier()) {
        auto id_pos = pos();
        name id = get_name_val();
        next();
        if (curr_is_token(tk)) {
            next();
            return mk_pair(optional<name>(id), parse_expr(rbp));
        } else {
            expr left = id_to_expr(id, id_pos);
            while (rbp < curr_lbp()) {
                left = parse_led(left);
            }
            return mk_pair(optional<name>(), left);
        }
    } else {
        return mk_pair(optional<name>(), parse_expr(rbp));
    }
}

pair<optional<name>, expr> parser::parse_qualified_expr(unsigned rbp) {
    return parse_id_tk_expr(get_colon_tk(), rbp);
}

pair<optional<name>, expr> parser::parse_optional_assignment(unsigned rbp) {
    return parse_id_tk_expr(get_assign_tk(), rbp);
}

expr parser::parse_scoped_expr(unsigned num_ps, expr const * ps, local_environment const & lenv, unsigned rbp) {
    local_scope scope(*this);
    m_env = lenv;
    for (unsigned i = 0; i < num_ps; i++)
        add_local(ps[i]);
    return parse_expr(rbp);
}

expr parser::parse_expr_with_env(local_environment const & lenv, unsigned rbp) {
    flet<environment> set_env(m_env, lenv);
    return parse_expr(rbp);
}

expr parser::parse_tactic(unsigned) {
    lean_unreachable();
}

/** \brief Helper class for creating type context only if needed */
class lazy_type_context : public abstract_type_context {
    environment m_env;
    options     m_opts;
    std::unique_ptr<type_context> m_ctx;
    type_context & ctx() {
        if (!m_ctx)
            m_ctx.reset(new type_context(m_env, m_opts));
        return *m_ctx;
    }
public:
    lazy_type_context(environment const & env, options const & opts):m_env(env), m_opts(opts) {}
    virtual ~lazy_type_context() {}
    virtual environment const & env() const override { return const_cast<lazy_type_context*>(this)->ctx().env(); }
    virtual expr whnf(expr const & e) override { return ctx().whnf(e); }
    virtual bool is_def_eq(expr const & e1, expr const & e2) override { return ctx().is_def_eq(e1, e2); }
    virtual expr infer(expr const & e) override { return ctx().infer(e); }
    virtual expr check(expr const & e) override { return ctx().check(e); }
    virtual optional<expr> is_stuck(expr const & e) override { return ctx().is_stuck(e); }
};

static name_set * g_documentable_cmds = nullptr;

static bool support_docummentation(name const & n) {
    return g_documentable_cmds->contains(n);
}

void parser::parse_command() {
    lean_assert(curr() == scanner::token_kind::CommandKeyword);
    m_last_cmd_pos = pos();
    name cmd_name = get_token_info().value();
    m_cmd_token = get_token_info().token();
    if (m_doc_string && !support_docummentation(cmd_name)) {
        next();
        reset_doc_string();
        throw parser_error(sstream() << "command '" << cmd_name << "' does not support doc string", m_last_cmd_pos);
    }
    if (auto it = cmds().find(cmd_name)) {
        lazy_type_context tc(m_env, get_options());
        scope_global_ios scope1(m_ios);
        scope_trace_env  scope2(m_env, m_ios.get_options(), tc);
        scope_traces_as_messages traces_as_messages(get_stream_name(), pos());
        if (is_notation_cmd(cmd_name)) {
            in_notation_ctx ctx(*this);
            if (it->get_skip_token())
                next();
            m_env = it->get_fn()(*this);
        } else {
            if (it->get_skip_token())
                next();
            m_env = it->get_fn()(*this);
        }
    } else {
        reset_doc_string();
        auto p = pos();
        next();
        throw parser_error(sstream() << "unknown command '" << cmd_name << "'", p);
    }
    reset_doc_string();
}

void parser::parse_doc_block() {
    m_doc_string = m_scanner.get_str_val();
    next();
}

void parser::parse_mod_doc_block() {
    m_env = add_module_doc_string(m_env, m_scanner.get_str_val());
    next();
}

void parser::check_no_doc_string() {
    if (m_doc_string) {
        auto p = pos();
        next();
        reset_doc_string();
        throw parser_error("invalid occurrence of doc string immediately before current position", p);
    }
}

void parser::reset_doc_string() {
    m_doc_string = optional<std::string>();
}

#if defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
#endif

std::vector<module_name> parser::parse_imports(unsigned & fingerprint) {
    m_last_cmd_pos = pos();
    bool prelude     = false;
    if (curr_is_token(get_prelude_tk())) {
        next();
        prelude = true;
    }
    std::vector<module_name> imports;
    if (!prelude) {
        imports.push_back({ "init", optional<unsigned>() });
    }
    while (curr_is_token(get_import_tk())) {
        m_last_cmd_pos = pos();
        next();
        while (true) {
            optional<unsigned> k;
            unsigned h = 0;
            while (true) {
                if (curr_is_token(get_period_tk())) {
                    next();
                    if (!k) {
                        k = 0;
                    } else {
                        k = *k + 1;
                        h++;
                    }
                } else if (curr_is_token(get_ellipsis_tk())) {
                    next();
                    if (!k) {
                        k = 2;
                        h = 2;
                    } else {
                        k = *k + 3;
                        h += 3;
                    }
                } else {
                    break;
                }
            }
            if (!curr_is_identifier())
                break;
            name f            = get_name_val();
            fingerprint       = hash(fingerprint, f.hash());
            if (k) {
                fingerprint = hash(fingerprint, h);
            }
            imports.push_back({ f, k });
            next();
        }
    }
    return imports;
}

void parser::process_imports() {
    unsigned fingerprint = 0;
    auto imports = parse_imports(fingerprint);

    for (auto & n : imports) {
        try {
            m_env = import_module(m_env, m_file_name, n, m_import_fn);
        } catch (exception & ex) {
            m_found_errors = true;
            parser_exception error((sstream() << "invalid import '" << n.m_name << "'").str(),
                                   m_file_name.c_str(), m_last_cmd_pos.first, m_last_cmd_pos.second);
            if (!m_use_exceptions && m_show_errors)
                report_message(error);
            if (m_use_exceptions)
                throw error;
        }
    }

    m_env = update_fingerprint(m_env, fingerprint);
    m_env = activate_export_decls(m_env, {}); // explicitly activate exports in root namespace
    m_env = replay_export_decls_core(m_env, m_ios);
    if (has_sorry(m_env)) {
#ifndef LEAN_IGNORE_SORRY
        // TODO(Leo): remove the #ifdef.
        // The compilation option LEAN_IGNORE_SORRY is a temporary hack for the nightly builds
        // We use it to avoid a buch of warnings on cdash.
        (mk_message(m_last_cmd_pos, WARNING) << "imported file uses 'sorry'").report();
#endif
    }
    m_imports_parsed = true;
}

std::vector<module_name> parser::get_imports() {
    scope_pos_info_provider scope1(*this);
    unsigned fingerprint;
    return parse_imports(fingerprint);
}

bool parser::parse_commands() {
    // We disable hash-consing while parsing to make sure the pos-info are correct.
    scoped_expr_caching disable(false);
    scoped_set_distinguishing_pp_options set(get_distinguishing_pp_options());
    scope_pos_info_provider scope1(*this);
    scope_message_context scope_parser_msgs("_parser", m_old_buckets_from_snapshot);
    try {
        bool done = false;
        // Only parse imports when we are at the beginning, i.e. not when starting from a snapshot.
        if (!m_imports_parsed) {
            scope_message_context scope_msg_ctx("imports");
            scoped_info_manager scope_infom( // TODO(gabriel): separate flag for snapshots/infos?
                    m_snapshot_vector ? scope_msg_ctx.enable_info_manager(m_file_name)
                                      : nullptr);
            protected_call([&]() { process_imports(); }, [&]() { sync_command(); });
        }
        while (!done) {
            save_snapshot(scope_parser_msgs);
            if (m_stop_at && pos().first > m_stop_at_line) {
                throw interrupt_parser();
            }
            scoped_task_context scope_task_ctx(get_current_module(), pos());
            scope_message_context scope_msg_ctx;
            scoped_info_manager scope_infom( // TODO(gabriel): separate flag for snapshots/infos?
                    m_snapshot_vector ? scope_msg_ctx.enable_info_manager(m_file_name)
                                      : nullptr);
            protected_call([&]() {
                    check_interrupted();
                    switch (curr()) {
                    case scanner::token_kind::CommandKeyword:
                        if (curr_is_token(get_end_tk())) {
                            check_no_doc_string();
                        }
                        parse_command();
                        break;
                    case scanner::token_kind::DocBlock:
                        check_no_doc_string();
                        parse_doc_block();
                        break;
                    case scanner::token_kind::ModDocBlock:
                        check_no_doc_string();
                        parse_mod_doc_block();
                        break;
                    case scanner::token_kind::Eof:
                        check_no_doc_string();
                        done = true;
                        break;
                    case scanner::token_kind::Keyword:
                        check_no_doc_string();
                        if (curr_is_token(get_period_tk())) {
                            next();
                            break;
                        }
                    default:
                        throw parser_error("command expected", pos());
                    }
                },
                [&]() { sync_command(); });
        }
        scope_message_context scope_msg_ctx("end");
        if (has_open_scopes(m_env)) {
            m_found_errors = true;
            if (!m_use_exceptions && m_show_errors)
                (mk_message(ERROR) << "invalid end of module, expecting 'end'").report();
            else if (m_use_exceptions)
                throw_parser_exception("invalid end of module, expecting 'end'", pos());
        }
        save_snapshot(scope_parser_msgs);
    } catch (interrupt_parser) {
        while (has_open_scopes(m_env))
            m_env = pop_scope_core(m_env, m_ios);
    }
    return !m_found_errors;
}

bool parser::curr_is_command_like() const {
    switch (curr()) {
    case scanner::token_kind::CommandKeyword:
        return true;
    case scanner::token_kind::Eof:
        return true;
    case scanner::token_kind::Keyword:
        return curr_is_token(get_period_tk());
    default:
        return false;
    }
}

void parser::save_snapshot(scope_message_context & smc) {
    if (!m_snapshot_vector)
        return;
    if (m_snapshot_vector->empty() || m_snapshot_vector->back()->m_pos != m_scanner.get_pos_info()) {
        m_snapshot_vector->push_back(std::make_shared<snapshot>(
                m_env, smc.get_sub_buckets(), m_local_level_decls, m_local_decls,
                m_level_variables, m_variables, m_include_vars,
                m_ios.get_options(), m_imports_parsed, m_parser_scope_stack, m_scanner.get_pos_info()));
    }
}

optional<pos_info> parser::get_pos_info(expr const & e) const {
    tag t = e.get_tag();
    if (t == nulltag)
        return optional<pos_info>();
    if (auto it = m_pos_table.find(t))
        return optional<pos_info>(*it);
    else
        return optional<pos_info>();
}

pos_info parser::get_some_pos() const {
    return m_last_cmd_pos;
}

char const * parser::get_file_name() const {
    return get_stream_name().c_str();
}

message_builder parser::mk_message(pos_info const &p, message_severity severity) {
    std::shared_ptr<abstract_type_context> tc = std::make_shared<type_context>(env(), get_options());
    return message_builder(this, tc, env(), ios(), get_file_name(), p, severity);
}
message_builder parser::mk_message(message_severity severity) {
    return mk_message(pos(), severity);
}

bool parse_commands(environment & env, io_state & ios, char const * fname) {
    st_task_queue tq;
    scope_global_task_queue scope(&tq);
    fs_module_vfs vfs;
    vfs.m_modules_to_load_from_source.insert(std::string(fname));
    module_mgr mod_mgr(&vfs, &get_global_message_buffer(), env, ios);

    auto mod = mod_mgr.get_module(fname)->m_result.get();

    lean_assert(mod.m_env);
    env = *mod.m_env;

    return mod.m_ok;
}

void initialize_parser() {
    g_parser_show_errors     = new name{"parser", "show_errors"};
    g_parser_parallel_import = new name{"parser", "parallel_import"};
    register_bool_option(*g_parser_show_errors, LEAN_DEFAULT_PARSER_SHOW_ERRORS,
                         "(lean parser) display error messages in the regular output channel");
    register_bool_option(*g_parser_parallel_import, LEAN_DEFAULT_PARSER_PARALLEL_IMPORT,
                         "(lean parser) import modules in parallel");
    g_tmp_prefix = new name(name::mk_internal_unique_name());
    g_anonymous_inst_name_prefix = new name("_inst");
    g_documentable_cmds = new name_set();

    g_documentable_cmds->insert("definition");
    g_documentable_cmds->insert("theorem");
    g_documentable_cmds->insert("constant");
    g_documentable_cmds->insert("axiom");
    g_documentable_cmds->insert("meta");
    g_documentable_cmds->insert("mutual");
    g_documentable_cmds->insert("@[");
    g_documentable_cmds->insert("protected");
    g_documentable_cmds->insert("class");
    g_documentable_cmds->insert("instance");
    g_documentable_cmds->insert("inductive");
    g_documentable_cmds->insert("structure");
}

void finalize_parser() {
    delete g_anonymous_inst_name_prefix;
    delete g_tmp_prefix;
    delete g_parser_show_errors;
    delete g_parser_parallel_import;
    delete g_documentable_cmds;
}
}
