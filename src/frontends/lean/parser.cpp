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
#include "util/sexpr/option_declarations.h"
#include "kernel/for_each_fn.h"
#include "kernel/replace_fn.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "kernel/error_msgs.h"
#include "library/parser_nested_exception.h"
#include "library/aliases.h"
#include "library/constants.h"
#include "library/private.h"
#include "library/locals.h"
#include "library/protected.h"
#include "library/choice.h"
#include "library/placeholder.h"
#include "library/deep_copy.h"
#include "library/module.h"
#include "library/scoped_ext.h"
#include "library/explicit.h"
#include "library/typed_expr.h"
#include "library/let.h"
#include "library/num.h"
#include "library/string.h"
#include "library/sorry.h"
#include "library/flycheck.h"
#include "library/pp_options.h"
#include "library/noncomputable.h"
#include "library/error_handling/error_handling.h"
#include "library/tactic/expr_to_tactic.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/parser_bindings.h"
#include "frontends/lean/notation_cmd.h"
#include "frontends/lean/elaborator.h"
#include "frontends/lean/info_annotation.h"
#include "frontends/lean/parse_rewrite_tactic.h"
#include "frontends/lean/update_environment_exception.h"
#include "frontends/lean/local_ref_info.h"
#include "frontends/lean/opt_cmd.h"
#include "frontends/lean/builtin_cmds.h"

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

bool get_parser_parallel_import(options const & opts) {
    return opts.get_bool(*g_parser_parallel_import, LEAN_DEFAULT_PARSER_PARALLEL_IMPORT);
}
// ==========================================

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

parser::undef_id_to_const_scope::undef_id_to_const_scope(parser & p):
    flet<undef_id_behavior>(p.m_undef_id_behavior, undef_id_behavior::AssumeConstant) {}
parser::undef_id_to_local_scope::undef_id_to_local_scope(parser & p):
    flet<undef_id_behavior>(p.m_undef_id_behavior, undef_id_behavior::AssumeLocal) {}

static name * g_tmp_prefix = nullptr;

void parser::init_stop_at(options const & opts) {
    unsigned col;
    m_info_at = false;
    m_stop_at = false;
    if (has_show_goal(opts, m_stop_at_line, col)) {
        m_stop_at      = true;
    } else if (has_show_hole(opts, m_stop_at_line, col)) {
        m_stop_at      = true;
    } else if (has_show_info(opts, m_info_at_line, m_info_at_col)) {
        m_info_at      = true;
        m_stop_at      = true;
        m_stop_at_line = m_info_at_line;
    }
}

parser::parser(environment const & env, io_state const & ios,
               std::istream & strm, char const * strm_name,
               bool use_exceptions, unsigned num_threads,
               snapshot const * s, snapshot_vector * sv, info_manager * im,
               keep_theorem_mode tmode):
    m_env(env), m_ios(ios), m_ngen(*g_tmp_prefix),
    m_verbose(true), m_use_exceptions(use_exceptions),
    m_scanner(strm, strm_name, s ? s->m_line : 1),
    m_theorem_queue(*this, num_threads > 1 ? num_threads - 1 : 0),
    m_snapshot_vector(sv), m_info_manager(im), m_cache(nullptr), m_index(nullptr) {
    m_local_decls_size_at_beg_cmd = 0;
    m_in_backtick = false;
    m_ignore_noncomputable = false;
    m_profile     = ios.get_options().get_bool("profile", false);
    init_stop_at(ios.get_options());
    if (num_threads > 1 && m_profile)
        throw exception("option --profile cannot be used when theorems are compiled in parallel");
    m_has_params = false;
    m_keep_theorem_mode = tmode;
    if (s) {
        m_ngen               = s->m_ngen;
        m_local_level_decls  = s->m_lds;
        m_local_decls        = s->m_eds;
        m_level_variables    = s->m_lvars;
        m_variables          = s->m_vars;
        m_include_vars       = s->m_include_vars;
        m_parser_scope_stack = s->m_parser_scope_stack;
    }
    m_num_threads = num_threads;
    m_undef_id_behavior = undef_id_behavior::Error;
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

void parser::scan() {
    if (m_info_at) {
        m_curr = m_scanner.scan(m_env);
        pos_info p = pos();
        if (p.first == m_info_at_line) {
            if (curr_is_identifier()) {
                name const & id = get_name_val();
                if (p.second <= m_info_at_col && m_info_at_col < p.second + id.utf8_size()) {
                    print_lean_info_header(regular_stream().get_stream());
                    bool ok = true;
                    try {
                        bool show_value = false;
                        ok = print_id_info(*this, id, show_value, p);
                    } catch (exception &) {
                        ok = false;
                    }
                    if (!ok)
                        regular_stream() << "unknown identifier '" << id << "'\n";
                    print_lean_info_footer(regular_stream().get_stream());
                    m_info_at = false;
                }
            } else if (curr_is_keyword()) {
                name const & tk = get_token_info().token();
                if (p.second <= m_info_at_col && m_info_at_col < p.second + tk.utf8_size()) {
                    print_lean_info_header(regular_stream().get_stream());
                    try {
                        print_token_info(*this, tk);
                    } catch (exception &) {}
                    print_lean_info_footer(regular_stream().get_stream());
                    m_info_at = false;
                }
            } else if (curr_is_command()) {
                name const & tk = get_token_info().token();
                if (p.second <= m_info_at_col && m_info_at_col < p.second + tk.utf8_size()) {
                    print_lean_info_header(regular_stream().get_stream());
                    regular_stream() << "'" << tk << "' is a command\n";
                    print_lean_info_footer(regular_stream().get_stream());
                    m_info_at = false;
                }
            }
        }
    } else {
        m_curr = m_scanner.scan(m_env);
    }
}

void parser::cache_definition(name const & n, expr const & pre_type, expr const & pre_value,
                              level_param_names const & ls, expr const & type, expr const & value) {
    if (m_cache)
        m_cache->add(m_env, n, pre_type, pre_value, ls, type, value);
}

auto parser::find_cached_definition(name const & n, expr const & pre_type, expr const & pre_value)
-> optional<std::tuple<level_param_names, expr, expr>> {
    if (m_cache)
        return m_cache->find(m_env, n, pre_type, pre_value);
    else
        return optional<std::tuple<level_param_names, expr, expr>>();
}

void parser::add_decl_index(name const & n, pos_info const & pos, name const & k, expr const & t) {
    if (m_index)
        m_index->add_decl(get_stream_name(), pos, n, k, t);
}

void parser::add_ref_index(name const & n, pos_info const & pos) {
    if (m_index)
        m_index->add_ref(get_stream_name(), pos, n);
}

void parser::add_abbrev_index(name const & a, name const & d) {
    if (m_index)
        m_index->add_abbrev(a, d);
}

bool parser::are_info_lines_valid(unsigned start_line, unsigned end_line) const {
    if (m_stop_at) {
        if (start_line <= m_stop_at_line && m_stop_at_line <= end_line)
            return false;
    }
    if (m_info_manager) {
        // we are tracking info
        for (unsigned i = start_line; i <= end_line; i++)
            if (m_info_manager->is_invalidated(i))
                return false;
    }
    return true;
}

void parser::remove_proof_state_info(pos_info const & start, pos_info const & end) {
    if (m_info_manager)
        m_info_manager->remove_proof_state_info(start.first, start.second, end.first, end.second);
}

expr parser::mk_sorry(pos_info const & p) {
    m_used_sorry = true;
    {
#ifndef LEAN_IGNORE_SORRY
        // TODO(Leo): remove the #ifdef.
        // The compilation option LEAN_IGNORE_SORRY is a temporary hack for the nightly builds
        // We use it to avoid a buch of warnings on cdash.
        flycheck_warning wrn(regular_stream());
        display_warning_pos(p.first, p.second);
        regular_stream() << " using 'sorry'" << endl;
#endif
    }
    return save_pos(::lean::mk_sorry(), p);
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

expr parser::mk_by_plus(expr const & t, pos_info const & pos) {
    if (!has_tactic_decls())
        throw parser_error("invalid 'by+' expression, tactic module has not been imported", pos);
    return save_pos(::lean::mk_by_plus(t), pos);
}

void parser::updt_options() {
    m_verbose     = get_verbose(m_ios.get_options());
    m_show_errors = get_parser_show_errors(m_ios.get_options());
    try {
        set_max_memory_megabyte(get_max_memory(m_ios.get_options()));
    } catch (exception&) {
        if (m_ios.get_options().contains(get_max_memory_opt_name())) {
            static bool m_already_reported = false;
            if (!m_already_reported) {
                m_already_reported = true;
                throw;
            }
        }
    }
}

void parser::display_warning_pos(unsigned line, unsigned pos) {
    ::lean::display_warning_pos(regular_stream(), get_stream_name().c_str(), line, pos);
}
void parser::display_warning_pos(pos_info p) { display_warning_pos(p.first, p.second); }

void parser::display_information_pos(pos_info pos) {
    ::lean::display_information_pos(regular_stream(), get_stream_name().c_str(), pos.first, pos.second);
}

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

void parser::display_error(throwable const & ex) {
    parser_pos_provider pos_provider(m_pos_table, get_stream_name(), m_last_cmd_pos);
    ::lean::display_error(regular_stream(), &pos_provider, ex);
}

void parser::display_error(script_exception const & ex) {
    parser_pos_provider pos_provider(m_pos_table, get_stream_name(), m_last_script_pos);
    ::lean::display_error(regular_stream(), &pos_provider, ex);
}

void parser::throw_parser_exception(char const * msg, pos_info p) {
    throw parser_exception(msg, get_stream_name().c_str(), p.first, p.second);
}

void parser::throw_nested_exception(throwable const & ex, pos_info p) {
    throw parser_nested_exception(std::shared_ptr<throwable>(ex.clone()),
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
        try {
            f();
        } catch (update_environment_exception & ex) {
            m_env = ex.get_env();
            ex.get_exception().rethrow();
        }
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
        if (m_use_exceptions || m_info_manager)
            throw;
    } catch (script_exception & ex) {
        reset_interrupt();
        CATCH(display_error(ex), throw_nested_exception(ex, m_last_script_pos));
    } catch (throwable & ex) {
        reset_interrupt();
        CATCH(display_error(ex), throw_nested_exception(ex, m_last_cmd_pos));
    }
}

void parser::sync_command() {
    // Keep consuming tokens until we find a Command or End-of-file
    while (curr() != scanner::token_kind::CommandKeyword && curr() != scanner::token_kind::Eof)
        next();
    if (m_info_manager)
        m_info_manager->commit_upto(m_scanner.get_line()+1, false);
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
    if (is_let_value(e))
        return e;
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

void parser::push_local_scope(bool save_options) {
    optional<options> opts;
    if (save_options)
        opts = m_ios.get_options();
    m_parser_scope_stack = cons(parser_scope_stack_elem(opts, m_level_variables, m_variables, m_include_vars,
                                                        m_undef_ids.size(), m_has_params, m_local_level_decls,
                                                        m_local_decls),
                                m_parser_scope_stack);
}

void parser::pop_local_scope() {
    if (!m_parser_scope_stack) {
        throw parser_error("invalid 'end', there is no open namespace/section", pos());
    }
    auto s = head(m_parser_scope_stack);
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
    m_undef_ids.shrink(s.m_num_undef_ids);
    m_parser_scope_stack = tail(m_parser_scope_stack);
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

void parser::add_parameter(name const & n, expr const & p) {
    lean_assert(is_local(p));
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
            r  = instantiate_rev(abstract_locals(r, old_locals.size(), old_locals.data()),
                                 new_locals.size(), new_locals.data());
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

unsigned parser::get_local_level_index(name const & n) const {
    return m_local_level_decls.find_idx(n);
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
    if (curr_is_token(get_cup_tk()))
        return g_level_cup_prec;
    else if (curr_is_token(get_add_tk()))
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
    if (curr_is_token(get_cup_tk())) {
        next();
        level right = parse_level(g_level_cup_prec);
        return mk_max(left, right);
    } else if (curr_is_token(get_add_tk())) {
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

elaborator_context parser::mk_elaborator_context(environment const & env, local_level_decls const & lls,
                                                 pos_info_provider const & pp) {
    return elaborator_context(env, m_ios, lls, &pp, m_info_manager, true);
}

std::tuple<expr, level_param_names> parser::elaborate_relaxed(expr const & e, list<expr> const & ctx) {
    bool check_unassigned = false;
    bool ensure_type      = false;
    bool nice_mvar_names  = true;
    parser_pos_provider pp = get_pos_provider();
    elaborator_context env = mk_elaborator_context(pp, check_unassigned);
    auto r = ::lean::elaborate(env, ctx, e, ensure_type, nice_mvar_names);
    m_pre_info_manager.clear();
    return r;
}

std::tuple<expr, level_param_names> parser::elaborate(expr const & e, list<expr> const & ctx) {
    bool check_unassigned = true;
    bool ensure_type      = false;
    parser_pos_provider pp = get_pos_provider();
    elaborator_context env = mk_elaborator_context(pp, check_unassigned);
    auto r = ::lean::elaborate(env, ctx, e, ensure_type);
    m_pre_info_manager.clear();
    return r;
}

std::tuple<expr, level_param_names> parser::elaborate_type(expr const & e, list<expr> const & ctx, bool clear_pre_info) {
    bool check_unassigned = true;
    bool ensure_type      = true;
    parser_pos_provider pp = get_pos_provider();
    elaborator_context env = mk_elaborator_context(pp, check_unassigned);
    auto r = ::lean::elaborate(env, ctx, e, ensure_type);
    if (clear_pre_info)
        m_pre_info_manager.clear();
    return r;
}

std::tuple<expr, level_param_names> parser::elaborate_at(environment const & env, expr const & e) {
    parser_pos_provider pp = get_pos_provider();
    elaborator_context eenv = mk_elaborator_context(env, pp);
    auto r = ::lean::elaborate(eenv, list<expr>(), e);
    m_pre_info_manager.clear();
    return r;
}

auto parser::elaborate_definition(name const & n, expr const & t, expr const & v)
    -> std::tuple<expr, expr, level_param_names> {
    parser_pos_provider pp = get_pos_provider();
    elaborator_context eenv = mk_elaborator_context(pp);
    auto r = ::lean::elaborate(eenv, n, t, v);
    m_pre_info_manager.clear();
    return r;
}

auto parser::elaborate_definition_at(environment const & env, local_level_decls const & lls,
                                     name const & n, expr const & t, expr const & v)
-> std::tuple<expr, expr, level_param_names> {
    parser_pos_provider pp = get_pos_provider();
    elaborator_context eenv = mk_elaborator_context(env, lls, pp);
    auto r = ::lean::elaborate(eenv, n, t, v);
    m_pre_info_manager.clear();
    return r;
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
    save_identifier_info(p, id);
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
    }
    for (auto p : names) {
        expr arg_type = type ? *type : save_pos(mk_expr_placeholder(), p.first);
        save_identifier_info(p.first, p.second);
        expr local = save_pos(mk_local(p.second, arg_type, bi), p.first);
        add_local(local);
        r.push_back(local);
    }
}

void parser::parse_binders_core(buffer<expr> & r, buffer<notation_entry> * nentries,
                                bool & last_block_delimited, unsigned rbp, bool simple_only) {
    while (true) {
        if (curr_is_identifier()) {
            parse_binder_block(r, binder_info(), rbp);
            last_block_delimited = false;
        } else if (curr_is_backtick()) {
            auto p    = pos();
            name n    = mk_fresh_name();
            expr type = parse_backtick_expr_core();
            expr local = save_pos(mk_local(n, type, binder_info()), p);
            add_local(local);
            r.push_back(local);
        } else {
            optional<binder_info> bi = parse_optional_binder_info(simple_only);
            if (bi) {
                rbp = 0;
                last_block_delimited = true;
                if (simple_only || !parse_local_notation_decl(nentries))
                    parse_binder_block(r, *bi, rbp);
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

expr parser::parse_notation_core(parse_table t, expr * left, bool as_tactic) {
    lean_assert(curr() == scanner::token_kind::Keyword);
    auto p = pos();
    if (m_info_manager)
        m_info_manager->add_symbol_info(p.first, p.second, get_token_info().token());
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
        notation::action const & a = r->first;
        switch (a.kind()) {
        case notation::action_kind::Skip:
            next();
            break;
        case notation::action_kind::Expr:
            next();
            args.push_back(parse_expr_or_tactic(a.rbp(), as_tactic));
            break;
        case notation::action_kind::Exprs: {
            next();
            buffer<expr> r_args;
            auto terminator = a.get_terminator();
            if (!terminator || !curr_is_token(*terminator)) {
                r_args.push_back(parse_expr_or_tactic(a.rbp(), as_tactic));
                while (curr_is_token(a.get_sep())) {
                    next();
                    r_args.push_back(parse_expr_or_tactic(a.rbp(), as_tactic));
                }
            }
            if (terminator) {
                if (curr_is_token(*terminator)) {
                    next();
                } else {
                    throw parser_error(sstream() << "invalid composite expression, '" << *terminator << "' expected", pos());
                }
            }
            expr rec = copy_with_new_pos(a.get_rec(), p);
            expr r;
            if (a.is_fold_right()) {
                if (a.get_initial()) {
                    r = instantiate_rev(copy_with_new_pos(*a.get_initial(), p), args.size(), args.data());
                } else {
                    r = r_args.back();
                    r_args.pop_back();
                }
                unsigned i = r_args.size();
                while (i > 0) {
                    --i;
                    args.push_back(r_args[i]);
                    args.push_back(r);
                    r = instantiate_rev(rec, args.size(), args.data());
                    args.pop_back(); args.pop_back();
                }
            } else {
                unsigned fidx = 0;
                if (a.get_initial()) {
                    r = instantiate_rev(copy_with_new_pos(*a.get_initial(), p), args.size(), args.data());
                } else {
                    r = r_args[0];
                    fidx++;
                }
                for (unsigned i = fidx; i < r_args.size(); i++) {
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
            next();
            binder_pos = pos();
            ps.push_back(parse_binder(a.rbp()));
            break;
        case notation::action_kind::Binders:
            next();
            binder_pos = pos();
            lenv = parse_binders(ps, a.rbp());
            break;
        case notation::action_kind::ScopedExpr: {
            next();
            expr r   = parse_scoped_expr(ps, lenv, a.rbp());
            bool no_cache = false;
            if (is_var(a.get_rec(), 0)) {
                if (a.use_lambda_abstraction())
                    r = Fun(ps, r, no_cache);
                else
                    r = Pi(ps, r, no_cache);
                r = rec_save_pos(r, binder_pos);
            } else {
                expr rec = copy_with_new_pos(a.get_rec(), p);
                unsigned i = ps.size();
                while (i > 0) {
                    --i;
                    expr const & l = ps[i];
                    if (a.use_lambda_abstraction())
                        r = Fun(l, r, no_cache);
                    else
                        r = Pi(l, r, no_cache);
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
            next();
            m_last_script_pos = p;
            using_script([&](lua_State * L) {
                    scoped_set_parser scope(L, *this);
                    lua_getglobal(L, a.get_lua_fn().c_str());
                    if (!lua_isfunction(L, -1))
                        throw parser_error(sstream() << "failed to use notation implemented in Lua, "
                                           << "Lua state does not contain function '"
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
    list<pair<unsigned, expr>> const & as = t.is_accepting();
    save_overload_notation(as, p);
    if (is_nil(as)) {
        if (p == pos())
            throw parser_error(sstream() << "invalid expression", pos());
        else
            throw parser_error(sstream() << "invalid expression starting at " << p.first << ":" << p.second, pos());
    }
    buffer<expr> cs;
    for (pair<unsigned, expr> const & a : as) {
        expr r = copy_with_new_pos(a.second, p);
        if (args.empty()) {
            // Notation does not have arguments. Thus, the info-manager should treat is as a single thing.
            r = mk_notation_info(r, r.get_tag());
        } else {
            r = instantiate_rev(r, args.size(), args.data());
        }
        cs.push_back(r);
    }
    expr r = save_pos(mk_choice(cs.size(), cs.data()), p);
    save_type_info(r);
    return r;
}

expr parser::parse_nud_notation() {
    return parse_notation(nud(), nullptr);
}

expr parser::parse_led_notation(expr left) {
    if (led().find(get_token_info().value())) {
        return parse_notation(led(), &left);
    } else {
        return mk_app(left, parse_expr(get_max_prec()), pos_of(left));
    }
}

expr parser::id_to_expr(name const & id, pos_info const & p) {
    buffer<level> lvl_buffer;
    levels ls;
    if (curr_is_token(get_llevel_curly_tk())) {
        next();
        while (!curr_is_token(get_rcurly_tk())) {
            lvl_buffer.push_back(parse_level());
        }
        next();
        ls = to_list(lvl_buffer.begin(), lvl_buffer.end());
    }

    // locals
    if (auto it1 = m_local_decls.find(id)) {
        if (ls && m_undef_id_behavior != undef_id_behavior::AssumeConstant)
            throw parser_error("invalid use of explicit universe parameter, identifier is a variable, "
                               "parameter or a constant bound to parameters in a section", p);
        auto r = copy_with_new_pos(*it1, p);
        save_type_info(r);
        save_identifier_info(p, id);
        return r;
    }

    for (name const & ns : get_namespaces(m_env)) {
        auto new_id = ns + id;
        if (!ns.is_anonymous() && m_env.find(new_id) &&
            (!id.is_atomic() || !is_protected(m_env, new_id))) {
            auto r = save_pos(mk_constant(new_id, ls), p);
            save_type_info(r);
            add_ref_index(new_id, p);
            save_identifier_info(p, new_id);
            return r;
        }
    }

    if (!id.is_atomic()) {
        name new_id = id;
        new_id = remove_root_prefix(new_id);
        if (m_env.find(new_id)) {
            auto r = save_pos(mk_constant(new_id, ls), p);
            save_type_info(r);
            add_ref_index(new_id, p);
            save_identifier_info(p, new_id);
            return r;
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
        save_overload(*r);
    }
    if (!r) {
        if (m_undef_id_behavior == undef_id_behavior::AssumeConstant) {
            r = save_pos(mk_constant(get_namespace(m_env) + id, ls), p);
        } else if (m_undef_id_behavior == undef_id_behavior::AssumeLocal) {
            expr local = mk_local(id, mk_expr_placeholder());
            m_undef_ids.push_back(local);
            r = save_pos(local, p);
        }
    }
    if (!r)
        throw parser_error(sstream() << "unknown identifier '" << id << "'", p);
    save_type_info(*r);
    if (is_constant(*r)) {
        add_ref_index(const_name(*r), p);
        save_identifier_info(p, const_name(*r));
    } else if (is_local(*r)) {
        save_identifier_info(p, local_pp_name(*r));
    }
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
    if (!m_has_num)
        m_has_num = has_num_decls(m_env);
    list<expr> vals;
    if (user_notation)
        vals = get_mpz_notation(m_env, n);
    if (!*m_has_num && !vals) {
        throw parser_error("numeral cannot be encoded as expression, environment does not contain the type 'num' "
                           "nor notation was defined for the given numeral "
                           "(solution: use 'import data.num', or define notation for the given numeral)", p);
    }
    buffer<expr> cs;
    if (*m_has_num)
        cs.push_back(save_pos(from_num(n), p));
    for (expr const & c : vals)
        cs.push_back(copy_with_new_pos(c, p));
    // Remark: choices are processed from right to left.
    // We want to process user provided notation before the default 'num'.
    lean_assert(!cs.empty());
    if (cs.size() == 1)
        return cs[0];
    else
        return save_pos(mk_choice(cs.size(), cs.data()), p);
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


expr parser::parse_backtick_expr_core() {
    next();
    flet<bool> set(m_in_backtick, true);
    expr type = parse_expr();
    if (curr() != scanner::token_kind::Backtick) {
        throw parser_error("invalid expression, '`' expected", pos());
    }
    next();
    return type;
}

expr parser::parse_backtick_expr() {
    auto p = pos();
    expr type   = parse_backtick_expr_core();
    expr assump = mk_by_plus(save_pos(mk_constant(get_tactic_assumption_name()), p), p);
    return save_pos(mk_typed_expr(type, assump), p);
}

expr parser::parse_nud() {
    switch (curr()) {
    case scanner::token_kind::Keyword:     return parse_nud_notation();
    case scanner::token_kind::Identifier:  return parse_id();
    case scanner::token_kind::Numeral:     return parse_numeral_expr();
    case scanner::token_kind::Decimal:     return parse_decimal_expr();
    case scanner::token_kind::String:      return parse_string_expr();
    case scanner::token_kind::Backtick:    return parse_backtick_expr();
    default: throw parser_error("invalid expression, unexpected token", pos());
    }
}

expr parser::parse_led(expr left) {
    switch (curr()) {
    case scanner::token_kind::Keyword: return parse_led_notation(left);
    default:                           return mk_app(left, parse_expr(get_max_prec()), pos_of(left));
    }
}

unsigned parser::curr_lbp_core(bool as_tactic) const {
    switch (curr()) {
    case scanner::token_kind::Keyword:
        if (as_tactic)
            return get_token_info().tactic_precedence();
        else
            return get_token_info().expr_precedence();
    case scanner::token_kind::CommandKeyword: case scanner::token_kind::Eof:
    case scanner::token_kind::ScriptBlock:    case scanner::token_kind::QuotedSymbol:
        return 0;
    case scanner::token_kind::Backtick:
        return m_in_backtick ? 0 : get_max_prec();
    case scanner::token_kind::Identifier:     case scanner::token_kind::Numeral:
    case scanner::token_kind::Decimal:        case scanner::token_kind::String:
        return get_max_prec();
    }
    lean_unreachable(); // LCOV_EXCL_LINE
}

expr parser::parse_expr(unsigned rbp) {
    expr left = parse_nud();
    while (rbp < curr_expr_lbp()) {
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
            while (rbp < curr_expr_lbp()) {
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

static bool is_tactic_type(expr const & e) {
    return is_constant(e) && const_name(e) == get_tactic_name();
}

static bool is_tactic_expr_list_type(expr const & e) {
    return is_constant(e) && const_name(e) == get_tactic_expr_list_name();
}

static bool is_tactic_opt_expr_list_type(expr const & e) {
    return is_constant(e) && const_name(e) == get_tactic_opt_expr_list_name();
}

static bool is_tactic_identifier_type(expr const & e) {
    return is_constant(e) && const_name(e) == get_tactic_identifier_name();
}

static bool is_tactic_identifier_list_type(expr const & e) {
    return is_constant(e) && const_name(e) == get_tactic_identifier_list_name();
}

static bool is_tactic_opt_identifier_list_type(expr const & e) {
    return is_constant(e) && const_name(e) == get_tactic_opt_identifier_list_name();
}

static bool is_tactic_using_expr(expr const & e) {
    return is_constant(e) && const_name(e) == get_tactic_using_expr_name();
}

static bool is_option_num(expr const & e) {
    return is_app(e) && is_constant(app_fn(e)) && const_name(app_fn(e)) == get_option_name() &&
        is_constant(app_arg(e)) && const_name(app_arg(e)) == get_num_name();
}

static bool is_tactic_command_type(expr e) {
    while (is_pi(e))
        e = binding_body(e);
    return is_tactic_type(e);
}

expr parser::parse_tactic_expr_arg(unsigned rbp) {
    parser::undef_id_to_local_scope scope1(*this);
    return parse_expr(rbp);
}

expr parser::parse_tactic_id_arg() {
    parser::undef_id_to_local_scope scope1(*this);
    return parse_id();
}

optional<expr> parser::is_tactic_command(name & id) {
    if (id.is_atomic())
        id = get_tactic_name() + id;
    auto d = m_env.find(id);
    if (!d)
        return none_expr();
    expr type = d->get_type();
    if (!is_tactic_command_type(type))
        return none_expr();
    return some_expr(type);
}

expr parser::mk_tactic_expr_list(buffer<expr> const & args, pos_info const & p) {
    unsigned i = args.size();
    expr r = save_pos(mk_constant(get_tactic_expr_list_nil_name()), p);
    while (i > 0) {
        i--;
        r = mk_app({save_pos(mk_constant(get_tactic_expr_list_cons_name()), p), args[i], r}, p);
    }
    return r;
}

expr parser::parse_tactic_expr_list() {
    auto p = pos();
    check_token_next(get_lbracket_tk(), "invalid tactic, '[' expected");
    buffer<expr> args;
    while (true) {
        args.push_back(parse_tactic_expr_arg());
        if (!curr_is_token(get_comma_tk()))
            break;
        next();
    }
    check_token_next(get_rbracket_tk(), "invalid tactic, ',' or ']' expected");
    return mk_tactic_expr_list(args, p);
}

expr parser::parse_tactic_id_list() {
    auto p = pos();
    buffer<expr> args;
    if (curr_is_identifier()) {
        while (curr_is_identifier()) {
            name id = get_name_val();
            args.push_back(mk_local(id, mk_expr_placeholder()));
            next();
        }
    } else {
        check_token_next(get_lbracket_tk(), "invalid tactic, '[' or identifier expected");
        while (true) {
            args.push_back(mk_local(check_id_next("invalid tactic, identifier expected"), mk_expr_placeholder()));
            if (!curr_is_token(get_comma_tk()))
                break;
            next();
        }
        check_token_next(get_rbracket_tk(), "invalid tactic, ',' or ']' expected");
    }
    return mk_tactic_expr_list(args, p);
}

expr parser::parse_tactic_opt_expr_list() {
    if (curr_is_token(get_lbracket_tk())) {
        return parse_tactic_expr_list();
    } else if (curr_is_token(get_with_tk())) {
        next();
        return parse_tactic_expr_list();
    } else {
        return save_pos(mk_constant(get_tactic_expr_list_nil_name()), pos());
    }
}

expr parser::parse_tactic_opt_id_list() {
    if (curr_is_token(get_lbracket_tk()) || curr_is_identifier()) {
        return parse_tactic_id_list();
    } else if (curr_is_token(get_with_tk())) {
        next();
        return parse_tactic_id_list();
    } else {
        return save_pos(mk_constant(get_tactic_expr_list_nil_name()), pos());
    }
}

expr parser::parse_tactic_option_num() {
    auto p = pos();
    if (curr_is_numeral()) {
        expr n = parse_numeral_expr(false);
        return mk_app(save_pos(mk_constant(get_option_some_name()), p), n, p);
    } else {
        return save_pos(mk_constant(get_option_none_name()), p);
    }
}

expr parser::parse_tactic_using_expr() {
    auto p = pos();
    if (curr_is_token(get_using_tk())) {
        next();
        return parse_expr();
    } else {
        return save_pos(mk_constant(get_tactic_none_expr_name()), p);
    }
}

expr parser::parse_tactic_nud() {
    if (curr_is_identifier()) {
        auto id_pos = pos();
        name id = get_name_val();
        if (optional<expr> tac_type = is_tactic_command(id)) {
            next();
            expr r         = save_pos(mk_constant(id), id_pos);
            expr type      = *tac_type;
            buffer<expr> ds;
            while (is_pi(type)) {
                ds.push_back(binding_domain(type));
                type = binding_body(type);
            }
            unsigned arity = ds.size();
            for (unsigned i = 0; i < arity; i++) {
                expr const & d = ds[i];
                if (is_tactic_type(d)) {
                    r = mk_app(r, parse_tactic(get_max_prec()), id_pos);
                } else if (is_tactic_expr_list_type(d)) {
                    r = mk_app(r, parse_tactic_expr_list(), id_pos);
                } else if (is_tactic_opt_expr_list_type(d)) {
                    r = mk_app(r, parse_tactic_opt_expr_list(), id_pos);
                } else if (is_tactic_identifier_type(d)) {
                    r = mk_app(r, mk_local(check_id_next("invalid tactic, identifier expected"),
                                           mk_expr_placeholder()), id_pos);
                } else if (is_tactic_identifier_list_type(d)) {
                    r = mk_app(r, parse_tactic_id_list(), id_pos);
                } else if (is_tactic_opt_identifier_list_type(d)) {
                    r = mk_app(r, parse_tactic_opt_id_list(), id_pos);
                } else if (is_tactic_using_expr(d)) {
                    r = mk_app(r, parse_tactic_using_expr(), id_pos);
                } else if (arity == 1 && is_option_num(d)) {
                    r = mk_app(r, parse_tactic_option_num(), id_pos);
                } else {
                    unsigned rbp;
                    if ((arity == 1) ||
                        (arity >= 2 && i == 0 && (is_tactic_opt_identifier_list_type(ds[1]) || is_tactic_using_expr(ds[1]))))
                        rbp = 0;
                    else
                        rbp = get_max_prec();
                    r = mk_app(r, parse_tactic_expr_arg(rbp), id_pos);
                }
            }
            return r;
        } else {
            return parse_expr();
        }
    } else if (curr_is_keyword()) {
        return parse_tactic_notation(tactic_nud(), nullptr);
    } else {
        throw parser_error("invalid tactic expression", pos());
    }
}

expr parser::parse_tactic_led(expr left) {
    if (tactic_led().find(get_token_info().value())) {
        return parse_tactic_notation(tactic_led(), &left);
    } else {
        throw parser_error("invalid tactic expression", pos());
    }
}

expr parser::parse_tactic(unsigned rbp) {
    expr left = parse_tactic_nud();
    while (rbp < curr_tactic_lbp()) {
        left = parse_tactic_led(left);
    }
    return left;
}

void parser::parse_command() {
    lean_assert(curr() == scanner::token_kind::CommandKeyword);
    m_last_cmd_pos = pos();
    name const & cmd_name = get_token_info().value();
    m_cmd_token = get_token_info().token();
    if (auto it = cmds().find(cmd_name)) {
        if (is_notation_cmd(cmd_name)) {
            in_notation_ctx ctx(*this);
            next();
            m_local_decls_size_at_beg_cmd = m_local_decls.size();
            m_env = it->get_fn()(*this);
        } else {
            next();
            m_local_decls_size_at_beg_cmd = m_local_decls.size();
            m_env = it->get_fn()(*this);
        }
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

static std::string * g_lua_module_key = nullptr;
static void lua_module_reader(deserializer & d, shared_environment &,
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

void parser::parse_imports() {
    buffer<module_name> olean_files;
    buffer<name>        lua_files;
    bool prelude     = false;
    std::string base = dirname(get_stream_name().c_str());
    bool imported    = false;
    unsigned fingerprint = 0;
    if (curr_is_token(get_prelude_tk())) {
        next();
        prelude = true;
    }
    auto import_olean = [&](optional<unsigned> const & k, name const & f) {
        if (auto it = try_file(base, k, f, ".olean")) {
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
    };
    if (!prelude) {
        import_olean(optional<unsigned>(), "init");
    }
    while (curr_is_token(get_import_tk())) {
        imported       = true;
        m_last_cmd_pos = pos();
        next();
        while (true) {
            optional<unsigned> k;
            while (curr_is_token(get_period_tk())) {
                next();
                if (!k)
                    k = 0;
                else
                    k = *k + 1;
            }
            if (!curr_is_identifier())
                break;
            name f            = get_name_val();
            fingerprint       = hash(fingerprint, f.hash());
            if (k)
                fingerprint = hash(fingerprint, *k);
            if (auto it = try_file(f, ".lua")) {
                if (k)
                    throw parser_error(sstream() << "invalid import, failed to import '" << f
                                       << "', relative paths are not supported for .lua files", pos());
                lua_files.push_back(f);
            } else {
                import_olean(k, f);
            }
            next();
        }
    }
    unsigned num_threads = 0;
    if (get_parser_parallel_import(m_ios.get_options()))
        num_threads = m_num_threads;
    bool keep_imported_thms = (m_keep_theorem_mode == keep_theorem_mode::All);
    m_env = import_modules(m_env, base, olean_files.size(), olean_files.data(), num_threads,
                           keep_imported_thms, m_ios);
    m_env = update_fingerprint(m_env, fingerprint);
    for (auto const & f : lua_files) {
        std::string rname = find_file(f, {".lua"});
        system_import(rname.c_str());
        m_env = module::add(m_env, *g_lua_module_key, [=](environment const &, serializer & s) {
                s << f;
            });
    }
    if (imported)
        commit_info(1, 0);
}

void parser::commit_info(unsigned line, unsigned col) {
    save_snapshot();
    if (m_info_manager) {
        m_info_manager->save_environment_options(line, col, m_env, m_ios.get_options());
        m_info_manager->commit_upto(line, true);
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
#ifndef LEAN_IGNORE_SORRY
            // TODO(Leo): remove the #ifdef.
            // The compilation option LEAN_IGNORE_SORRY is a temporary hack for the nightly builds
            // We use it to avoid a buch of warnings on cdash.
            flycheck_warning wrn(regular_stream());
            display_warning_pos(pos());
            regular_stream() << " imported file uses 'sorry'" << endl;
#endif
        }
        while (!done) {
            if (m_stop_at && pos().first > m_stop_at_line) {
                throw interrupt_parser();
            }
            protected_call([&]() {
                    check_interrupted();
                    switch (curr()) {
                    case scanner::token_kind::CommandKeyword:
                        if (curr_is_token(get_end_tk()))
                            commit_info();
                        parse_command();
                        commit_info();
                        break;
                    case scanner::token_kind::ScriptBlock:
                        parse_script();
                        save_snapshot();
                        break;
                    case scanner::token_kind::Eof:
                        done = true;
                        break;
                    case scanner::token_kind::Keyword:
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
        if (has_open_scopes(m_env)) {
            m_found_errors = true;
            if (!m_use_exceptions && m_show_errors)
                display_error("invalid end of module, expecting 'end'", pos());
            else if (m_use_exceptions)
                throw_parser_exception("invalid end of module, expecting 'end'", pos());
        }
    } catch (interrupt_parser) {
        commit_info();
        while (has_open_scopes(m_env))
            m_env = pop_scope_core(m_env, m_ios);
    }
    commit_info(m_scanner.get_line()+1, 0);

    protected_call(
        [&]() {
            m_theorem_queue.for_each([&](certified_declaration const & thm) {
                    if (keep_new_thms()) {
                        name const & thm_name = thm.get_declaration().get_name();
                        if (m_env.get(thm_name).is_axiom())
                            replace_theorem(thm);
                    }
                });
        },
        []() {});
    return !m_found_errors;
}

bool parser::curr_is_command_like() const {
    switch (curr()) {
    case scanner::token_kind::CommandKeyword:
        return true;
    case scanner::token_kind::ScriptBlock:
        return true;
    case scanner::token_kind::Eof:
        return true;
    case scanner::token_kind::Keyword:
        return curr_is_token(get_period_tk());
    default:
        return false;
    }
}

void parser::add_delayed_theorem(environment const & env, name const & n, level_param_names const & ls,
                                 expr const & t, expr const & v) {
    m_theorem_queue_set.insert(n);
    m_theorem_queue.add(env, n, ls, get_local_level_decls(), t, v);
}

void parser::add_delayed_theorem(certified_declaration const & cd) {
    m_theorem_queue_set.insert(cd.get_declaration().get_name());
    m_theorem_queue.add(cd);
}

void parser::replace_theorem(certified_declaration const & thm) {
    m_env = m_env.replace(thm);
    name const & thm_name = thm.get_declaration().get_name();
    if (!m_ignore_noncomputable && !check_computable(m_env, thm_name)) {
        throw exception(sstream() << "declaration '" << thm_name
                        << "' was marked as a theorem, but it is a noncomputable definition");
    }
}

environment parser::reveal_theorems(buffer<name> const & ds) {
    m_theorem_queue.for_each([&](certified_declaration const & thm) {
            if (keep_new_thms()) {
                name const & thm_name = thm.get_declaration().get_name();
                if (m_env.get(thm_name).is_axiom() &&
                    std::any_of(ds.begin(), ds.end(), [&](name const & n) { return n == thm_name; })) {
                    replace_theorem(thm);
                    m_theorem_queue_set.erase(thm_name);
                }
            }
        });
    return m_env;
}

void parser::save_snapshot() {
    m_pre_info_manager.clear();
    if (!m_snapshot_vector)
        return;
    if (m_snapshot_vector->empty() || static_cast<int>(m_snapshot_vector->back().m_line) != m_scanner.get_line())
        m_snapshot_vector->push_back(snapshot(m_env, m_ngen, m_local_level_decls, m_local_decls,
                                              m_level_variables, m_variables, m_include_vars,
                                              m_ios.get_options(), m_parser_scope_stack, m_scanner.get_line()));
}

void parser::save_pre_info_data() {
    // if elaborator failed, then m_pre_info_data contains type information before elaboration.
    if (m_info_manager) {
        bool overwrite = false;
        m_info_manager->merge(m_pre_info_manager, overwrite);
        m_pre_info_manager.clear();
    }
}

void parser::save_overload(expr const & e) {
    if (!m_info_manager || !is_choice(e))
        return;
    auto p = pos_of(e);
    m_info_manager->add_overload_info(p.first, p.second, e);
}

void parser::save_overload_notation(list<expr> const & as, pos_info const & p) {
    if (!m_info_manager || length(as) <= 1)
        return;
    m_info_manager->add_overload_notation_info(p.first, p.second, as);
}
void parser::save_overload_notation(list<pair<unsigned, expr>> const & as, pos_info const & p) {
    if (!m_info_manager || length(as) <= 1)
        return;
    list<expr> new_as = map2<expr, pair<unsigned, expr>, std::function<expr(pair<unsigned, expr> const &)>>(as, [](pair<unsigned, expr> const & p) { return p.second; });
    save_overload_notation(new_as, p);
}
void parser::save_identifier_info(pos_info const & p, name const & full_id) {
    if (!m_info_manager)
        return;
    m_info_manager->add_identifier_info(p.first, p.second, full_id);
}

void parser::save_type_info(expr const & e) {
    if (!m_info_manager)
        return;
    if (is_explicit(e)) {
        save_type_info(get_explicit_arg(e));
    } else if (is_as_atomic(e)) {
        save_type_info(get_as_atomic_arg(e));
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
        m_pre_info_manager.add_type_info(p.first, p.second, d->get_type());
    } else if (is_local(e)) {
        auto p = pos_of(e);
        expr t = mlocal_type(e);
        if (is_meta(t))
            return;
        m_pre_info_manager.add_type_info(p.first, p.second, t);
    }
}

bool parse_commands(environment & env, io_state & ios, std::istream & in, char const * strm_name, bool use_exceptions,
                    unsigned num_threads, definition_cache * cache, declaration_index * index,
                    keep_theorem_mode tmode) {
    parser p(env, ios, in, strm_name, use_exceptions, num_threads, nullptr, nullptr, nullptr, tmode);
    p.set_cache(cache);
    p.set_index(index);
    bool r = p();
    ios = p.ios();
    env = p.env();
    return r;
}

bool parse_commands(environment & env, io_state & ios, char const * fname, bool use_exceptions, unsigned num_threads,
                    definition_cache * cache, declaration_index * index, keep_theorem_mode tmode) {
    std::ifstream in(fname);
    if (in.bad() || in.fail())
        throw exception(sstream() << "failed to open file '" << fname << "'");
    return parse_commands(env, ios, in, fname, use_exceptions, num_threads, cache, index, tmode);
}

void initialize_parser() {
    g_parser_show_errors     = new name{"parser", "show_errors"};
    g_parser_parallel_import = new name{"parser", "parallel_import"};
    register_bool_option(*g_parser_show_errors, LEAN_DEFAULT_PARSER_SHOW_ERRORS,
                         "(lean parser) display error messages in the regular output channel");
    register_bool_option(*g_parser_parallel_import, LEAN_DEFAULT_PARSER_PARALLEL_IMPORT,
                         "(lean parser) import modules in parallel");
    g_tmp_prefix = new name(name::mk_internal_unique_name());
    g_lua_module_key = new std::string("lua_module");
    register_module_object_reader(*g_lua_module_key, lua_module_reader);
}

void finalize_parser() {
    delete g_lua_module_key;
    delete g_tmp_prefix;
    delete g_parser_show_errors;
    delete g_parser_parallel_import;
}
}
