/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <string>
#include "util/name_map.h"
#include "util/name_set.h"
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"
#include "kernel/error_msgs.h"

namespace lean {
format pp_indent_expr(formatter const & fmt, expr const & e) {
    return nest(get_pp_indent(fmt.get_options()), compose(line(), fmt(e)));
}

format pp_type_expected(formatter const & fmt, expr const & e, expr const * e_type) {
    format f = format("type expected at") + pp_indent_expr(fmt, e);
    if (e_type) {
        f += line() + format("term has type") + pp_indent_expr(fmt, *e_type);
    }
    return f;
}

format pp_function_expected(formatter const & fmt, expr const & fn) {
    return format("function expected at") + pp_indent_expr(fmt, fn);
}

format pp_function_expected(formatter const & fmt, expr const & fn, expr const & fn_type) {
    return pp_function_expected(fmt, fn) +
           line() + format("term has type") + pp_indent_expr(fmt, fn_type);
}

format pp_function_expected(formatter const & fmt, expr const & app, expr const & fn, expr const & fn_type) {
    return pp_function_expected(fmt, app) +
            line() + format("term") + pp_indent_expr(fmt, get_app_fn(fn)) +
            line() + format("has type") + pp_indent_expr(fmt, fn_type);
}

static list<options> * g_distinguishing_pp_options = nullptr;

void set_distinguishing_pp_options(list<options> const & opts) {
    *g_distinguishing_pp_options = opts;
}

list<options> const & get_distinguishing_pp_options() {
    return *g_distinguishing_pp_options;
}

expr erase_binder_info(expr const & e) {
    return replace(e, [](expr const & e) {
            if (is_local(e) || is_metavar(e)) {
                return some_expr(e);
            } else if (is_binding(e) && binding_info(e) != binder_info()) {
                return some_expr(update_binding(e, erase_binder_info(binding_domain(e)),
                                                erase_binder_info(binding_body(e)), binder_info()));
            } else {
                return none_expr();
            }
        });
}

static std::tuple<formatter, format, format> pp_until_different(formatter const & _fmt, expr const & e1, expr const & e2, list<options> extra) {
    formatter fmt(_fmt);
    expr n_e1 = erase_binder_info(e1);
    expr n_e2 = erase_binder_info(e2);
    while (true) {
        format r1 = pp_indent_expr(fmt, n_e1);
        format r2 = pp_indent_expr(fmt, n_e2);
        if (!format_pp_eq(r1, r2, fmt.get_options()))
            return std::make_tuple(fmt, pp_indent_expr(fmt, e1), pp_indent_expr(fmt, e2));
        if (!extra)
            return std::make_tuple(_fmt, pp_indent_expr(_fmt, e1), pp_indent_expr(_fmt, e2));
        options o = join(head(extra), fmt.get_options());
        fmt   = fmt.update_options(o);
        extra = tail(extra);
    }
}

std::tuple<formatter, format, format> pp_until_different(formatter const & fmt, expr const & e1, expr const & e2) {
    return pp_until_different(fmt, e1, e2, *g_distinguishing_pp_options);
}

static void check_alias(name const & n, name const & id, name_map<name> & name_to_id, name_set & aliased) {
    if (name const * old_id = name_to_id.find(n)) {
        if (id != *old_id) {
            aliased.insert(n);
        }
    } else {
        name_to_id.insert(n, id);
    }
}

static void collect_aliased_locals(expr const & e, name_map<name> & name_to_id, name_set & aliased) {
    for_each(e, [&](expr const & t, unsigned) {
            if (is_local(t) || is_metavar(t)) {
                check_alias(mlocal_pp_name(t), mlocal_name(t), name_to_id, aliased);
            } else if (is_constant(t)) {
                check_alias(const_name(t), const_name(t), name_to_id, aliased);
            }
            return true;
        });
}

format pp_type_mismatch(formatter const & _fmt, expr const & given_type, expr const & expected_type,
                        optional<expr> const & given_type_type,
                        optional<expr> const & expected_type_type) {
    formatter fmt(_fmt);
    name_map<name> name_to_id; name_set aliased;
    collect_aliased_locals(given_type, name_to_id, aliased);
    collect_aliased_locals(expected_type, name_to_id, aliased);
    format expected_fmt, given_fmt;
    std::tie(fmt, expected_fmt, given_fmt) = pp_until_different(fmt, expected_type, given_type);
    format r;
    r += format("has type");
    if (given_type_type && expected_type_type &&
        is_sort(*given_type_type) &&
        is_sort(*expected_type_type) &&
        !is_equivalent(sort_level(*given_type_type), sort_level(*expected_type_type))) {
        r += given_fmt + format(" : ") + fmt(*given_type_type);
        r += compose(line(), format("but is expected to have type"));
        r += expected_fmt + format(" : ") + fmt(*expected_type_type);
    } else {
        r += given_fmt;
        r += compose(line(), format("but is expected to have type"));
        r += expected_fmt;
    }
    if (!aliased.empty()) {
        r += line() + format("types contain aliased name(s):");
        aliased.for_each([&](name const & n) {
                r += space() + format(n);
            });
        r += line() + format("remark: the tactic `dedup` can be used to rename aliases");
    }
    return r;
}

format pp_type_mismatch(formatter const & fmt, expr const & e, expr const & e_type, expr const & expected_type,
                        optional<expr> const & e_type_type,
                        optional<expr> const & expected_type_type) {
    format r;
    r += pp_indent_expr(fmt, e);
    r += line() + pp_type_mismatch(fmt, e_type, expected_type, e_type_type, expected_type_type);
    return r;
}

format pp_app_type_mismatch(formatter const & _fmt, expr const & app, expr const & fn_type, expr const & arg, expr const & given_type,
                            optional<expr> const & given_type_type, optional<expr> const & domain_type_type) {
    formatter fmt(_fmt);
    lean_assert(is_pi(fn_type));
    if (!is_explicit(binding_info(fn_type))) {
        // Force implicit arguments to be shown if argument is implicit
        options opts = fmt.get_options();
        // TODO(Leo): this is hackish, the option is defined in the folder library
        opts = opts.update_if_undef(name{"pp", "implicit"}, true);
        fmt = fmt.update_options(opts);
    }
    if (is_lambda(get_app_fn(app))) {
        // Disable beta reduction in the pretty printer since it will make the error hard to understand.
        // See issue https://github.com/leanprover/lean/issues/669
        options opts = fmt.get_options();
        // TODO(Leo): this is hackish, the option is defined in the folder library
        opts = opts.update_if_undef(name{"pp", "beta"}, false);
        fmt = fmt.update_options(opts);
    }
    expr expected_type = binding_domain(fn_type);
    format r;
    r += format("type mismatch at application");
    r += pp_indent_expr(fmt, app);
    r += line () + format("term") + pp_type_mismatch(fmt, arg, given_type, expected_type, given_type_type, domain_type_type);
    return r;
}

format pp_def_type_mismatch(formatter const & fmt, name const & n, expr const & given_type, expr const & expected_type,
                            optional<expr> const & given_type_type, optional<expr> const & expected_type_type) {
    format r;
    r += format("type mismatch at definition '");
    r += format(n);
    r += format("', ");
    r += pp_type_mismatch(fmt, given_type, expected_type, given_type_type, expected_type_type);
    return r;
}

static format pp_until_meta_visible(formatter const & fmt, expr const & e, list<options> extra) {
    options o = fmt.get_options();
    o = o.update_if_undef(get_formatter_hide_full_terms_name(), true);
    formatter fmt1 = fmt.update_options(o);
    while (true) {
        format r = pp_indent_expr(fmt1, e);
        std::ostringstream out;
        out << mk_pair(r, fmt1.get_options());
        if (out.str().find("?M") != std::string::npos)
            return r;
        if (!extra)
            return pp_indent_expr(fmt.update_options(o), e);
        options o2 = join(head(extra), fmt.get_options());
        o2    = o2.update_if_undef(get_formatter_hide_full_terms_name(), true);
        fmt1  = fmt.update_options(o2);
        extra = tail(extra);
    }
}

format pp_until_meta_visible(formatter const & fmt, expr const & e) {
    return pp_until_meta_visible(fmt, e, *g_distinguishing_pp_options);
}

format pp_decl_has_metavars(formatter const & fmt, name const & n, expr const & e, bool is_type) {
    format r("failed to add declaration '");
    r += format(n);
    r += format("' to environment, ");
    if (is_type)
        r += format("type");
    else
        r += format("value");
    r += format(" has metavariables");
    options const & o = fmt.get_options();
    if (!o.contains(get_formatter_hide_full_terms_name()))
        r += line() + format("remark: set 'formatter.hide_full_terms' to false to see the complete term");
    r += pp_until_meta_visible(fmt, e);
    return r;
}

void initialize_error_msgs() {
    g_distinguishing_pp_options = new list<options>();
}
void finalize_error_msgs() {
    delete g_distinguishing_pp_options;
}
}
