/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <vector>
#include <string>
#include "util/sstream.h"
#include "kernel/kernel_exception.h"

namespace lean {
format kernel_exception::pp(formatter const &, options const &) const { return format(what()); }

class generic_kernel_exception : public kernel_exception {
protected:
    optional<expr> m_main_expr;
    pp_fn          m_pp_fn;
public:
    generic_kernel_exception(ro_environment const & env, char const * msg, optional<expr> const & m, pp_fn const & fn):
        kernel_exception(env, msg),
        m_main_expr(m),
        m_pp_fn(fn) {}
    virtual ~generic_kernel_exception() noexcept {}
    virtual optional<expr> get_main_expr() const { return m_main_expr; }
    virtual format pp(formatter const & fmt, options const & opts) const { return m_pp_fn(fmt, opts); }
    virtual exception * clone() const { return new generic_kernel_exception(m_env, m_msg.c_str(), m_main_expr, m_pp_fn); }
    virtual void rethrow() const { throw *this; }
};

[[ noreturn ]] void throw_kernel_exception(ro_environment const & env, char const * msg, optional<expr> const & m) {
    std::string msg_str = msg;
    throw generic_kernel_exception(env, msg, m, [=](formatter const &, options const &) { return format(msg); });
}

[[ noreturn ]] void throw_kernel_exception(ro_environment const & env, sstream const & strm, optional<expr> const & m) {
    throw_kernel_exception(env, strm.str().c_str(), m);
}

[[ noreturn ]] void throw_kernel_exception(ro_environment const & env, char const * msg, pp_fn const & fn,
                                           optional<expr> const & m) {
    throw generic_kernel_exception(env, msg, m, fn);
}

[[ noreturn ]] void throw_kernel_exception(ro_environment const & env, pp_fn const & fn, optional<expr> const & m) {
    throw generic_kernel_exception(env, "kernel exception", m, fn);
}

[[ noreturn ]] void throw_unknown_object(ro_environment const & env, name const & n) {
    throw_kernel_exception(env, sstream() << "unknown object '" << n << "'");
}

[[ noreturn ]] void throw_already_declared(ro_environment const & env, name const & n) {
    throw_kernel_exception(env, sstream() << "invalid object declaration, environment already has an object named '" << n << "'");
}

[[ noreturn ]] void throw_read_only_environment(ro_environment const & env) {
    throw_kernel_exception(env, "environment cannot be updated because it has children environments");
}


#if 0



format unknown_name_exception::pp(formatter const &, options const &) const {
    return format{format(what()), format(" '"), format(get_name()), format("'")};
}

format has_no_type_exception::pp(formatter const &, options const &) const {
    return format{format("object '"), format(const_name(m_const)), format("' has no type associated with it")};
}

format app_type_mismatch_exception::pp(formatter const & fmt, options const & opts) const {
    unsigned indent     = get_pp_indent(opts);
    context const & ctx = get_context();
    expr const & app    = get_application();
    format app_fmt      = fmt(ctx, app, false, opts);
    std::vector<expr> const & arg_types = get_arg_types();
    auto it = arg_types.begin();
    format f_type_fmt   = fmt(ctx, *it, false, opts);
    format arg_types_fmt;
    ++it;
    for (unsigned i = 1; it != arg_types.end(); ++it, ++i) {
        expr const & a    = arg(app, i);
        format arg_fmt    = fmt(ctx, a, false, opts);
        if (is_pi(a) || is_lambda(a) || is_let(a))
            arg_fmt = paren(arg_fmt);
        format arg_type_fmt = fmt(ctx, *it, false, opts);
        arg_types_fmt += nest(indent, compose(line(), group(format{arg_fmt, space(), colon(), nest(indent, format{line(), arg_type_fmt})})));
    }
    format r;
    r += format{format("type mismatch in argument #"), format(m_arg_pos),  format(" at application")};
    r += nest(indent, compose(line(), app_fmt));
    r += compose(line(), format("Function type:"));
    r += nest(indent, compose(line(), f_type_fmt));
    r += line();
    if (arg_types.size() > 2)
        r += format("Arguments types:");
    else
        r += format("Argument type:");
    r += arg_types_fmt;
    return r;
}

format pair_type_mismatch_exception::pp(formatter const & fmt, options const & opts) const {
    unsigned indent     = get_pp_indent(opts);
    context const & ctx = get_context();
    expr const & pair   = get_pair();
    format pair_fmt     = fmt(ctx, pair, false, opts);
    format r = format("type mismatch in the ");
    if (m_first)
        r += format("1st");
    else
        r += format("2nd");
    r += format(" argument of the pair");
    r += nest(indent, compose(line(), pair_fmt));
    r += compose(line(), format("Pair type:"));
    r += nest(indent, compose(line(), fmt(ctx, m_sig_type, false, opts)));
    r += line();
    r += format("Argument type:");
    r += nest(indent, compose(line(), fmt(ctx, m_arg_type, false, opts)));
    return r;
}

format abstraction_expected_exception::pp(formatter const & fmt, options const & opts) const {
    unsigned indent = get_pp_indent(opts);
    format expr_fmt = fmt(get_context(), get_expr(), false, opts);
    format r;
    r += format(what());
    r += format(" at");
    r += nest(indent, compose(line(), expr_fmt));
    return r;
}

format type_expected_exception::pp(formatter const & fmt, options const & opts) const {
    unsigned indent = get_pp_indent(opts);
    format expr_fmt = fmt(get_context(), get_expr(), false, opts);
    format r;
    r += format("type expected, got");
    r += nest(indent, compose(line(), expr_fmt));
    return r;
}

format def_type_mismatch_exception::pp(formatter const & fmt, options const & opts) const {
    unsigned indent     = get_pp_indent(opts);
    context const & ctx = get_context();
    format r;
    r += format("type mismatch at definition '");
    r += format(get_name());
    r += format("', expected type");
    r += nest(indent, compose(line(), fmt(ctx, get_type(), false, opts)));
    r += compose(line(), format("Given type:"));
    r += nest(indent, compose(line(), fmt(ctx, get_value_type(), false, opts)));
    return r;
}
#endif
}
