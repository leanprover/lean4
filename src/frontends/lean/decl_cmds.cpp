/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include "util/sstream.h"
#include "kernel/type_checker.h"
#include "kernel/abstract.h"
#include "kernel/replace_fn.h"
#include "kernel/for_each_fn.h"
#include "library/scoped_ext.h"
#include "library/aliases.h"
#include "library/num.h"
#include "library/private.h"
#include "library/normalize.h"
#include "library/protected.h"
#include "library/placeholder.h"
#include "library/locals.h"
#include "library/explicit.h"
#include "library/reducible.h"
#include "library/coercion.h"
#include "library/choice.h"
#include "library/replace_visitor.h"
#include "library/class.h"
#include "library/abbreviation.h"
#include "library/unfold_macros.h"
#include "library/definitional/equations.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/util.h"
#include "frontends/lean/tokens.h"

namespace lean {
static environment declare_universe(parser & p, environment env, name const & n, bool local) {
    if (in_context(env) || local) {
        p.add_local_level(n, mk_param_univ(n), local);
    } else {
        name const & ns = get_namespace(env);
        name full_n  = ns + n;
        env = module::add_universe(env, full_n);
        if (!ns.is_anonymous())
            env = add_level_alias(env, n, full_n);
    }
    return env;
}

static environment universes_cmd_core(parser & p, bool local) {
    if (!p.curr_is_identifier())
        throw parser_error("invalid 'universes' command, identifier expected", p.pos());
    environment env = p.env();
    while (p.curr_is_identifier()) {
        name n = p.get_name_val();
        p.next();
        env = declare_universe(p, env, n, local);
    }
    return env;
}

static environment universe_cmd(parser & p) {
    if (p.curr_is_token(get_variables_tk())) {
        p.next();
        return universes_cmd_core(p, true);
    } else {
        bool local = false;
        if (p.curr_is_token(get_variable_tk())) {
            p.next();
            local = true;
        }
        name n = p.check_id_next("invalid 'universe' command, identifier expected");
        return declare_universe(p, p.env(), n, local);
    }
}

static environment universes_cmd(parser & p) {
    return universes_cmd_core(p, false);
}

bool parse_univ_params(parser & p, buffer<name> & ps) {
    if (p.curr_is_token(get_llevel_curly_tk())) {
        p.next();
        while (!p.curr_is_token(get_rcurly_tk())) {
            name l = p.check_id_next("invalid universe parameter, identifier expected");
            p.add_local_level(l, mk_param_univ(l));
            ps.push_back(l);
        }
        p.next();
        return true;
    } else{
        return false;
    }
}

void update_univ_parameters(buffer<name> & ls_buffer, name_set const & found, parser const & p) {
    unsigned old_sz = ls_buffer.size();
    found.for_each([&](name const & n) {
            if (std::find(ls_buffer.begin(), ls_buffer.begin() + old_sz, n) == ls_buffer.begin() + old_sz)
                ls_buffer.push_back(n);
        });
    std::sort(ls_buffer.begin(), ls_buffer.end(), [&](name const & n1, name const & n2) {
            return p.get_local_level_index(n1) < p.get_local_level_index(n2);
        });
}

enum class variable_kind { Constant, Parameter, Variable, Axiom };

static void check_parameter_type(parser & p, name const & n, expr const & type, pos_info const & pos) {
    for_each(type, [&](expr const & e, unsigned) {
            if (is_local(e) && p.is_local_variable(e))
                throw parser_error(sstream() << "invalid parameter declaration '" << n << "', it depends on " <<
                                   "variable '" << local_pp_name(e) << "'", pos);
            return true;
        });
}

static environment declare_var(parser & p, environment env,
                               name const & n, level_param_names const & ls, expr const & type,
                               variable_kind k, optional<binder_info> const & _bi, pos_info const & pos) {
    binder_info bi;
    if (_bi) bi = *_bi;
    if (k == variable_kind::Parameter || k == variable_kind::Variable) {
        if (k == variable_kind::Parameter) {
            check_in_context_or_section(p);
            check_parameter_type(p, n, type, pos);
        }
        if (p.get_local(n))
            throw parser_error(sstream() << "invalid parameter/variable declaration, '"
                               << n << "' has already been declared", pos);
        name u = p.mk_fresh_name();
        expr l = p.save_pos(mk_local(u, n, type, bi), pos);
        if (k == variable_kind::Parameter)
            p.add_parameter(n, l);
        else
            p.add_local_expr(n, l, k == variable_kind::Variable);
        return env;
    } else {
        lean_assert(k == variable_kind::Constant || k == variable_kind::Axiom);
        name const & ns = get_namespace(env);
        name full_n  = ns + n;
        expr new_type = expand_abbreviations(env, unfold_untrusted_macros(env, type));
        if (k == variable_kind::Axiom) {
            env = module::add(env, check(env, mk_axiom(full_n, ls, new_type)));
            p.add_decl_index(full_n, pos, get_axiom_tk(), new_type);
        } else {
            env = module::add(env, check(env, mk_constant_assumption(full_n, ls, new_type)));
            p.add_decl_index(full_n, pos, get_variable_tk(), new_type);
        }
        if (!ns.is_anonymous())
            env = add_expr_alias(env, n, full_n);
        return env;
    }
}

/** \brief If we are in a section, then add the new local levels to it. */
static void update_local_levels(parser & p, level_param_names const & new_ls, bool is_variable) {
    for (auto const & l : new_ls)
        p.add_local_level(l, mk_param_univ(l), is_variable);
}

optional<binder_info> parse_binder_info(parser & p, variable_kind k) {
    optional<binder_info> bi = p.parse_optional_binder_info();
    if (bi && k != variable_kind::Parameter && k != variable_kind::Variable)
        parser_error("invalid binder annotation, it can only be used to declare variables/parameters", p.pos());
    return bi;
}

static void check_variable_kind(parser & p, variable_kind k) {
    if (in_context(p.env())) {
        if (k == variable_kind::Axiom || k == variable_kind::Constant)
            throw parser_error("invalid declaration, 'constant/axiom' cannot be used in contexts",
                               p.pos());
    } else if (!in_section(p.env()) && !in_context(p.env()) && k == variable_kind::Parameter) {
        throw parser_error("invalid declaration, 'parameter/hypothesis/conjecture' "
                           "can only be used in contexts and sections", p.pos());
    }
}

static environment variable_cmd_core(parser & p, variable_kind k) {
    check_variable_kind(p, k);
    auto pos = p.pos();
    optional<binder_info> bi = parse_binder_info(p, k);
    name n = p.check_id_next("invalid declaration, identifier expected");
    buffer<name> ls_buffer;
    if (p.curr_is_token(get_llevel_curly_tk()) && (k == variable_kind::Parameter || k == variable_kind::Variable))
        throw parser_error("invalid declaration, only constants/axioms can be universe polymorphic", p.pos());
    optional<parser::local_scope> scope1;
    if (k == variable_kind::Constant || k == variable_kind::Axiom)
        scope1.emplace(p);
    parse_univ_params(p, ls_buffer);
    expr type;
    if (!p.curr_is_token(get_colon_tk())) {
        buffer<expr> ps;
        unsigned rbp = 0;
        auto lenv = p.parse_binders(ps, rbp);
        p.check_token_next(get_colon_tk(), "invalid declaration, ':' expected");
        type = p.parse_scoped_expr(ps, lenv);
        type = Pi(ps, type, p);
    } else {
        p.next();
        type = p.parse_expr();
    }
    p.parse_close_binder_info(bi);
    check_command_period_or_eof(p);
    level_param_names ls;
    if (ls_buffer.empty()) {
        ls = to_level_param_names(collect_univ_params(type));
    } else {
        update_univ_parameters(ls_buffer, collect_univ_params(type), p);
        ls = to_list(ls_buffer.begin(), ls_buffer.end());
    }
    level_param_names new_ls;
    list<expr> ctx = p.locals_to_context();
    std::tie(type, new_ls) = p.elaborate_type(type, ctx);
    if (k == variable_kind::Variable || k == variable_kind::Parameter)
        update_local_levels(p, new_ls, k == variable_kind::Variable);
    return declare_var(p, p.env(), n, append(ls, new_ls), type, k, bi, pos);
}
static environment variable_cmd(parser & p) {
    return variable_cmd_core(p, variable_kind::Variable);
}
static environment axiom_cmd(parser & p)    {
    return variable_cmd_core(p, variable_kind::Axiom);
}
static environment constant_cmd(parser & p)    {
    return variable_cmd_core(p, variable_kind::Constant);
}
static environment parameter_cmd(parser & p)    {
    return variable_cmd_core(p, variable_kind::Parameter);
}

static environment variables_cmd_core(parser & p, variable_kind k) {
    check_variable_kind(p, k);
    auto pos = p.pos();
    environment env = p.env();

    optional<binder_info> bi = parse_binder_info(p, k);
    buffer<name> ids;
    while (!p.curr_is_token(get_colon_tk())) {
        name id = p.check_id_next("invalid parameters declaration, identifier expected");
        ids.push_back(id);
    }
    p.next();
    optional<parser::local_scope> scope1;
    if (k == variable_kind::Constant || k == variable_kind::Axiom)
        scope1.emplace(p);
    expr type = p.parse_expr();
    p.parse_close_binder_info(bi);
    level_param_names ls = to_level_param_names(collect_univ_params(type));
    list<expr> ctx = p.locals_to_context();
    for (auto id : ids) {
        // Hack: to make sure we get different universe parameters for each parameter.
        // Alternative: elaborate once and copy types replacing universes in new_ls.
        level_param_names new_ls;
        expr new_type;
        check_command_period_open_binder_or_eof(p);
        std::tie(new_type, new_ls) = p.elaborate_type(type, ctx);
        if (k == variable_kind::Variable || k == variable_kind::Parameter)
            update_local_levels(p, new_ls, k == variable_kind::Variable);
        new_ls = append(ls, new_ls);
        env = declare_var(p, env, id, new_ls, new_type, k, bi, pos);
    }
    if (p.curr_is_token(get_lparen_tk()) || p.curr_is_token(get_lcurly_tk()) ||
        p.curr_is_token(get_ldcurly_tk()) || p.curr_is_token(get_lbracket_tk())) {
        if (k == variable_kind::Constant || k == variable_kind::Axiom) {
            // Hack: temporarily update the parser environment.
            // We must do that to be able to process
            //    constants (A : Type) (a : A)
            parser::local_scope scope2(p, env);
            return variables_cmd_core(p, k);
        } else {
            return variables_cmd_core(p, k);
        }
    }
    return env;
}
static environment variables_cmd(parser & p) {
    return variables_cmd_core(p, variable_kind::Variable);
}
static environment parameters_cmd(parser & p) {
    return variables_cmd_core(p, variable_kind::Parameter);
}
static environment constants_cmd(parser & p) {
    return variables_cmd_core(p, variable_kind::Constant);
}

struct decl_attributes {
    bool               m_def_only; // if true only definition attributes are allowed
    bool               m_is_abbrev; // if true only abbreviation attributes are allowed
    bool               m_is_instance;
    bool               m_is_coercion;
    bool               m_is_reducible;
    bool               m_is_irreducible;
    bool               m_is_semireducible;
    bool               m_is_class;
    bool               m_is_parsing_only;
    bool               m_has_multiple_instances;
    optional<unsigned> m_priority;
    optional<unsigned> m_unfold_c_hint;

    decl_attributes(bool def_only = true, bool is_abbrev = false):
        m_priority() {
        m_def_only               = def_only;
        m_is_abbrev              = is_abbrev;
        m_is_instance            = false;
        m_is_coercion            = false;
        m_is_reducible           = is_abbrev;
        m_is_irreducible         = false;
        m_is_semireducible       = false;
        m_is_class               = false;
        m_is_parsing_only        = false;
        m_has_multiple_instances = false;
    }

    struct elim_choice_fn : public replace_visitor {
        name m_prio_ns;
        elim_choice_fn():m_prio_ns(get_priority_namespace()) {}

        virtual expr visit_macro(expr const & e) {
            if (is_choice(e)) {
                for (unsigned i = 0; i < get_num_choices(e); i++) {
                    expr const & c = get_choice(e, i);
                    if (is_constant(c) && const_name(c).get_prefix() == m_prio_ns)
                        return c;
                }
                throw exception("invalid priority expression, it contains overloaded symbols");
            } else {
                return replace_visitor::visit_macro(e);
            }
        }
    };

    optional<unsigned> parse_instance_priority(parser & p) {
        if (p.curr_is_token(get_priority_tk())) {
            p.next();
            auto pos = p.pos();
            environment env = open_priority_aliases(open_num_notation(p.env()));
            parser::local_scope scope(p, env);
            expr val = p.parse_expr();
            val = elim_choice_fn()(val);
            val = normalize(p.env(), val);
            if (optional<mpz> mpz_val = to_num(val)) {
                if (!mpz_val->is_unsigned_int())
                    throw parser_error("invalid 'priority', argument does not fit in a machine integer", pos);
                p.check_token_next(get_rbracket_tk(), "invalid 'priority', ']' expected");
                return optional<unsigned>(mpz_val->get_unsigned_int());
            } else {
                throw parser_error("invalid 'priority', argument does not evaluate to a numeral", pos);
            }
        } else {
            return optional<unsigned>();
        }
    }

    void parse(buffer<name> const & ns, parser & p) {
        while (true) {
            auto pos = p.pos();
            if (p.curr_is_token(get_instance_tk())) {
                m_is_instance = true;
                p.next();
            } else if (p.curr_is_token(get_coercion_tk())) {
                auto pos = p.pos();
                p.next();
                if (in_context(p.env()))
                    throw parser_error("invalid '[coercion]' attribute, coercions cannot be defined in contexts", pos);
                m_is_coercion = true;
            } else if (p.curr_is_token(get_reducible_tk())) {
                if (m_is_irreducible || m_is_semireducible)
                    throw parser_error("invalid '[reducible]' attribute, '[irreducible]' or '[semireducible]' was already provided", pos);
                m_is_reducible = true;
                p.next();
            } else if (p.curr_is_token(get_irreducible_tk())) {
                if (m_is_reducible || m_is_semireducible)
                    throw parser_error("invalid '[irreducible]' attribute, '[reducible]' or '[semireducible]' was already provided", pos);
                m_is_irreducible = true;
                p.next();
            } else if (p.curr_is_token(get_semireducible_tk())) {
                if (m_is_reducible || m_is_irreducible)
                    throw parser_error("invalid '[irreducible]' attribute, '[reducible]' or '[irreducible]' was already provided", pos);
                m_is_semireducible = true;
                p.next();
            } else if (p.curr_is_token(get_class_tk())) {
                if (m_def_only)
                    throw parser_error("invalid '[class]' attribute, definitions cannot be marked as classes", pos);
                m_is_class = true;
                p.next();
            } else if (p.curr_is_token(get_multiple_instances_tk())) {
                if (m_def_only)
                    throw parser_error("invalid '[multiple-instances]' attribute, only classes can have this attribute", pos);
                m_has_multiple_instances = true;
                p.next();
            } else if (auto it = parse_instance_priority(p)) {
                m_priority = *it;
                if (!m_is_instance) {
                    if (ns.empty()) {
                        throw parser_error("invalid '[priority]' attribute, declaration must be marked as an '[instance]'", pos);
                    } else {
                        for (name const & n : ns) {
                            if (!is_instance(p.env(), n))
                                throw parser_error(sstream() << "invalid '[priority]' attribute, declaration '" << n
                                                   << "' must be marked as an '[instance]'", pos);
                        }
                        m_is_instance = true;
                    }
                }
            } else if (p.curr_is_token(get_parsing_only_tk())) {
                if (!m_is_abbrev)
                    throw parser_error("invalid '[parsing-only]' attribute, only abbreviations can be "
                                       "marked as '[parsing-only]'", pos);
                m_is_parsing_only = true;
                p.next();
            } else if (p.curr_is_token(get_unfold_c_tk())) {
                p.next();
                unsigned r = p.parse_small_nat();
                if (r == 0)
                    throw parser_error("invalid '[unfold-c]' attribute, value must be greater than 0", pos);
                m_unfold_c_hint = r - 1;
                p.check_token_next(get_rbracket_tk(), "invalid 'unfold-c', ']' expected");
            } else {
                break;
            }
        }
    }

    void parse(name const & n, parser & p) {
        buffer<name> ns;
        ns.push_back(n);
        parse(ns, p);
    }

    void parse(parser & p) {
        buffer<name> ns;
        parse(ns, p);
    }

    environment apply(environment env, io_state const & ios, name const & d, bool persistent) {
        if (m_is_instance) {
            if (m_priority) {
                #if defined(__GNUC__) && !defined(__CLANG__)
                #pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
                #endif
                env = add_instance(env, d, *m_priority, persistent);
            } else {
                env = add_instance(env, d, persistent);
            }
        }
        if (m_is_coercion)
            env = add_coercion(env, d, ios, persistent);
        if (m_is_reducible)
            env = set_reducible(env, d, reducible_status::Reducible, persistent);
        if (m_is_irreducible)
            env = set_reducible(env, d, reducible_status::Irreducible, persistent);
        if (m_is_semireducible)
            env = set_reducible(env, d, reducible_status::Semireducible, persistent);
        if (m_is_class)
            env = add_class(env, d, persistent);
        if (m_has_multiple_instances)
            env = mark_multiple_instances(env, d, persistent);
        if (m_unfold_c_hint)
            env = add_unfold_c_hint(env, d, m_unfold_c_hint, persistent);
        return env;
    }
};

static void check_end_of_theorem(parser const & p) {
    if (!p.curr_is_command_like())
        throw parser_error("':=', '.', command, script, or end-of-file expected", p.pos());
}

static void erase_local_binder_info(buffer<expr> & ps) {
    for (expr & p : ps)
        p = update_local(p, binder_info());
}

static bool is_curr_with_or_comma_or_bar(parser & p) {
    return p.curr_is_token(get_with_tk()) || p.curr_is_token(get_comma_tk()) || p.curr_is_token(get_bar_tk());
}

/**
   For convenience, the left-hand-side of a recursive equation may contain
   undeclared variables.
   We use parser::undef_id_to_local_scope to force the parser to create a local constant for
   each undefined identifier.

   This method validates occurrences of these variables. They can only occur as an application
   or macro argument.
*/
static void validate_equation_lhs(parser const & p, expr const & lhs, buffer<expr> const & locals) {
    if (is_app(lhs)) {
        validate_equation_lhs(p, app_fn(lhs), locals);
        validate_equation_lhs(p, app_arg(lhs), locals);
    } else if (is_macro(lhs)) {
        for (unsigned i = 0; i < macro_num_args(lhs); i++)
            validate_equation_lhs(p, macro_arg(lhs, i), locals);
    } else if (!is_local(lhs)) {
        for_each(lhs, [&](expr const & e, unsigned) {
                if (is_local(e) &&
                    std::any_of(locals.begin(), locals.end(), [&](expr const & local) {
                            return mlocal_name(e) == mlocal_name(local);
                        })) {
                    throw parser_error(sstream() << "invalid occurrence of variable '" << mlocal_name(lhs) <<
                                       "' in the left-hand-side of recursive equation", p.pos_of(lhs));
                }
                return has_local(e);
            });
    }
}

/**
   \brief Merge multiple occurrences of a variable in the left-hand-side of a recursive equation.

   \see validate_equation_lhs
*/
static expr merge_equation_lhs_vars(expr const & lhs, buffer<expr> & locals) {
    expr_map<expr> m;
    unsigned j = 0;
    for (unsigned i = 0; i < locals.size(); i++) {
        unsigned k;
        for (k = 0; k < i; k++) {
            if (mlocal_name(locals[k]) == mlocal_name(locals[i])) {
                m.insert(mk_pair(locals[i], locals[k]));
                break;
            }
        }
        if (k == i) {
            locals[j] = locals[i];
            j++;
        }
    }
    if (j == locals.size())
        return lhs;
    locals.shrink(j);
    return replace(lhs, [&](expr const & e) {
            if (!has_local(e))
                return some_expr(e);
            if (is_local(e)) {
                auto it = m.find(e);
                if (it != m.end())
                    return some_expr(it->second);
            }
            return none_expr();
        });
}

static void throw_invalid_equation_lhs(name const & n, pos_info const & p) {
    throw parser_error(sstream() << "invalid recursive equation, head symbol '"
                       << n << "' in the left-hand-side does not correspond to function(s) being defined", p);
}

static bool is_eqn_prefix(parser & p) {
    return p.curr_is_token(get_bar_tk()) || p.curr_is_token(get_comma_tk());
}

static void check_eqn_prefix(parser & p) {
    if (!is_eqn_prefix(p))
        throw parser_error("invalid declaration, ',' or '|' expected", p.pos());
    p.next();
}

expr parse_equations(parser & p, name const & n, expr const & type, buffer<name> & auxs,
                     optional<local_environment> const & lenv, buffer<expr> const & ps,
                     pos_info const & def_pos) {
    buffer<expr> eqns;
    buffer<expr> fns;
    {
        parser::local_scope scope1(p, lenv);
        for (expr const & param : ps)
            p.add_local(param);
        lean_assert(is_curr_with_or_comma_or_bar(p));
        fns.push_back(mk_local(n, type));
        if (p.curr_is_token(get_with_tk())) {
            while (p.curr_is_token(get_with_tk())) {
                p.next();
                auto pos = p.pos();
                name g_name = p.check_id_next("invalid declaration, identifier expected");
                p.check_token_next(get_colon_tk(), "invalid declaration, ':' expected");
                expr g_type = p.parse_expr();
                expr g      = p.save_pos(mk_local(g_name, g_type), pos);
                auxs.push_back(g_name);
                fns.push_back(g);
            }
        }
        check_eqn_prefix(p);
        for (expr const & fn : fns)
            p.add_local(fn);
        while (true) {
            expr lhs;
            unsigned prev_num_undef_ids = p.get_num_undef_ids();
            buffer<expr> locals;
            {
                parser::undef_id_to_local_scope scope2(p);
                auto lhs_pos = p.pos();
                lhs = p.parse_expr();
                expr lhs_fn = get_app_fn(lhs);
                if (is_explicit(lhs_fn))
                    lhs_fn = get_explicit_arg(lhs_fn);
                if (is_constant(lhs_fn))
                    throw_invalid_equation_lhs(const_name(lhs_fn), lhs_pos);
                if (is_local(lhs_fn) && std::all_of(fns.begin(), fns.end(), [&](expr const & fn) { return fn != lhs_fn; }))
                    throw_invalid_equation_lhs(local_pp_name(lhs_fn), lhs_pos);
                if (!is_local(lhs_fn))
                    throw parser_error("invalid recursive equation, head symbol in left-hand-side is not a constant", lhs_pos);
                unsigned num_undef_ids = p.get_num_undef_ids();
                for (unsigned i = prev_num_undef_ids; i < num_undef_ids; i++) {
                    locals.push_back(p.get_undef_id(i));
                }
            }
            validate_equation_lhs(p, lhs, locals);
            lhs = merge_equation_lhs_vars(lhs, locals);
            auto assign_pos = p.pos();
            p.check_token_next(get_assign_tk(), "invalid declaration, ':=' expected");
            {
                parser::local_scope scope2(p);
                for (expr const & local : locals)
                    p.add_local(local);
                expr rhs = p.parse_expr();
                eqns.push_back(Fun(fns, Fun(locals, p.save_pos(mk_equation(lhs, rhs), assign_pos), p)));
            }
            if (!is_eqn_prefix(p))
                break;
            p.next();
        }
    }
    if (p.curr_is_token(get_wf_tk())) {
        auto pos = p.pos();
        p.next();
        expr R   = p.save_pos(mk_expr_placeholder(), pos);
        expr Hwf = p.parse_expr();
        return p.save_pos(mk_equations(fns.size(), eqns.size(), eqns.data(), R, Hwf), def_pos);
    } else {
        return p.save_pos(mk_equations(fns.size(), eqns.size(), eqns.data()), def_pos);
    }
}

/** \brief Use equations compiler infrastructure to implement match-with */
expr parse_match(parser & p, unsigned, expr const *, pos_info const & pos) {
    expr t  = p.parse_expr();
    buffer<expr> eqns;
    p.check_token_next(get_with_tk(), "invalid 'match' expression, 'with' expected");
    expr fn = mk_local(p.mk_fresh_name(), "match", mk_expr_placeholder(), binder_info());
    if (p.curr_is_token(get_end_tk())) {
        p.next();
        // empty match-with
        eqns.push_back(Fun(fn, mk_no_equation()));
        expr f = p.save_pos(mk_equations(1, eqns.size(), eqns.data()), pos);
        return p.mk_app(f, t, pos);
    }
    if (is_eqn_prefix(p))
        p.next(); // optional '|' in the first case
    while (true) {
        expr lhs;
        unsigned prev_num_undef_ids = p.get_num_undef_ids();
        buffer<expr> locals;
        {
            parser::undef_id_to_local_scope scope2(p);
            auto lhs_pos = p.pos();
            lhs = p.parse_expr();
            lhs = p.mk_app(fn, lhs, lhs_pos);
            unsigned num_undef_ids = p.get_num_undef_ids();
            for (unsigned i = prev_num_undef_ids; i < num_undef_ids; i++) {
                locals.push_back(p.get_undef_id(i));
            }
        }
        validate_equation_lhs(p, lhs, locals);
        lhs = merge_equation_lhs_vars(lhs, locals);
        auto assign_pos = p.pos();
        p.check_token_next(get_assign_tk(), "invalid 'match' expression, ':=' expected");
        {
            parser::local_scope scope2(p);
            for (expr const & local : locals)
                p.add_local(local);
            expr rhs = p.parse_expr();
            eqns.push_back(Fun(fn, Fun(locals, p.save_pos(mk_equation(lhs, rhs), assign_pos), p)));
        }
        if (!is_eqn_prefix(p))
            break;
        p.next();
    }
    p.check_token_next(get_end_tk(), "invalid 'match' expression, 'end' expected");
    expr f = p.save_pos(mk_equations(1, eqns.size(), eqns.data()), pos);
    return p.mk_app(f, t, pos);
}

// An Lean example is not really a definition, but we use the definition infrastructure to simulate it.
enum def_cmd_kind { Theorem, Definition, Example, Abbreviation, LocalAbbreviation };

class definition_cmd_fn {
    parser &          m_p;
    environment       m_env;
    def_cmd_kind      m_kind;
    bool              m_is_opaque;
    bool              m_is_private;
    bool              m_is_protected;
    pos_info          m_pos;

    name              m_name;
    decl_attributes   m_attributes;
    name              m_real_name; // real name for this declaration
    buffer<name>      m_ls_buffer;
    buffer<name>      m_aux_decls; // user provided names for aux_decls
    buffer<name>      m_real_aux_names; // real names for aux_decls
    buffer<expr>      m_aux_types; // types of auxiliary decls
    expr              m_type;
    expr              m_value;
    level_param_names m_ls;
    pos_info          m_end_pos;

    expr              m_pre_type;
    expr              m_pre_value;

    bool is_definition() const { return m_kind == Definition || m_kind == Abbreviation || m_kind == LocalAbbreviation; }
    unsigned start_line() const { return m_pos.first; }
    unsigned end_line() const { return m_end_pos.first; }

    void parse_name() {
        if (m_kind == Example)
            m_name = m_p.mk_fresh_name();
        else
            m_name = m_p.check_id_next("invalid declaration, identifier expected");
    }

    void parse_type_value() {
        // Parse universe parameters
        parser::local_scope scope1(m_p);
        parse_univ_params(m_p, m_ls_buffer);

        // Parse modifiers
        m_attributes.parse(m_p);

        if (m_p.curr_is_token(get_assign_tk())) {
            auto pos = m_p.pos();
            m_p.next();
            m_type  = m_p.save_pos(mk_expr_placeholder(), pos);
            m_value = m_p.parse_expr();
        } else if (m_p.curr_is_token(get_colon_tk())) {
            m_p.next();
            auto pos = m_p.pos();
            m_type = m_p.parse_expr();
            if (is_curr_with_or_comma_or_bar(m_p)) {
                m_value = parse_equations(m_p, m_name, m_type, m_aux_decls,
                                          optional<local_environment>(), buffer<expr>(), m_pos);
            } else if (!is_definition() && !m_p.curr_is_token(get_assign_tk())) {
                check_end_of_theorem(m_p);
                m_value = m_p.save_pos(mk_expr_placeholder(), pos);
            } else {
                m_p.check_token_next(get_assign_tk(), "invalid declaration, ':=' expected");
                m_value = m_p.save_pos(m_p.parse_expr(), pos);
            }
        } else {
            buffer<expr> ps;
            optional<local_environment> lenv;
            bool last_block_delimited = false;
            lenv     = m_p.parse_binders(ps, last_block_delimited);
            auto pos = m_p.pos();
            if (m_p.curr_is_token(get_colon_tk())) {
                m_p.next();
                m_type = m_p.parse_scoped_expr(ps, *lenv);
                if (is_curr_with_or_comma_or_bar(m_p)) {
                    m_value = parse_equations(m_p, m_name, m_type, m_aux_decls, lenv, ps, m_pos);
                } else if (!is_definition() && !m_p.curr_is_token(get_assign_tk())) {
                    check_end_of_theorem(m_p);
                    m_value = m_p.save_pos(mk_expr_placeholder(), pos);
                } else {
                    m_p.check_token_next(get_assign_tk(), "invalid declaration, ':=' expected");
                    m_value = m_p.parse_scoped_expr(ps, *lenv);
                }
            } else {
                if (!last_block_delimited && !ps.empty() &&
                    !is_placeholder(mlocal_type(ps.back()))) {
                    throw parser_error("invalid declaration, ambiguous parameter declaration, "
                                       "(solution: put parentheses around parameters)",
                                       pos);
                }
                m_type = m_p.save_pos(mk_expr_placeholder(), m_p.pos());
                m_p.check_token_next(get_assign_tk(), "invalid declaration, ':=' expected");
                m_value = m_p.parse_scoped_expr(ps, *lenv);
            }
            m_type  = Pi(ps, m_type, m_p);
            erase_local_binder_info(ps);
            m_value = Fun(ps, m_value, m_p);
        }
        m_end_pos = m_p.pos();
    }

    void mk_real_name() {
        if (m_is_private) {
            unsigned h  = hash(m_pos.first, m_pos.second);
            auto env_n  = add_private_name(m_env, m_name, optional<unsigned>(h));
            m_env       = env_n.first;
            m_real_name = env_n.second;
            for (name const & aux : m_aux_decls) {
                auto env_n = add_private_name(m_env, aux, optional<unsigned>(h));
                m_env      = env_n.first;
                m_real_aux_names.push_back(env_n.second);
            }
        } else {
            name const & ns = get_namespace(m_env);
            m_real_name     = ns + m_name;
            for (name const & aux : m_aux_decls)
                m_real_aux_names.push_back(ns + aux);
        }
    }

    void parse() {
        parse_name();
        parse_type_value();
        check_command_period_or_eof(m_p);
        if (m_p.used_sorry())
            m_p.declare_sorry();
        m_env = m_p.env();
        mk_real_name();
    }

    void process_locals() {
        if (m_p.has_locals()) {
            buffer<expr> locals;
            collect_locals(m_type, m_value, m_p, locals);
            m_type = Pi_as_is(locals, m_type, m_p);
            buffer<expr> new_locals;
            new_locals.append(locals);
            erase_local_binder_info(new_locals);
            m_value = Fun_as_is(new_locals, m_value, m_p);
            auto ps = collect_univ_params_ignoring_tactics(m_type);
            ps      = collect_univ_params_ignoring_tactics(m_value, ps);
            update_univ_parameters(m_ls_buffer, ps, m_p);
            remove_local_vars(m_p, locals);
            m_ls = to_list(m_ls_buffer.begin(), m_ls_buffer.end());
            levels local_ls = collect_local_nonvar_levels(m_p, m_ls);
            local_ls = remove_local_vars(m_p, local_ls);
            if (!locals.empty()) {
                expr ref = mk_local_ref(m_real_name, local_ls, locals);
                m_p.add_local_expr(m_name, ref);
            } else if (local_ls) {
                expr ref = mk_constant(m_real_name, local_ls);
                m_p.add_local_expr(m_name, ref);
            }
        } else {
            update_univ_parameters(m_ls_buffer, collect_univ_params(m_value, collect_univ_params(m_type)), m_p);
            m_ls = to_list(m_ls_buffer.begin(), m_ls_buffer.end());
        }
    }

    bool try_cache() {
        // We don't cache examples.
        // We don't cache mutually recursive definitions (if this becomes a performance problem, we can fix it).
        if (m_kind != Example &&
            m_p.are_info_lines_valid(start_line(), end_line()) &&
            m_aux_decls.size() == 0) {
            // we only use the cache if the information associated with the line is valid
            if (auto it = m_p.find_cached_definition(m_real_name, m_type, m_value)) {
                optional<certified_declaration> cd;
                try {
                    level_param_names c_ls; expr c_type, c_value;
                    std::tie(c_ls, c_type, c_value) = *it;
                    // cache may have been created using a different trust level
                    c_type  = expand_abbreviations(m_env, unfold_untrusted_macros(m_env, c_type));
                    c_value = expand_abbreviations(m_env, unfold_untrusted_macros(m_env, c_value));
                    if (m_kind == Theorem) {
                        cd = check(m_env, mk_theorem(m_real_name, c_ls, c_type, c_value));
                        if (!m_p.keep_new_thms()) {
                            // discard theorem
                            cd = check(m_env, mk_axiom(m_real_name, c_ls, c_type));
                        }
                    } else {
                        cd = check(m_env, mk_definition(m_env, m_real_name, c_ls, c_type, c_value, m_is_opaque));
                    }
                    if (!m_is_private)
                        m_p.add_decl_index(m_real_name, m_pos, m_p.get_cmd_token(), c_type);
                    m_env = module::add(m_env, *cd);
                    return true;
                } catch (exception&) {}
            }
        }
        return false;
    }

    void register_decl(name const & n, name const & real_n, expr const & type) {
        if (m_kind != Example) {
            // TODO(Leo): register aux_decls
            if (!m_is_private)
                m_p.add_decl_index(real_n, m_pos, m_p.get_cmd_token(), type);
            if (m_is_protected)
                m_env = add_protected(m_env, real_n);
            if (n != real_n)
                m_env = add_expr_alias_rec(m_env, n, real_n);
            if (m_kind == Abbreviation || m_kind == LocalAbbreviation) {
                bool persistent = m_kind == Abbreviation;
                m_env = add_abbreviation(m_env, real_n, m_attributes.m_is_parsing_only, persistent);
            }
            bool persistent = true;
            m_env = m_attributes.apply(m_env, m_p.ios(), real_n, persistent);
        }
    }

    void register_decl() {
        register_decl(m_name, m_real_name, m_type);
        for (unsigned i = 0; i < m_aux_decls.size(); i++) {
            register_decl(m_aux_decls[i], m_real_aux_names[i], m_aux_types[i]);
        }
    }

    // When compiling mutually recursive equations or equations based on well-found recursion,
    // the equations compiler produces a result that combines different definitions.
    // We say the result is "tangled". This method untangles it.
    // The tangled result is of the form
    //     Fun (a : A), [equations_result main-value aux-type-1 aux-value-1 ... aux-type-i aux-value-i]
    //
    // The result is the updated value. The auxiliary definitions (type and value) are stored at m_aux_types and aux_values
    expr untangle_definitions(expr const & type, expr const & value, buffer<expr> & aux_values) {
        if (is_lambda(value)) {
            lean_assert(is_pi(type));
            expr r = untangle_definitions(binding_body(type), binding_body(value), aux_values);
            lean_assert(aux_values.size() == m_aux_types.size());
            for (unsigned i = 0; i < aux_values.size(); i++) {
                m_aux_types[i] = mk_pi(binding_name(type), binding_domain(type), m_aux_types[i], binding_info(type));
                aux_values[i]  = mk_lambda(binding_name(value), binding_domain(value), aux_values[i], binding_info(value));
            }
            return update_binding(value, binding_domain(value), r);
        } else if (is_equations_result(value)) {
            lean_assert(get_equations_result_size(value) > 1);
            lean_assert(get_equations_result_size(value) % 2 == 1);
            for (unsigned i = 1; i < get_equations_result_size(value); i+=2) {
                m_aux_types.push_back(get_equations_result(value, i));
                aux_values.push_back(get_equations_result(value, i+1));
            }
            return get_equations_result(value, 0);
        } else {
            throw exception("invalid declaration, unexpected result produced by equations compiler");
        }
    }

    // Elaborate definitions that contain auxiliary ones nested inside.
    // Remark: we do not cache this kind of definition.
    // This method will also initialize m_aux_types
    void elaborate_multi() {
        lean_assert(!m_aux_decls.empty());
        level_param_names new_ls;
        std::tie(m_type, m_value, new_ls) = m_p.elaborate_definition(m_name, m_type, m_value, m_is_opaque);
        new_ls = append(m_ls, new_ls);
        lean_assert(m_aux_types.empty());
        buffer<expr> aux_values;
        m_value = untangle_definitions(m_type, m_value, aux_values);
        lean_assert(aux_values.size() == m_aux_types.size());
        if (aux_values.size() != m_real_aux_names.size())
            throw exception("invalid declaration, failed to compile auxiliary declarations");
        m_type  = expand_abbreviations(m_env, unfold_untrusted_macros(m_env, m_type));
        m_value = expand_abbreviations(m_env, unfold_untrusted_macros(m_env, m_value));
        for (unsigned i = 0; i < aux_values.size(); i++) {
            m_aux_types[i] = expand_abbreviations(m_env, unfold_untrusted_macros(m_env, m_aux_types[i]));
            aux_values[i]  = expand_abbreviations(m_env, unfold_untrusted_macros(m_env, aux_values[i]));
        }
        if (is_definition()) {
            m_env = module::add(m_env, check(m_env, mk_definition(m_env, m_real_name, new_ls,
                                                                  m_type, m_value, m_is_opaque)));
            for (unsigned i = 0; i < aux_values.size(); i++)
                m_env = module::add(m_env, check(m_env, mk_definition(m_env, m_real_aux_names[i], new_ls,
                                                                      m_aux_types[i], aux_values[i], m_is_opaque)));
        } else {
            m_env = module::add(m_env, check(m_env, mk_theorem(m_real_name, new_ls, m_type, m_value)));
            for (unsigned i = 0; i < aux_values.size(); i++)
                m_env = module::add(m_env, check(m_env, mk_theorem(m_real_aux_names[i], new_ls,
                                                                   m_aux_types[i], aux_values[i])));
        }
    }

    void elaborate() {
        if (!try_cache()) {
            expr pre_type  = m_type;
            expr pre_value = m_value;
            level_param_names new_ls;
            m_p.remove_proof_state_info(m_pos, m_p.pos());
            if (!m_aux_decls.empty()) {
                // TODO(Leo): split equations_result
                elaborate_multi();
            } else if (!is_definition()) {
                // Theorems and Examples
                auto type_pos = m_p.pos_of(m_type);
                bool clear_pre_info = false; // we don't want to clear pre_info data until we process the proof.
                std::tie(m_type, new_ls) = m_p.elaborate_type(m_type, list<expr>(), clear_pre_info);
                check_no_metavar(m_env, m_real_name, m_type, true);
                m_ls = append(m_ls, new_ls);
                m_type = expand_abbreviations(m_env, unfold_untrusted_macros(m_env, m_type));
                expr type_as_is = m_p.save_pos(mk_as_is(m_type), type_pos);
                if (!m_p.collecting_info() && m_kind == Theorem && m_p.num_threads() > 1) {
                    // Add as axiom, and create a task to prove the theorem.
                    // Remark: we don't postpone the "proof" of Examples.
                    m_p.add_delayed_theorem(m_env, m_real_name, m_ls, type_as_is, m_value);
                    m_env = module::add(m_env, check(m_env, mk_axiom(m_real_name, m_ls, m_type)));
                } else {
                    std::tie(m_type, m_value, new_ls) = m_p.elaborate_definition(m_name, type_as_is, m_value, m_is_opaque);
                    m_type  = expand_abbreviations(m_env, unfold_untrusted_macros(m_env, m_type));
                    m_value = expand_abbreviations(m_env, unfold_untrusted_macros(m_env, m_value));
                    new_ls = append(m_ls, new_ls);
                    auto cd = check(m_env, mk_theorem(m_real_name, new_ls, m_type, m_value));
                    if (m_kind == Theorem) {
                        // Remark: we don't keep examples
                        if (!m_p.keep_new_thms()) {
                            // discard theorem
                            cd = check(m_env, mk_axiom(m_real_name, new_ls, m_type));
                        }
                        m_env = module::add(m_env, cd);
                        m_p.cache_definition(m_real_name, pre_type, pre_value, new_ls, m_type, m_value);
                    }
                }
            } else {
                std::tie(m_type, m_value, new_ls) = m_p.elaborate_definition(m_name, m_type, m_value, m_is_opaque);
                new_ls = append(m_ls, new_ls);
                m_type  = expand_abbreviations(m_env, unfold_untrusted_macros(m_env, m_type));
                m_value = expand_abbreviations(m_env, unfold_untrusted_macros(m_env, m_value));
                m_env = module::add(m_env, check(m_env, mk_definition(m_env, m_real_name, new_ls,
                                                                      m_type, m_value, m_is_opaque)));
                m_p.cache_definition(m_real_name, pre_type, pre_value, new_ls, m_type, m_value);
            }
        }
    }

public:
    definition_cmd_fn(parser & p, def_cmd_kind kind, bool is_opaque, bool is_private, bool is_protected):
        m_p(p), m_env(m_p.env()), m_kind(kind), m_is_opaque(is_opaque),
        m_is_private(is_private), m_is_protected(is_protected),
        m_pos(p.pos()), m_attributes(true, kind == Abbreviation || kind == LocalAbbreviation) {
        lean_assert(!(!is_definition() && !m_is_opaque));
        lean_assert(!(m_is_private && m_is_protected));
    }

    environment operator()() {
        parse();
        process_locals();
        elaborate();
        register_decl();
        return m_env;
    }
};

static environment definition_cmd_core(parser & p, def_cmd_kind kind, bool is_opaque, bool is_private, bool is_protected) {
    return definition_cmd_fn(p, kind, is_opaque, is_private, is_protected)();
}
static environment definition_cmd(parser & p) {
    return definition_cmd_core(p, Definition, false, false, false);
}
static environment abbreviation_cmd(parser & p) {
    return definition_cmd_core(p, Abbreviation, false, false, false);
}
environment local_abbreviation_cmd(parser & p) {
    return definition_cmd_core(p, LocalAbbreviation, false, true, false);
}
static environment opaque_definition_cmd(parser & p) {
    p.check_token_next(get_definition_tk(), "invalid 'opaque' definition, 'definition' expected");
    return definition_cmd_core(p, Definition, true, false, false);
}
static environment theorem_cmd(parser & p) {
    return definition_cmd_core(p, Theorem, true, false, false);
}
static environment example_cmd(parser & p) {
    return definition_cmd_core(p, Example, true, false, false);
}
static environment private_definition_cmd(parser & p) {
    def_cmd_kind kind = Definition;
    bool is_opaque  = false;
    if (p.curr_is_token_or_id(get_opaque_tk())) {
        is_opaque = true;
        p.next();
        p.check_token_next(get_definition_tk(), "invalid 'private' definition, 'definition' expected");
    } else if (p.curr_is_token_or_id(get_definition_tk())) {
        p.next();
    } else if (p.curr_is_token_or_id(get_abbreviation_tk())) {
        kind = Abbreviation;
        p.next();
    } else if (p.curr_is_token_or_id(get_theorem_tk())) {
        p.next();
        kind = Theorem;
        is_opaque  = true;
    } else {
        throw parser_error("invalid 'private' definition/theorem, 'definition' or 'theorem' expected", p.pos());
    }
    return definition_cmd_core(p, kind, is_opaque, true, false);
}
static environment protected_definition_cmd(parser & p) {
    def_cmd_kind kind = Definition;
    bool is_opaque  = false;
    if (p.curr_is_token_or_id(get_opaque_tk())) {
        is_opaque = true;
        p.next();
        p.check_token_next(get_definition_tk(), "invalid 'protected' definition, 'definition' expected");
    } else if (p.curr_is_token_or_id(get_definition_tk())) {
        p.next();
    } else if (p.curr_is_token_or_id(get_abbreviation_tk())) {
        p.next();
        kind = Abbreviation;
    } else if (p.curr_is_token_or_id(get_theorem_tk())) {
        p.next();
        kind       = Theorem;
        is_opaque  = true;
    } else {
        throw parser_error("invalid 'protected' definition/theorem, 'definition' or 'theorem' expected", p.pos());
    }
    return definition_cmd_core(p, kind, is_opaque, false, true);
}

static environment include_cmd_core(parser & p, bool include) {
    if (!p.curr_is_identifier())
        throw parser_error(sstream() << "invalid include/omit command, identifier expected", p.pos());
    while (p.curr_is_identifier()) {
        auto pos = p.pos();
        name n = p.get_name_val();
        p.next();
        if (!p.get_local(n))
            throw parser_error(sstream() << "invalid include/omit command, '" << n << "' is not a parameter/variable", pos);
        if (include) {
            if (p.is_include_variable(n))
                throw parser_error(sstream() << "invalid include command, '" << n << "' has already been included", pos);
            p.include_variable(n);
        } else {
            if (!p.is_include_variable(n))
                throw parser_error(sstream() << "invalid omit command, '" << n << "' has not been included", pos);
            p.omit_variable(n);
        }
    }
    return p.env();
}

static environment include_cmd(parser & p) {
    return include_cmd_core(p, true);
}

static environment omit_cmd(parser & p) {
    return include_cmd_core(p, false);
}

static environment attribute_cmd_core(parser & p, bool persistent) {
    buffer<name> ds;
    name d          = p.check_constant_next("invalid 'attribute' command, constant expected");
    ds.push_back(d);
    while (p.curr_is_identifier()) {
        ds.push_back(p.check_constant_next("invalid 'attribute' command, constant expected"));
    }
    bool decl_only  = false;
    decl_attributes attributes(decl_only);
    attributes.parse(ds, p);
    environment env = p.env();
    for (name const & d : ds)
        env = attributes.apply(env, p.ios(), d, persistent);
    return env;
}

static environment attribute_cmd(parser & p) {
    return attribute_cmd_core(p, true);
}

environment local_attribute_cmd(parser & p) {
    return attribute_cmd_core(p, false);
}

void register_decl_cmds(cmd_table & r) {
    add_cmd(r, cmd_info("universe",     "declare a universe level", universe_cmd));
    add_cmd(r, cmd_info("universes",    "declare universe levels", universes_cmd));
    add_cmd(r, cmd_info("variable",     "declare a new variable", variable_cmd));
    add_cmd(r, cmd_info("parameter",    "declare a new parameter", parameter_cmd));
    add_cmd(r, cmd_info("constant",     "declare a new constant (aka top-level variable)", constant_cmd));
    add_cmd(r, cmd_info("axiom",        "declare a new axiom", axiom_cmd));
    add_cmd(r, cmd_info("variables",    "declare new variables", variables_cmd));
    add_cmd(r, cmd_info("parameters",   "declare new parameters", parameters_cmd));
    add_cmd(r, cmd_info("constants",    "declare new constants (aka top-level variables)", constants_cmd));
    add_cmd(r, cmd_info("definition",   "add new definition", definition_cmd));
    add_cmd(r, cmd_info("example",      "add new example", example_cmd));
    add_cmd(r, cmd_info("opaque",       "add new opaque definition", opaque_definition_cmd));
    add_cmd(r, cmd_info("private",      "add new private definition/theorem", private_definition_cmd));
    add_cmd(r, cmd_info("protected",    "add new protected definition/theorem", protected_definition_cmd));
    add_cmd(r, cmd_info("theorem",      "add new theorem", theorem_cmd));
    add_cmd(r, cmd_info("include",      "force section parameter/variable to be included", include_cmd));
    add_cmd(r, cmd_info("attribute",    "set declaration attributes", attribute_cmd));
    add_cmd(r, cmd_info("abbreviation", "declare a new abbreviation", abbreviation_cmd));
    add_cmd(r, cmd_info("omit",         "undo 'include' command", omit_cmd));
}
}
