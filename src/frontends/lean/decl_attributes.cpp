/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/replace_visitor.h"
#include "library/choice.h"
#include "library/normalize.h"
#include "library/reducible.h"
#include "library/class.h"
#include "library/relation_manager.h"
#include "library/user_recursors.h"
#include "library/coercion.h"
#include "library/num.h"
#include "library/simplifier/rewrite_rule_set.h"
#include "frontends/lean/decl_attributes.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/util.h"

namespace lean {
decl_attributes::decl_attributes(bool def_only, bool is_abbrev, bool persistent):
    m_priority() {
    m_def_only               = def_only;
    m_is_abbrev              = is_abbrev;
    m_persistent             = persistent;
    m_is_instance            = false;
    m_is_coercion            = false;
    m_is_reducible           = is_abbrev;
    m_is_irreducible         = false;
    m_is_semireducible       = false;
    m_is_quasireducible      = false;
    m_is_class               = false;
    m_is_parsing_only        = false;
    m_has_multiple_instances = false;
    m_unfold_f_hint          = false;
    m_constructor_hint       = false;
    m_symm                   = false;
    m_trans                  = false;
    m_refl                   = false;
    m_subst                  = false;
    m_recursor               = false;
    m_rewrite                = false;
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

optional<unsigned> decl_attributes::parse_instance_priority(parser & p) {
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

void decl_attributes::parse(buffer<name> const & ns, parser & p) {
    while (true) {
        auto pos = p.pos();
        if (p.curr_is_token(get_instance_tk())) {
            m_is_instance = true;
            p.next();
        } else if (p.curr_is_token(get_coercion_tk())) {
            p.next();
            m_is_coercion = true;
        } else if (p.curr_is_token(get_reducible_tk())) {
            if (m_is_irreducible || m_is_semireducible || m_is_quasireducible)
                throw parser_error("invalid '[reducible]' attribute, '[irreducible]', '[quasireducible]' or '[semireducible]' was already provided", pos);
            m_is_reducible = true;
            p.next();
        } else if (p.curr_is_token(get_irreducible_tk())) {
            if (m_is_reducible || m_is_semireducible || m_is_quasireducible)
                throw parser_error("invalid '[irreducible]' attribute, '[reducible]', '[quasireducible]' or '[semireducible]' was already provided", pos);
            m_is_irreducible = true;
            p.next();
        } else if (p.curr_is_token(get_semireducible_tk())) {
            if (m_is_reducible || m_is_irreducible || m_is_quasireducible)
                throw parser_error("invalid '[irreducible]' attribute, '[reducible]', '[quasireducible]' or '[irreducible]' was already provided", pos);
            m_is_semireducible = true;
            p.next();
        } else if (p.curr_is_token(get_quasireducible_tk())) {
            if (m_is_reducible || m_is_irreducible || m_is_semireducible)
                throw parser_error("invalid '[quasireducible]' attribute, '[reducible]', '[semireducible]' or '[irreducible]' was already provided", pos);
            m_is_quasireducible = true;
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
        } else if (p.curr_is_token(get_unfold_f_tk())) {
            p.next();
            m_unfold_f_hint = true;
        } else if (p.curr_is_token(get_constructor_tk())) {
            p.next();
            m_constructor_hint = true;
        } else if (p.curr_is_token(get_unfold_c_tk())) {
            p.next();
            unsigned r = p.parse_small_nat();
            if (r == 0)
                throw parser_error("invalid '[unfold-c]' attribute, value must be greater than 0", pos);
            m_unfold_c_hint = r - 1;
            p.check_token_next(get_rbracket_tk(), "invalid 'unfold-c', ']' expected");
        } else if (p.curr_is_token(get_symm_tk())) {
            p.next();
            m_symm = true;
        } else if (p.curr_is_token(get_refl_tk())) {
            p.next();
            m_refl = true;
        } else if (p.curr_is_token(get_trans_tk())) {
            p.next();
            m_trans = true;
        } else if (p.curr_is_token(get_subst_tk())) {
            p.next();
            m_subst = true;
        } else if (p.curr_is_token(get_rewrite_attr_tk())) {
            p.next();
            m_rewrite = true;
        } else if (p.curr_is_token(get_recursor_tk())) {
            p.next();
            if (!p.curr_is_token(get_rbracket_tk())) {
                unsigned r = p.parse_small_nat();
                if (r == 0)
                    throw parser_error("invalid '[recursor]' attribute, value must be greater than 0", pos);
                m_recursor_major_pos = r - 1;
            }
            p.check_token_next(get_rbracket_tk(), "invalid 'recursor', ']' expected");
            m_recursor = true;
        } else {
            break;
        }
    }
}

void decl_attributes::parse(name const & n, parser & p) {
    buffer<name> ns;
    ns.push_back(n);
    parse(ns, p);
}

void decl_attributes::parse(parser & p) {
    buffer<name> ns;
    parse(ns, p);
}

environment decl_attributes::apply(environment env, io_state const & ios, name const & d) const {
    if (m_is_instance) {
        if (m_priority) {
            #if defined(__GNUC__) && !defined(__CLANG__)
            #pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
            #endif
            env = add_instance(env, d, *m_priority, m_persistent);
        } else {
            env = add_instance(env, d, m_persistent);
        }
    }
    if (m_is_coercion)
        env = add_coercion(env, d, ios, m_persistent);
    auto decl = env.find(d);
    if (decl && decl->is_definition()) {
        if (m_is_reducible)
            env = set_reducible(env, d, reducible_status::Reducible, m_persistent);
        if (m_is_irreducible)
            env = set_reducible(env, d, reducible_status::Irreducible, m_persistent);
        if (m_is_semireducible)
            env = set_reducible(env, d, reducible_status::Semireducible, m_persistent);
        if (m_is_quasireducible)
            env = set_reducible(env, d, reducible_status::Quasireducible, m_persistent);
        if (m_unfold_c_hint)
            env = add_unfold_c_hint(env, d, *m_unfold_c_hint, m_persistent);
        if (m_unfold_f_hint)
            env = add_unfold_f_hint(env, d, m_persistent);
    }
    if (m_constructor_hint)
        env = add_constructor_hint(env, d, m_persistent);
    if (m_symm)
        env = add_symm(env, d, m_persistent);
    if (m_refl)
        env = add_refl(env, d, m_persistent);
    if (m_trans)
        env = add_trans(env, d, m_persistent);
    if (m_subst)
        env = add_subst(env, d, m_persistent);
    if (m_recursor)
        env = add_user_recursor(env, d, m_recursor_major_pos, m_persistent);
    if (m_is_class)
        env = add_class(env, d, m_persistent);
    if (m_rewrite)
        env = add_rewrite_rule(env, d, m_persistent);
    if (m_has_multiple_instances)
        env = mark_multiple_instances(env, d, m_persistent);
    return env;
}

void decl_attributes::write(serializer & s) const {
    s << m_def_only << m_is_abbrev << m_persistent << m_is_instance << m_is_coercion
      << m_is_reducible << m_is_irreducible << m_is_semireducible << m_is_quasireducible
      << m_is_class << m_is_parsing_only << m_has_multiple_instances << m_unfold_f_hint
      << m_constructor_hint << m_symm << m_trans << m_refl << m_subst << m_recursor
      << m_rewrite << m_recursor_major_pos << m_priority << m_unfold_c_hint;
}

void decl_attributes::read(deserializer & d) {
    d >> m_def_only >> m_is_abbrev >> m_persistent >> m_is_instance >> m_is_coercion
      >> m_is_reducible >> m_is_irreducible >> m_is_semireducible >> m_is_quasireducible
      >> m_is_class >> m_is_parsing_only >> m_has_multiple_instances >> m_unfold_f_hint
      >> m_constructor_hint >> m_symm >> m_trans >> m_refl >> m_subst >> m_recursor
      >> m_rewrite >> m_recursor_major_pos >> m_priority >> m_unfold_c_hint;
}
}
