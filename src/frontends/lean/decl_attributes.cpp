/*
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/replace_visitor.h"
#include "library/normalize.h"
#include "library/reducible.h"
#include "library/class.h"
#include "library/relation_manager.h"
#include "library/user_recursors.h"
#include "library/coercion.h"
#include "library/simplifier/simp_rule_set.h"
#include "frontends/lean/decl_attributes.h"
#include "frontends/lean/parser.h"
#include "frontends/lean/tokens.h"
#include "frontends/lean/util.h"

namespace lean {
decl_attributes::decl_attributes(bool is_abbrev, bool persistent):
    m_priority() {
    m_is_abbrev              = is_abbrev;
    m_persistent             = persistent;
    m_is_instance            = false;
    m_is_trans_instance      = false;
    m_is_coercion            = false;
    m_is_reducible           = is_abbrev;
    m_is_irreducible         = false;
    m_is_semireducible       = false;
    m_is_quasireducible      = false;
    m_is_class               = false;
    m_is_parsing_only        = false;
    m_has_multiple_instances = false;
    m_unfold_full_hint       = false;
    m_constructor_hint       = false;
    m_symm                   = false;
    m_trans                  = false;
    m_refl                   = false;
    m_subst                  = false;
    m_recursor               = false;
    m_simp                   = false;
    m_congr                  = false;
}

void decl_attributes::parse(buffer<name> const & ns, parser & p) {
    while (true) {
        auto pos = p.pos();
        if (p.curr_is_token(get_instance_tk())) {
            m_is_instance = true;
            if (m_is_trans_instance)
                throw parser_error("invalid '[instance]' attribute, '[trans-instance]' was already provided", pos);
            p.next();
        } else if (p.curr_is_token(get_trans_inst_tk())) {
            m_is_trans_instance = true;
            if (m_is_instance)
                throw parser_error("invalid '[trans-instance]' attribute, '[instance]' was already provided", pos);
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
            m_is_class = true;
            p.next();
        } else if (p.curr_is_token(get_multiple_instances_tk())) {
            m_has_multiple_instances = true;
            p.next();
        } else if (auto it = parse_priority(p)) {
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
        } else if (p.curr_is_token(get_unfold_full_tk())) {
            p.next();
            m_unfold_full_hint = true;
        } else if (p.curr_is_token(get_constructor_tk())) {
            p.next();
            m_constructor_hint = true;
        } else if (p.curr_is_token(get_unfold_tk())) {
            p.next();
            buffer<unsigned> idxs;
            while (true) {
                unsigned r = p.parse_small_nat();
                if (r == 0)
                    throw parser_error("invalid '[unfold]' attribute, value must be greater than 0", pos);
                idxs.push_back(r-1);
                if (p.curr_is_token(get_rbracket_tk()))
                    break;
            }
            p.next();
            m_unfold_hint = to_list(idxs);
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
        } else if (p.curr_is_token(get_simp_attr_tk())) {
            p.next();
            m_simp = true;
        } else if (p.curr_is_token(get_congr_attr_tk())) {
            p.next();
            m_congr = true;
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
    if (m_is_trans_instance) {
        if (m_priority) {
            #if defined(__GNUC__) && !defined(__CLANG__)
            #pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
            #endif
            env = add_trans_instance(env, d, *m_priority, m_persistent);
        } else {
            env = add_trans_instance(env, d, m_persistent);
        }
    }
    if (m_is_coercion)
        env = add_coercion(env, ios, d, m_persistent);
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
        if (m_unfold_hint)
            env = add_unfold_hint(env, d, m_unfold_hint, m_persistent);
        if (m_unfold_full_hint)
            env = add_unfold_full_hint(env, d, m_persistent);
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
    if (m_simp)
        env = add_simp_rule(env, d, m_persistent);
    if (m_congr)
        env = add_congr_rule(env, d, m_persistent);
    if (m_has_multiple_instances)
        env = mark_multiple_instances(env, d, m_persistent);
    return env;
}

void decl_attributes::write(serializer & s) const {
    s << m_is_abbrev << m_persistent << m_is_instance << m_is_trans_instance << m_is_coercion
      << m_is_reducible << m_is_irreducible << m_is_semireducible << m_is_quasireducible
      << m_is_class << m_is_parsing_only << m_has_multiple_instances << m_unfold_full_hint
      << m_constructor_hint << m_symm << m_trans << m_refl << m_subst << m_recursor
      << m_simp << m_congr << m_recursor_major_pos << m_priority;
    write_list(s, m_unfold_hint);
}

void decl_attributes::read(deserializer & d) {
    d >> m_is_abbrev >> m_persistent >> m_is_instance >> m_is_trans_instance >> m_is_coercion
      >> m_is_reducible >> m_is_irreducible >> m_is_semireducible >> m_is_quasireducible
      >> m_is_class >> m_is_parsing_only >> m_has_multiple_instances >> m_unfold_full_hint
      >> m_constructor_hint >> m_symm >> m_trans >> m_refl >> m_subst >> m_recursor
      >> m_simp >> m_congr >> m_recursor_major_pos >> m_priority;
    m_unfold_hint = read_list<unsigned>(d);
}
}
