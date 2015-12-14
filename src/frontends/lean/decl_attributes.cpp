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
#include "library/light_lt_manager.h"
#include "library/blast/simplifier/simp_rule_set.h"
#include "library/blast/backward/backward_rule_set.h"
#include "library/blast/forward/pattern.h"
#include "library/blast/forward/forward_lemma_set.h"
#include "library/blast/grinder/intro_elim_lemmas.h"
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
    m_forward                = false;
    m_intro                  = false;
    m_intro_bang             = false;
    m_elim                   = false;
    m_no_pattern             = false;
}

void decl_attributes::parse(parser & p) {
    while (true) {
        auto pos = p.pos();
        if (p.curr_is_token(get_instance_tk())) {
            m_is_instance = true;
            if (m_is_trans_instance)
                throw parser_error("invalid '[instance]' attribute, '[trans_instance]' was already provided", pos);
            p.next();
        } else if (p.curr_is_token(get_trans_inst_tk())) {
            m_is_trans_instance = true;
            if (m_is_instance)
                throw parser_error("invalid '[trans_instance]' attribute, '[instance]' was already provided", pos);
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
            if (!m_is_instance && !m_simp && !m_congr && !m_forward && !m_elim && !m_intro && !m_intro_bang) {
                throw parser_error("invalid '[priority]' attribute, declaration must be marked as an '[instance]', '[simp]', '[congr]', "
                                   "'[forward]', '[intro!]', '[intro]' or '[elim]'", pos);
            }
        } else if (p.curr_is_token(get_parsing_only_tk())) {
            if (!m_is_abbrev)
                throw parser_error("invalid '[parsing_only]' attribute, only abbreviations can be "
                                   "marked as '[parsing_only]'", pos);
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
        } else if (p.curr_is_token(get_light_attr_tk())) {
            p.next();
            m_light_arg = p.parse_small_nat();
            p.check_token_next(get_rbracket_tk(), "light attribute has form '[light <i>]'");
        } else if (p.curr_is_token(get_forward_attr_tk())) {
            p.next();
            m_forward = true;
        } else if (p.curr_is_token(get_elim_attr_tk())) {
            p.next();
            m_elim = true;
        } else if (p.curr_is_token(get_intro_attr_tk())) {
            p.next();
            m_intro = true;
        } else if (p.curr_is_token(get_intro_bang_attr_tk())) {
            p.next();
            m_intro_bang = true;
        } else if (p.curr_is_token(get_no_pattern_attr_tk())) {
            p.next();
            m_no_pattern = true;
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

environment decl_attributes::apply(environment env, io_state const & ios, name const & d, name const & ns) const {
    bool forward = m_forward;
    if (has_pattern_hints(env.get(d).get_type())) {
        // turn on [forward] if patterns hints have been used in the type.
        forward = true;
    }

    if (m_is_instance) {
        if (m_priority) {
            #if defined(__GNUC__) && !defined(__CLANG__)
            #pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
            #endif
            env = add_instance(env, d, *m_priority, ns, m_persistent);
        } else {
            env = add_instance(env, d, ns, m_persistent);
        }
    }
    if (m_is_trans_instance) {
        if (m_priority) {
            #if defined(__GNUC__) && !defined(__CLANG__)
            #pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
            #endif
            env = add_trans_instance(env, d, *m_priority, ns, m_persistent);
        } else {
            env = add_trans_instance(env, d, ns, m_persistent);
        }
    }
    if (m_is_coercion)
        env = add_coercion(env, ios, d, ns, m_persistent);
    auto decl = env.find(d);
    if (decl && decl->is_definition()) {
        if (m_is_reducible)
            env = set_reducible(env, d, reducible_status::Reducible, ns, m_persistent);
        if (m_is_irreducible)
            env = set_reducible(env, d, reducible_status::Irreducible, ns, m_persistent);
        if (m_is_semireducible)
            env = set_reducible(env, d, reducible_status::Semireducible, ns, m_persistent);
        if (m_is_quasireducible)
            env = set_reducible(env, d, reducible_status::Quasireducible, ns, m_persistent);
        if (m_unfold_hint)
            env = add_unfold_hint(env, d, m_unfold_hint, ns, m_persistent);
        if (m_unfold_full_hint)
            env = add_unfold_full_hint(env, d, ns, m_persistent);
    }
    if (m_constructor_hint)
        env = add_constructor_hint(env, d, ns, m_persistent);
    if (m_symm)
        env = add_symm(env, d, ns, m_persistent);
    if (m_refl)
        env = add_refl(env, d, ns, m_persistent);
    if (m_trans)
        env = add_trans(env, d, ns, m_persistent);
    if (m_subst)
        env = add_subst(env, d, ns, m_persistent);
    if (m_recursor)
        env = add_user_recursor(env, d, m_recursor_major_pos, ns, m_persistent);
    if (m_is_class)
        env = add_class(env, d, ns, m_persistent);
    if (m_simp) {
        if (m_priority)
            env = add_simp_rule(env, d, *m_priority, ns, m_persistent);
        else
            env = add_simp_rule(env, d, LEAN_SIMP_DEFAULT_PRIORITY, ns, m_persistent);
    }
    if (m_congr) {
        if (m_priority)
            env = add_congr_rule(env, d, *m_priority, ns, m_persistent);
        else
            env = add_congr_rule(env, d, LEAN_SIMP_DEFAULT_PRIORITY, ns, m_persistent);
    }
    if (m_light_arg) {
        env = add_light_rule(env, d, *m_light_arg, ns, m_persistent);
    }
    if (forward) {
        mk_multipatterns(env, ios, d); // try to create patterns
        if (m_priority)
            env = add_forward_lemma(env, d, *m_priority, ns, m_persistent);
        else
            env = add_forward_lemma(env, d, LEAN_FORWARD_DEFAULT_PRIORITY, ns, m_persistent);
    }
    if (m_intro) {
        if (m_priority)
            env = add_backward_rule(env, d, *m_priority, ns, m_persistent);
        else
            env = add_backward_rule(env, d, LEAN_BACKWARD_DEFAULT_PRIORITY, ns, m_persistent);
    }
    if (m_intro_bang) {
        if (m_priority)
            env = add_intro_lemma(env, ios, d, *m_priority, ns, m_persistent);
        else
            env = add_intro_lemma(env, ios, d, LEAN_INTRO_DEFAULT_PRIORITY, ns, m_persistent);
    }
    if (m_elim) {
        if (m_priority)
            env = add_elim_lemma(env, ios, d, *m_priority, ns, m_persistent);
        else
            env = add_elim_lemma(env, ios, d, LEAN_ELIM_DEFAULT_PRIORITY, ns, m_persistent);
    }
    if (m_no_pattern) {
        env = add_no_pattern(env, d, ns, m_persistent);
    }
    if (m_has_multiple_instances)
        env = mark_multiple_instances(env, d, ns, m_persistent);
    return env;
}

void decl_attributes::write(serializer & s) const {
    s << m_is_abbrev << m_persistent << m_is_instance << m_is_trans_instance << m_is_coercion
      << m_is_reducible << m_is_irreducible << m_is_semireducible << m_is_quasireducible
      << m_is_class << m_is_parsing_only << m_has_multiple_instances << m_unfold_full_hint
      << m_constructor_hint << m_symm << m_trans << m_refl << m_subst << m_recursor
      << m_simp << m_congr << m_recursor_major_pos << m_priority
      << m_forward << m_elim << m_intro << m_intro_bang << m_no_pattern;
    write_list(s, m_unfold_hint);
}

void decl_attributes::read(deserializer & d) {
    d >> m_is_abbrev >> m_persistent >> m_is_instance >> m_is_trans_instance >> m_is_coercion
      >> m_is_reducible >> m_is_irreducible >> m_is_semireducible >> m_is_quasireducible
      >> m_is_class >> m_is_parsing_only >> m_has_multiple_instances >> m_unfold_full_hint
      >> m_constructor_hint >> m_symm >> m_trans >> m_refl >> m_subst >> m_recursor
      >> m_simp >> m_congr >> m_recursor_major_pos >> m_priority
      >> m_forward >> m_elim >> m_intro >> m_intro_bang >> m_no_pattern;
    m_unfold_hint = read_list<unsigned>(d);
}

bool operator==(decl_attributes const & d1, decl_attributes const & d2) {
    return
        d1.m_is_abbrev == d2.m_is_abbrev &&
        d1.m_persistent == d2.m_persistent &&
        d1.m_is_instance == d2.m_is_instance &&
        d1.m_is_trans_instance == d2.m_is_trans_instance &&
        d1.m_is_coercion == d2.m_is_coercion &&
        d1.m_is_reducible == d2.m_is_reducible &&
        d1.m_is_irreducible == d2.m_is_irreducible &&
        d1.m_is_semireducible == d2.m_is_semireducible &&
        d1.m_is_quasireducible == d2.m_is_quasireducible &&
        d1.m_is_class == d2.m_is_class &&
        d1.m_is_parsing_only == d2.m_is_parsing_only &&
        d1.m_has_multiple_instances == d2.m_has_multiple_instances &&
        d1.m_unfold_full_hint == d2.m_unfold_full_hint &&
        d1.m_constructor_hint == d2.m_constructor_hint &&
        d1.m_symm == d2.m_symm &&
        d1.m_trans == d2.m_trans &&
        d1.m_refl == d2.m_refl &&
        d1.m_subst == d2.m_subst &&
        d1.m_recursor == d2.m_recursor &&
        d1.m_simp == d1.m_simp &&
        d1.m_congr == d2.m_congr &&
        d1.m_recursor_major_pos == d2.m_recursor_major_pos &&
        d1.m_priority == d2.m_priority &&
        d1.m_forward == d2.m_forward &&
        d1.m_elim == d2.m_elim &&
        d1.m_intro == d2.m_intro &&
        d1.m_intro_bang == d2.m_intro_bang &&
        d1.m_no_pattern == d2.m_no_pattern &&
        d1.m_unfold_hint == d2.m_unfold_hint;
}
}
