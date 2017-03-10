/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include "kernel/inductive/inductive.h"
#include "kernel/abstract.h"
#include "util/sexpr/option_declarations.h"
#include "library/locals.h"
#include "library/trace.h"
#include "library/module.h"
#include "library/attribute_manager.h"
#include "library/inductive_compiler/compiler.h"
#include "library/inductive_compiler/basic.h"
#include "library/inductive_compiler/util.h"
#include "library/constructions/drec.h"
#include "library/constructions/rec_on.h"
#include "library/constructions/induction_on.h"
#include "library/constructions/cases_on.h"
#include "library/constructions/brec_on.h"
#include "library/constructions/no_confusion.h"
#include "library/constructions/has_sizeof.h"
#include "library/constructions/injective.h"

#ifndef LEAN_DEFAULT_XINDUCTIVE_REC_ON
#define LEAN_DEFAULT_XINDUCTIVE_REC_ON true
#endif

#ifndef LEAN_DEFAULT_XINDUCTIVE_CASES_ON
#define LEAN_DEFAULT_XINDUCTIVE_CASES_ON true
#endif

#ifndef LEAN_DEFAULT_XINDUCTIVE_NO_CONFUSION
#define LEAN_DEFAULT_XINDUCTIVE_NO_CONFUSION true
#endif

#ifndef LEAN_DEFAULT_XINDUCTIVE_BREC_ON
#define LEAN_DEFAULT_XINDUCTIVE_BREC_ON true
#endif

namespace lean {

static name * g_inductive_rec_on       = nullptr;
static name * g_inductive_cases_on     = nullptr;
static name * g_inductive_no_confusion = nullptr;
static name * g_inductive_brec_on      = nullptr;

static bool get_inductive_rec_on(options const & opts) {
    return opts.get_bool(*g_inductive_rec_on, LEAN_DEFAULT_XINDUCTIVE_REC_ON);
}

static bool get_inductive_cases_on(options const & opts) {
    return opts.get_bool(*g_inductive_cases_on, LEAN_DEFAULT_XINDUCTIVE_CASES_ON);
}

static bool get_inductive_brec_on(options const & opts) {
    return opts.get_bool(*g_inductive_brec_on, LEAN_DEFAULT_XINDUCTIVE_BREC_ON);
}

static bool get_inductive_no_confusion(options const & opts) {
    return opts.get_bool(*g_inductive_no_confusion, LEAN_DEFAULT_XINDUCTIVE_NO_CONFUSION);
}

using inductive::inductive_decl;
using inductive::intro_rule;
using inductive::mk_intro_rule;

class add_basic_inductive_decl_fn {
    environment                           m_env;
    options const &                       m_opts;
    name_map<implicit_infer_kind> const & m_implicit_infer_map;
    ginductive_decl const &               m_decl;
    bool                                  m_is_trusted;
    void mk_basic_aux_decls() {
        name ind_name = mlocal_name(m_decl.get_inds()[0]);

        bool has_eq   = has_eq_decls(m_env);
        bool has_heq  = has_heq_decls(m_env);
        bool has_unit = has_punit_decls(m_env);
        bool has_prod = has_pprod_decls(m_env);

        bool gen_rec_on       = get_inductive_rec_on(m_opts);
        bool gen_brec_on      = get_inductive_brec_on(m_opts);
        bool gen_cases_on     = get_inductive_cases_on(m_opts);
        bool gen_no_confusion = get_inductive_no_confusion(m_opts);

        if (is_inductive_predicate(m_env, ind_name))
            m_env = mk_drec(m_env, ind_name);

        if (gen_rec_on)
            m_env = mk_rec_on(m_env, ind_name);

        if (gen_rec_on)
            m_env = mk_induction_on(m_env, ind_name);

        if (has_unit) {
            if (gen_cases_on)
                m_env = mk_cases_on(m_env, ind_name);

            if (gen_cases_on && gen_no_confusion && has_eq && has_heq) {
                m_env = mk_no_confusion(m_env, ind_name);
                m_env = mk_injective_lemmas(m_env, ind_name);
            }

            if (gen_brec_on && has_prod) {
                m_env = mk_below(m_env, ind_name);
                m_env = mk_ibelow(m_env, ind_name);
            }
        }

        if (gen_brec_on && has_unit && has_prod) {
            m_env = mk_brec_on(m_env, ind_name);
            m_env = mk_binduction_on(m_env, ind_name);
        }

        m_env = mk_has_sizeof(m_env, ind_name);
    }

    void send_to_kernel() {
        buffer<name> const & lp_names = m_decl.get_lp_names();
        buffer<expr> const & params = m_decl.get_params();
        expr const & ind = m_decl.get_inds()[0];
        buffer<expr> const & intro_rules = m_decl.get_intro_rules()[0];

        expr new_ind_type = Pi(params, mlocal_type(ind));
        lean_assert(!has_local(new_ind_type));

        lean_trace(name({"inductive_compiler", "basic", "ind"}), tout() << mlocal_name(ind) << "\n";);

        buffer<intro_rule> new_intro_rules;
        for (expr const & ir : intro_rules) {
            implicit_infer_kind k = get_implicit_infer_kind(m_implicit_infer_map, mlocal_name(ir));
            expr new_ir_type = infer_implicit_params(Pi(params, mlocal_type(ir)), params.size(), k);
            lean_assert(!has_local(new_ir_type));
            new_intro_rules.push_back(mk_intro_rule(mlocal_name(ir), new_ir_type));
            lean_trace(name({"inductive_compiler", "basic", "irs"}), tout() << mlocal_name(ir) << " : " << new_ir_type << "\n";);
        }
        inductive_decl kdecl(mlocal_name(ind), to_list(lp_names), params.size(), new_ind_type, to_list(new_intro_rules));
        m_env = module::add_inductive(m_env, kdecl, m_is_trusted);
    }

public:
    add_basic_inductive_decl_fn(environment const & env, options const & opts, name_map<implicit_infer_kind> implicit_infer_map,
                                ginductive_decl const & decl, bool is_trusted):
        m_env(env), m_opts(opts), m_implicit_infer_map(implicit_infer_map), m_decl(decl), m_is_trusted(is_trusted) {}

    environment operator()() {
        send_to_kernel();
        mk_basic_aux_decls();
        return m_env;
    }
};

environment add_basic_inductive_decl(environment const & env, options const & opts, name_map<implicit_infer_kind> implicit_infer_map,
                                     ginductive_decl const & decl, bool is_trusted) {
    return add_basic_inductive_decl_fn(env, opts, implicit_infer_map, decl, is_trusted)();
}

void initialize_inductive_compiler_basic() {
    register_trace_class(name({"inductive_compiler", "basic"}));
    register_trace_class(name({"inductive_compiler", "basic", "ind"}));
    register_trace_class(name({"inductive_compiler", "basic", "irs"}));

    g_inductive_rec_on       = new name{"inductive", "rec_on"};
    g_inductive_cases_on     = new name{"inductive", "cases_on"};
    g_inductive_brec_on      = new name{"inductive", "brec_on"};
    g_inductive_no_confusion = new name{"inductive", "no_confusion"};

    register_bool_option(*g_inductive_rec_on, LEAN_DEFAULT_XINDUCTIVE_REC_ON,
                         "(inductive) automatically generate the auxiliary declarations C.rec_on and C.induction_on  for each inductive datatype C");

    register_bool_option(*g_inductive_brec_on, LEAN_DEFAULT_XINDUCTIVE_BREC_ON,
                         "(inductive) automatically generate the auxiliary declaration C.brec_on for each inductive datatype C");

    register_bool_option(*g_inductive_cases_on, LEAN_DEFAULT_XINDUCTIVE_CASES_ON,
                         "(inductive) automatically generate the auxiliary declaration C.cases_on for each inductive datatype C"
                         "(remark: if cases_on is disabled, then the auxiliary declaration C.no_confusion is also disabled");

    register_bool_option(*g_inductive_no_confusion, LEAN_DEFAULT_XINDUCTIVE_NO_CONFUSION,
                         "(inductive) automatically generate the auxiliary declaration C.no_confusion for each inductive datatype C");
}

void finalize_inductive_compiler_basic() {
    delete g_inductive_rec_on;
    delete g_inductive_cases_on;
    delete g_inductive_brec_on;
    delete g_inductive_no_confusion;
}

}
