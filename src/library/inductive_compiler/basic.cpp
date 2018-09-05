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
#include "library/constructions/rec_on.h"
#include "library/constructions/cases_on.h"
#include "library/constructions/brec_on.h"
#include "library/constructions/no_confusion.h"

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

class add_basic_inductive_decl_fn {
    environment                           m_env;
    options const &                       m_opts;
    name_map<implicit_infer_kind> const & m_implicit_infer_map;
    ginductive_decl const &               m_decl;
    bool                                  m_is_meta;
    void mk_basic_aux_decls() {
        name ind_name = local_name(m_decl.get_inds()[0]);

        bool has_eq   = has_eq_decls(m_env);
        bool has_heq  = has_heq_decls(m_env);
        bool has_unit = has_punit_decls(m_env);
        bool has_prod = has_pprod_decls(m_env);

        bool gen_rec_on       = get_inductive_rec_on(m_opts);
        bool gen_brec_on      = get_inductive_brec_on(m_opts);
        bool gen_cases_on     = get_inductive_cases_on(m_opts);
        bool gen_no_confusion = get_inductive_no_confusion(m_opts);

        // if (is_inductive_predicate(m_env, ind_name))
            // m_env = mk_drec(m_env, ind_name);

        lean_trace(name({"inductive_compiler"}), tout() << ">> generate rec_on\n";);
        if (gen_rec_on)
            m_env = mk_old_rec_on(m_env, ind_name);

        if (has_unit) {
            lean_trace(name({"inductive_compiler"}), tout() << ">> generate cases_on\n";);
            if (gen_cases_on)
                m_env = mk_old_cases_on(m_env, ind_name);

            if (gen_cases_on && gen_no_confusion && has_eq && has_heq) {
                lean_trace(name({"inductive_compiler"}), tout() << ">> generate no_confusion\n";);
                m_env = old_mk_no_confusion(m_env, ind_name);
            }

            if (gen_brec_on && has_prod) {
                lean_trace(name({"inductive_compiler"}), tout() << ">> generate below\n";);
                m_env = old_mk_below(m_env, ind_name);
                lean_trace(name({"inductive_compiler"}), tout() << ">> generate ibelow\n";);
                m_env = old_mk_ibelow(m_env, ind_name);
            }
        }

        if (gen_brec_on && has_unit && has_prod) {
            lean_trace(name({"inductive_compiler"}), tout() << ">> generate brec_on\n";);
            m_env = old_mk_brec_on(m_env, ind_name);
            lean_trace(name({"inductive_compiler"}), tout() << ">> generate binduction_on\n";);
            m_env = old_mk_binduction_on(m_env, ind_name);
        }
    }

    void send_to_kernel() {
        buffer<name> const & lp_names = m_decl.get_lp_names();
        buffer<expr> const & params = m_decl.get_params();
        expr const & ind = m_decl.get_inds()[0];
        buffer<expr> const & intro_rules = m_decl.get_intro_rules()[0];

        expr new_ind_type = Pi(params, local_type(ind));
        lean_assert(!has_local(new_ind_type));

        lean_trace(name({"inductive_compiler", "basic", "ind"}), tout() << local_name(ind) << "\n";);

        buffer<inductive::intro_rule> new_intro_rules;
        for (expr const & ir : intro_rules) {
            implicit_infer_kind k = get_implicit_infer_kind(m_implicit_infer_map, local_name(ir));
            expr new_ir_type = infer_implicit_params(Pi(params, local_type(ir)), params.size(), k);
            lean_assert(!has_local(new_ir_type));
            new_intro_rules.push_back(inductive::mk_intro_rule(local_name(ir), new_ir_type));
            lean_trace(name({"inductive_compiler", "basic", "irs"}), tout() << local_name(ir) << " : " << new_ir_type << "\n";);
        }
        inductive::inductive_decl kdecl(local_name(ind), names(lp_names), params.size(), new_ind_type, to_list(new_intro_rules));
        m_env = module::add_inductive(m_env, kdecl, m_is_meta);
    }

public:
    add_basic_inductive_decl_fn(environment const & env, options const & opts, name_map<implicit_infer_kind> implicit_infer_map,
                                ginductive_decl const & decl, bool is_meta):
        m_env(env), m_opts(opts), m_implicit_infer_map(implicit_infer_map), m_decl(decl), m_is_meta(is_meta) {}

    environment operator()() {
        send_to_kernel();
        mk_basic_aux_decls();
        return m_env;
    }
};

environment add_basic_inductive_decl(environment const & env, options const & opts, name_map<implicit_infer_kind> implicit_infer_map,
                                     ginductive_decl const & decl, bool is_meta) {
    return add_basic_inductive_decl_fn(env, opts, implicit_infer_map, decl, is_meta)();
}

void initialize_inductive_compiler_basic() {
    register_trace_class(name({"inductive_compiler"}));
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
