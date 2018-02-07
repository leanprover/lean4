/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "library/sorry.h"
#include "library/noncomputable.h"
#include "util/fresh_name.h"
#include "util/sstream.h"
#include "kernel/instantiate.h"
#include "kernel/inductive/inductive.h"
#include "library/constants.h"
#include "library/trace.h"
#include "library/annotation.h"
#include "library/util.h"
#include "library/quote.h"
#include "library/replace_visitor.h"
#include "library/vm/vm.h"
#include "library/vm/optimize.h"
#include "library/compiler/simp_inductive.h"
#include "library/compiler/erase_irrelevant.h"
#include "library/compiler/nat_value.h"
#include "library/compiler/preprocess.h"
#include "library/compiler/comp_irrelevant.h"

namespace lean {
static name * g_vm_compiler_fresh = nullptr;

class vm_compiler_fn {
    environment        m_env;
    name_generator     m_ngen;
    buffer<vm_instr> & m_code;

    void emit(vm_instr const & i) {
        m_code.push_back(i);
    }

    unsigned next_pc() const {
        return m_code.size();
    }

    expr mk_local(name const & n) {
        return ::lean::mk_local(n, mk_neutral_expr());
    }

    void compile_args(unsigned nargs, expr const * args, unsigned bpz, name_map<unsigned> const & m) {
        for (unsigned i = 0; i < nargs; i++, bpz++) {
            compile(args[i], bpz, m);
        }
    }

    void compile_rev_args(unsigned nargs, expr const * args, unsigned bpz, name_map<unsigned> const & m) {
        unsigned i = nargs;
        while (i > 0) {
            --i;
            compile(args[i], bpz, m);
            bpz++;
        }
    }

    void compile_global(vm_decl const & decl, unsigned nargs, expr const * args, unsigned bpz, name_map<unsigned> const & m) {
        compile_rev_args(nargs, args, bpz, m);
        if (decl.get_arity() <= nargs) {
            if (decl.is_builtin())
                emit(mk_invoke_builtin_instr(decl.get_idx()));
            else if (decl.is_cfun())
                emit(mk_invoke_cfun_instr(decl.get_idx()));
            else
                emit(mk_invoke_global_instr(decl.get_idx()));
            emit_apply_instr(nargs - decl.get_arity());
        } else {
            lean_assert(decl.get_arity() > nargs);
            emit(mk_closure_instr(decl.get_idx(), nargs));
        }
    }

    [[ noreturn ]] void throw_unknown_constant(name const & n) {
        throw exception(sstream() << "code generation failed, VM does not have code for '" << n << "'");
    }

    void emit_apply_instr(unsigned n) {
        for (unsigned i = 0; i < n; i++)
            emit(mk_apply_instr());
    }

    void compile_constant(expr const & e) {
        name const & n = const_name(e);
        if (is_neutral_expr(e)) {
            emit(mk_sconstructor_instr(0));
        } else if (is_unreachable_expr(e)) {
            emit(mk_unreachable_instr());
        } else if (n == get_nat_zero_name()) {
            emit(mk_num_instr(mpz(0)));
        } else if (auto idx = is_internal_cnstr(e)) {
            emit(mk_sconstructor_instr(*idx));
        } else if (optional<vm_decl> decl = get_vm_decl(m_env, n)) {
            compile_global(*decl, 0, nullptr, 0, name_map<unsigned>());
        } else {
            throw_unknown_constant(n);
        }
    }

    void compile_local(expr const & e, name_map<unsigned> const & m) {
        unsigned idx = *m.find(mlocal_name(e));
        emit(mk_push_instr(idx));
    }

    void compile_cases_on(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        buffer<expr> args;
        expr fn = get_app_args(e, args);
        lean_assert(is_constant(fn));
        name const & fn_name = const_name(fn);
        unsigned num = get_vm_supported_cases_num_minors(m_env, fn);
        lean_assert(args.size() == num + 1);
        lean_assert(num >= 1);
        /** compile major premise */
        compile(args[0], bpz, m);
        unsigned cases_pos = next_pc();
        buffer<unsigned> cases_args;
        buffer<unsigned> goto_pcs;
        cases_args.resize(num, 0);
        if (fn_name == get_nat_cases_on_name()) {
            emit(mk_nat_cases_instr(0, 0));
        } else if (optional<unsigned> builtin_cases_idx = get_vm_builtin_cases_idx(m_env, fn_name)) {
            #if defined(__GNUC__) && !defined(__CLANG__)
            #pragma GCC diagnostic ignored "-Wmaybe-uninitialized"
            #endif
            emit(mk_builtin_cases_instr(*builtin_cases_idx, cases_args.size(), cases_args.data()));
        } else if (num == 1) {
            emit(mk_destruct_instr());
        } else if (num == 2) {
            emit(mk_cases2_instr(0, 0));
        } else {
            emit(mk_casesn_instr(cases_args.size(), cases_args.data()));
        }
        for (unsigned i = 1; i < args.size(); i++) {
            cases_args[i - 1] = next_pc();
            expr b = args[i];
            buffer<expr> locals;
            name_map<unsigned> new_m = m;
            unsigned new_bpz = bpz;
            while (is_lambda(b)) {
                name n = m_ngen.next();
                new_m.insert(n, new_bpz);
                locals.push_back(mk_local(n));
                new_bpz++;
                b = binding_body(b);
            }
            b = instantiate_rev(b, locals.size(), locals.data());
            compile(b, new_bpz, new_m);
            if (locals.size() > 0)
                emit(mk_drop_instr(locals.size()));
            // if it is not the last case, we need to use a goto
            if (i + 1 < args.size()) {
                goto_pcs.push_back(next_pc());
                emit(mk_goto_instr(0)); // fix later
            }
        }
        /* Fix cases instruction pc's */
        if (num >= 2 || get_vm_builtin_cases_idx(m_env, fn_name)) {
            for (unsigned i = 0; i < cases_args.size(); i++)
                m_code[cases_pos].set_pc(i, cases_args[i]);
        }
        unsigned end_pc = next_pc();
        /* Fix goto instruction pc's */
        for (unsigned i = 0; i < goto_pcs.size(); i++) {
            m_code[goto_pcs[i]].set_goto_pc(end_pc);
        }
    }

    void compile_cnstr(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        lean_assert(is_internal_cnstr(fn));
        unsigned cidx = *is_internal_cnstr(fn);
        compile_args(args.size(), args.data(), bpz, m);
        emit(mk_constructor_instr(cidx, get_app_num_args(e)));
    }

    void compile_proj(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        buffer<expr> args;
        expr const & fn = get_app_args(e, args);
        lean_assert(is_internal_proj(fn));
        unsigned idx = *is_internal_proj(fn);
        lean_assert(args.size() >= 1);
        compile_rev_args(args.size() - 1, args.data() + 1, bpz, m);
        bpz += args.size() - 1;
        compile(args[0], bpz, m);
        emit(mk_proj_instr(idx));
        emit_apply_instr(args.size() - 1);
    }

    void compile_external(name const & n, buffer<expr> & args, unsigned bpz, name_map<unsigned> const & m) {
        // Not sure if this is the best approach, trying to lazy load the required
        // dynamic libraries.
        std::cout << "external compile" << n << std::endl;
        optional<vm_decl> decl = get_vm_decl(m_env, n);
        lean_assert(decl);
        compile_global(*decl, args.size(), args.data(), bpz, m);
    }

    void compile_fn_call(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        buffer<expr> args;
        expr fn = get_app_args(e, args);
        if (!is_constant(fn)) {
            compile_rev_args(args.size(), args.data(), bpz, m);
            compile(fn, bpz + args.size(), m);
            emit_apply_instr(args.size());
            return;
        } else if (is_constant(fn)) {
            if (is_neutral_expr(fn)) {
                emit(mk_sconstructor_instr(0));
            } else if (optional<vm_decl> decl = get_vm_decl(m_env, const_name(fn))) {
                compile_global(*decl, args.size(), args.data(), bpz, m);
            } else {
                throw_unknown_constant(const_name(fn));
            }
        } else {
            lean_unreachable();
        }
    }

    void compile_app(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        expr const & fn = get_app_fn(e);
        if (is_vm_supported_cases(m_env, fn)) {
            compile_cases_on(e, bpz, m);
        } else if (is_internal_cnstr(fn)) {
            compile_cnstr(e, bpz, m);
        } else if (is_internal_proj(fn)) {
            compile_proj(e, bpz, m);
        } else {
            compile_fn_call(e, bpz, m);
        }
    }

    class elim_comp_irrelevant_marks_fn : public replace_visitor {
        virtual expr visit_macro(expr const & e) override {
            if (is_marked_as_comp_irrelevant(e))
                return visit(get_annotation_arg(e));
            else
                return replace_visitor::visit_macro(e);
        }
    };

    optional<expr> to_type_info(expr const & t) {
        if (!is_neutral_expr(t) && closed(t) && !has_param_univ(t)) {
            return some_expr(elim_comp_irrelevant_marks_fn()(t));
        } else {
            return none_expr();
        }
    }

    void compile_let(expr e, unsigned bpz, name_map<unsigned> const & m) {
        unsigned counter = 0;
        buffer<expr> locals;
        name_map<unsigned> new_m = m;
        while (is_let(e)) {
            counter++;
            compile(instantiate_rev(let_value(e), locals.size(), locals.data()), bpz, new_m);
            emit(mk_local_info_instr(bpz, let_name(e), to_type_info(let_type(e))));
            name n = m_ngen.next();
            new_m.insert(n, bpz);
            locals.push_back(mk_local(n));
            bpz++;
            e = let_body(e);
        }
        lean_assert(counter > 0);
        compile(instantiate_rev(e, locals.size(), locals.data()), bpz, new_m);
        emit(mk_drop_instr(counter));
    }

    void compile_macro(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        if (is_nat_value(e)) {
            emit(mk_num_instr(get_nat_value_value(e)));
        } else if (is_annotation(e)) {
            compile(get_annotation_arg(e), bpz, m);
        } else if (is_expr_quote(e)) {
            emit(mk_expr_instr(get_expr_quote_value(e)));
        } else if (is_pexpr_quote(e)) {
            emit(mk_expr_instr(get_pexpr_quote_value(e)));
        } else if (is_sorry(e)) {
            compile_global(*get_vm_decl(m_env, "sorry"), 0, nullptr, bpz, m);
        } else {
            throw exception(sstream() << "code generation failed, unexpected kind of macro has been found: '"
                            << macro_def(e).get_name() << "'");
        }
    }

    void compile(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        switch (e.kind()) {
        case expr_kind::Var:      lean_unreachable();
        case expr_kind::Sort:     lean_unreachable();
        case expr_kind::Meta:     lean_unreachable();
        case expr_kind::Pi:       lean_unreachable();
        case expr_kind::Lambda:   lean_unreachable();
        case expr_kind::Macro:    compile_macro(e, bpz, m);  break;
        case expr_kind::Constant: compile_constant(e);       break;
        case expr_kind::Local:    compile_local(e, m);       break;
        case expr_kind::App:      compile_app(e, bpz, m);    break;
        case expr_kind::Let:      compile_let(e, bpz, m);    break;
        }
    }

    unsigned get_arity(expr e) {
        unsigned r = 0;
        while (is_lambda(e)) {
            r++;
            e = binding_body(e);
        }
        return r;
    }

public:
    vm_compiler_fn(environment const & env, buffer<vm_instr> & code):
        m_env(env), m_ngen(*g_vm_compiler_fresh), m_code(code) {}

    pair<unsigned, list<vm_local_info>> operator()(expr e) {
        buffer<expr> locals;
        unsigned bpz   = 0;
        unsigned arity = get_arity(e);
        unsigned i     = arity;
        name_map<unsigned> m;
        list<vm_local_info> args_info;
        while (is_lambda(e)) {
            name n = m_ngen.next();
            i--;
            m.insert(n, i);
            locals.push_back(mk_local(n));
            bpz++;
            args_info = cons(vm_local_info(binding_name(e), to_type_info(binding_domain(e))), args_info);
            e = binding_body(e);
        }
        e = instantiate_rev(e, locals.size(), locals.data());
        compile(e, bpz, m);
        emit(mk_ret_instr());
        return mk_pair(arity, args_info);
    }
};

static environment vm_compile(environment const & env, buffer<procedure> const & procs, bool optimize_bytecode) {
    environment new_env = env;
    for (auto const & p : procs) {
        new_env = reserve_vm_index(new_env, p.m_name, p.m_code);
    }

    for (auto const & p : procs) {
        buffer<vm_instr> code;
        vm_compiler_fn gen(new_env, code);
        list<vm_local_info> args_info;
        unsigned arity;
        std::tie(arity, args_info) = gen(p.m_code);
        lean_trace(name({"compiler", "code_gen"}), tout() << " " << p.m_name << " " << arity << "\n";
                   display_vm_code(tout().get_stream(), code.size(), code.data()););
        if (optimize_bytecode) {
            optimize(new_env, code);
            lean_trace(name({"compiler", "optimize_bytecode"}), tout() << " " << p.m_name << " " << arity << "\n";
                       display_vm_code(tout().get_stream(), code.size(), code.data()););
        }
        new_env = update_vm_code(new_env, p.m_name, code.size(), code.data(), args_info, p.m_pos);
    }
    return new_env;
}

environment vm_compile(environment const & env, buffer<declaration> const & ds, bool optimize_bytecode) {
    buffer<procedure> procs;
    preprocess(env, ds, procs);
    return vm_compile(env, procs, optimize_bytecode);
}

static optional<environment> try_reuse_aux_meta_code(environment const & env, name const & d_name) {
    name aux_name = mk_aux_meta_rec_name(d_name);
    optional<vm_decl> v_decl = get_vm_decl(env, aux_name);
    if (!v_decl || !v_decl->is_bytecode())
        return optional<environment>();
    /* If we already compiled d_name._meta_aux (which is a meta definition),
       we reuse the generated code.
       The goal is to have a predictable runtime cost model for Lean and avoid
       the overhead generated by the equation compiler when using well founded recursion
       and structural recursion.
    */
    return optional<environment>(add_vm_code(env, d_name, v_decl->get_arity(),
                                             v_decl->get_code_size(), v_decl->get_code(),
                                             v_decl->get_args_info(), v_decl->get_pos_info()));
}

environment vm_compile(environment const & env, declaration const & d, bool optimize_bytecode) {
    if (!d.is_definition() || d.is_theorem() || is_noncomputable(env, d.get_name()) || is_vm_builtin_function(d.get_name()))
        return env;

    if (auto new_env = try_reuse_aux_meta_code(env, d.get_name()))
        return *new_env;

    buffer<declaration> ds;
    ds.push_back(d);
    return vm_compile(env, ds, optimize_bytecode);
}

void initialize_vm_compiler() {
    g_vm_compiler_fresh = new name ("_vmc_fresh");
    register_name_generator_prefix(*g_vm_compiler_fresh);
    register_trace_class({"compiler", "optimize_bytecode"});
    register_trace_class({"compiler", "code_gen"});
}

void finalize_vm_compiler() {
    delete g_vm_compiler_fresh;
}
}
