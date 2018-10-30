/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include "runtime/sstream.h"
#include "util/fresh_name.h"
#include "kernel/instantiate.h"
#include "library/sorry.h"
#include "library/constants.h"
#include "library/trace.h"
#include "library/annotation.h"
#include "library/util.h"
#include "library/replace_visitor.h"
#include "library/vm/vm.h"
#include "library/vm/optimize.h"
#include "library/compiler/llnf.h"
#include "library/compiler/util.h"

namespace lean {
class emit_bytecode_fn {
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
        return ::lean::mk_local(n, mk_enf_neutral());
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

    [[ noreturn ]] void throw_no_unboxed_support() {
        throw exception("code generation failed, old VM has no support for unboxed data");
    }

    void compile_constant(expr const & e) {
        name const & n = const_name(e);
        unsigned cidx; unsigned ssz;
        if (is_enf_neutral(e)) {
            emit(mk_sconstructor_instr(0));
        } else if (is_enf_unreachable(e)) {
            emit(mk_unreachable_instr());
        } else if (n == get_nat_zero_name()) {
            emit(mk_num_instr(mpz(0)));
        } else if (is_llnf_cnstr(e, cidx, ssz)) {
            if (ssz != 0) throw_no_unboxed_support();
            emit(mk_sconstructor_instr(cidx));
        } else if (optional<vm_decl> decl = get_vm_decl(m_env, n)) {
            compile_global(*decl, 0, nullptr, 0, name_map<unsigned>());
        } else {
            throw_unknown_constant(n);
        }
    }

    void compile_local(expr const & e, name_map<unsigned> const & m) {
        unsigned idx = *m.find(local_name(e));
        emit(mk_push_instr(idx));
    }

    void compile_cases_on(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        buffer<expr> args;
        expr fn = get_app_args(e, args);
        lean_assert(args.size() >= 3); /* major + at least 2 minor premises */
        /** compile major premise */
        compile(args[0], bpz, m);
        unsigned num       = args.size() - 1;
        unsigned cases_pos = next_pc();
        buffer<unsigned> cases_args;
        buffer<unsigned> goto_pcs;
        cases_args.resize(num, 0);
        if (num == 2) {
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
        if (num >= 2) {
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
        lean_assert(is_llnf_cnstr(fn));
        unsigned cidx, ssz;
        is_llnf_cnstr(fn, cidx, ssz);
        if (ssz != 0) throw_no_unboxed_support();
        compile_args(args.size(), args.data(), bpz, m);
        emit(mk_constructor_instr(cidx, get_app_num_args(e)));
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
            if (is_enf_neutral(fn)) {
                emit(mk_sconstructor_instr(0));
            } else if (is_enf_unreachable(fn)) {
                emit(mk_unreachable_instr());
            } else if (optional<vm_decl> decl = get_vm_decl(m_env, const_name(fn))) {
                compile_global(*decl, args.size(), args.data(), bpz, m);
            } else {
                throw_unknown_constant(const_name(fn));
            }
        } else {
            lean_unreachable();
        }
    }

    void compile_proj(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        expr const & p = app_fn(e);
        lean_assert(is_llnf_proj(p));
        expr const & a = app_arg(e);
        compile(a, bpz, m);
        unsigned idx;
        is_llnf_proj(p, idx);
        emit(mk_proj_instr(idx));
    }

    void compile_updt(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        expr fn = app_fn(app_fn(e));
        expr s  = app_arg(app_fn(e));
        expr v  = app_arg(e);
        unsigned idx;
        is_llnf_updt(fn, idx);
        compile(s, bpz, m);
        bpz++;
        compile(v, bpz, m);
        emit(mk_updt_instr(idx));
    }

    void compile_updt_cidx(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        expr fn = app_fn(e);
        expr s  = app_arg(e);
        unsigned idx;
        is_llnf_updt_cidx(fn, idx);
        compile(s, bpz, m);
        emit(mk_updt_cidx_instr(idx));
    }

    void compile_reset(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        expr fn = app_fn(e);
        expr s  = app_arg(e);
        unsigned idx;
        is_llnf_reset(fn, idx);
        compile(s, bpz, m);
        emit(mk_reset_instr(idx));
    }

    void compile_app(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        expr const & fn = get_app_fn(e);
        if (is_cases_on_app(m_env, fn)) {
            compile_cases_on(e, bpz, m);
        } else if (is_llnf_cnstr(fn)) {
            compile_cnstr(e, bpz, m);
        } else if (is_llnf_proj(fn)) {
            compile_proj(e, bpz, m);
        } else if (is_llnf_updt(fn)) {
            compile_updt(e, bpz, m);
        } else if (is_llnf_updt_cidx(fn)) {
            compile_updt_cidx(e, bpz, m);
        } else if (is_llnf_reset(fn)) {
            compile_reset(e, bpz, m);
        } else if (is_sorry(e)) {
            compile_global(*get_vm_decl(m_env, "sorry"), 0, nullptr, bpz, m);
        } else {
            compile_fn_call(e, bpz, m);
        }
    }

    class elim_comp_irrelevant_marks_fn : public replace_visitor {
        virtual expr visit_mdata(expr const & e) override {
            return replace_visitor::visit_mdata(e);
        }
    };

    optional<expr> to_type_info(expr const & t) {
        if (!is_enf_neutral(t) && !has_loose_bvars(t) && !has_param_univ(t)) {
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

    void compile_lit(expr const & e) {
        switch (lit_value(e).kind()) {
        case literal_kind::Nat:
            emit(mk_num_instr(lit_value(e).get_nat().to_mpz()));
            break;
        case literal_kind::String:
            emit(mk_string_instr(lit_value(e).get_string().to_std_string()));
            break;
        }
    }

    void compile(expr const & e, unsigned bpz, name_map<unsigned> const & m) {
        switch (e.kind()) {
        case expr_kind::BVar:     lean_unreachable();
        case expr_kind::Sort:     lean_unreachable();
        case expr_kind::MVar:     lean_unreachable();
        case expr_kind::Pi:       lean_unreachable();
        case expr_kind::Lambda:   lean_unreachable();
        case expr_kind::Proj:     lean_unreachable();
        case expr_kind::MData:    compile(mdata_expr(e), bpz, m); break;
        case expr_kind::Const:    compile_constant(e);       break;
        case expr_kind::FVar:     compile_local(e, m);       break;
        case expr_kind::App:      compile_app(e, bpz, m);    break;
        case expr_kind::Let:      compile_let(e, bpz, m);    break;
        case expr_kind::Lit:      compile_lit(e);            break;
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
    emit_bytecode_fn(environment const & env, buffer<vm_instr> & code):
        m_env(env), m_code(code) {}

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

environment emit_bytecode(environment const & env, comp_decls const & ds) {
    environment new_env = env;
    for (comp_decl const & d : ds) {
        new_env = reserve_vm_index(new_env, d.fst(), d.snd());
    }

    for (comp_decl const & d : ds) {
        buffer<vm_instr> code;
        emit_bytecode_fn emitter(new_env, code);
        list<vm_local_info> args_info;
        unsigned arity;
        std::tie(arity, args_info) = emitter(d.snd());
        lean_trace(name({"compiler", "code_gen"}), tout() << " " << d.fst() << " " << arity << "\n";
                   display_vm_code(tout().get_stream(), code.size(), code.data()););
        optimize(new_env, code);
        lean_trace(name({"compiler", "optimize_bytecode"}), tout() << " " << d.fst() << " " << arity << "\n";
                   display_vm_code(tout().get_stream(), code.size(), code.data()););
        new_env = update_vm_code(new_env, d.fst(), code.size(), code.data(), args_info);
    }
    return new_env;
}
}
