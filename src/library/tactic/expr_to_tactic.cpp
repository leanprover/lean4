/*
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <unordered_map>
#include <string>
#include "util/sstream.h"
#include "util/optional.h"
#include "kernel/instantiate.h"
#include "kernel/type_checker.h"
#include "library/annotation.h"
#include "library/string.h"
#include "library/num.h"
#include "library/kernel_serializer.h"
#include "library/tactic/expr_to_tactic.h"
#include "library/tactic/intros_tactic.h"

namespace lean {
static expr * g_exact_tac_fn      = nullptr;
static expr * g_and_then_tac_fn   = nullptr;
static expr * g_or_else_tac_fn    = nullptr;
static expr * g_id_tac_fn         = nullptr;
static expr * g_repeat_tac_fn     = nullptr;
static expr * g_determ_tac_fn     = nullptr;
static expr * g_tac_type          = nullptr;
static expr * g_builtin_tac       = nullptr;
static expr * g_fixpoint_tac      = nullptr;
expr const & get_exact_tac_fn() { return *g_exact_tac_fn; }
expr const & get_and_then_tac_fn() { return *g_and_then_tac_fn; }
expr const & get_or_else_tac_fn() { return *g_or_else_tac_fn; }
expr const & get_id_tac_fn() { return *g_id_tac_fn; }
expr const & get_determ_tac_fn() { return *g_determ_tac_fn; }
expr const & get_repeat_tac_fn() { return *g_repeat_tac_fn; }
expr const & get_tactic_type() { return *g_tac_type; }
expr const & get_builtin_tac() { return *g_builtin_tac; }

typedef std::unordered_map<name, expr_to_tactic_fn, name_hash, name_eq> expr_to_tactic_map;
static expr_to_tactic_map * g_map = nullptr;

expr_to_tactic_map & get_expr_to_tactic_map() {
    return *g_map;
}

void register_tac(name const & n, expr_to_tactic_fn const & fn) {
    get_expr_to_tactic_map().insert(mk_pair(n, fn));
}

bool has_tactic_decls(environment const & env) {
    try {
        type_checker tc(env);
        return
            tc.infer(*g_builtin_tac).first     == *g_tac_type &&
            tc.infer(*g_and_then_tac_fn).first == *g_tac_type >> (*g_tac_type >> *g_tac_type) &&
            tc.infer(*g_or_else_tac_fn).first  == *g_tac_type >> (*g_tac_type >> *g_tac_type) &&
            tc.infer(*g_repeat_tac_fn).first   == *g_tac_type >> *g_tac_type;
    } catch (exception &) {
        return false;
    }
}

static name * g_tactic_name = nullptr;
static std::string * g_tactic_opcode = nullptr;

name const & get_tactic_name() { return *g_tactic_name; }
std::string const & get_tactic_opcode() { return *g_tactic_opcode; }

LEAN_THREAD_VALUE(bool, g_unfold_tactic_macros, true);

/** \brief We use macros to wrap some builtin tactics that would not type check otherwise.
    Example: in the tactic `apply t`, `t` is a pre-term (i.e., a term before elaboration).
    Moreover its context depends on the goal it is applied to.
*/
class tactic_macro_definition_cell : public macro_definition_cell {
    name              m_name;
    expr_to_tactic_fn m_fn;
public:
    tactic_macro_definition_cell(name const & n, expr_to_tactic_fn const & fn):
        m_name(n), m_fn(fn) {}
    name const & get_tatic_kind() const { return m_name; }
    expr_to_tactic_fn const & get_fn() const { return m_fn; }
    virtual bool operator==(macro_definition_cell const & other) const {
        if (tactic_macro_definition_cell const * other_ptr = dynamic_cast<tactic_macro_definition_cell const *>(&other)) {
            return m_name == other_ptr->m_name;
        } else {
            return false;
        }
    }
    virtual name get_name() const { return get_tactic_name(); }
    virtual format pp(formatter const &) const { return format(m_name); }
    virtual void display(std::ostream & out) const { out << m_name; }
    virtual pair<expr, constraint_seq> get_type(expr const &, extension_context &) const {
        return mk_pair(get_tactic_type(), constraint_seq());
    }
    virtual optional<expr> expand(expr const &, extension_context &) const {
        // Remark: small hack for conditionally expanding tactic macros.
        // When processing type checking a macro definition, we want to unfold it,
        // otherwise the kernel will not accept it.
        // When converting it to a tactic object, we don't want to unfold it.
        // The procedure expr_to_tactic temporarily sets g_unfold_tactic_macros to false.
        // This is a thread local storage. So, there is no danger.
        if (g_unfold_tactic_macros)
            return some_expr(get_builtin_tac());
        else
            return none_expr();
    }
    virtual void write(serializer & s) const {
        s.write_string(get_tactic_opcode());
        s << m_name;
    }
};

typedef std::unordered_map<name, macro_definition, name_hash, name_eq>  tactic_macros;
static tactic_macros * g_tactic_macros = nullptr;
tactic_macros & get_tactic_macros() { return *g_tactic_macros; }

void register_tactic_macro(name const & n, expr_to_tactic_fn const & fn) {
    tactic_macros & ms = get_tactic_macros();
    lean_assert(ms.find(n) == ms.end());
    ms.insert(mk_pair(n, macro_definition(new tactic_macro_definition_cell(n, fn))));
}

static void register_tacm(name const & n, expr_to_tactic_fn const & fn) {
    register_tactic_macro(n, fn);
}

expr mk_tactic_macro(name const & kind, unsigned num_args, expr const * args) {
    tactic_macros & ms = get_tactic_macros();
    auto it = ms.find(kind);
    if (it != ms.end()) {
        return mk_macro(it->second, num_args, args);
    } else {
        throw exception(sstream() << "unknown builtin tactic '" << kind << "'");
    }
}

expr mk_tactic_macro(name const & kind, expr const & e) {
    return mk_tactic_macro(kind, 1, &e);
}

bool is_tactic_macro(expr const & e) {
    return is_macro(e) && macro_def(e).get_name() == get_tactic_name();
}

static name * g_rename_tactic_name = nullptr;
static name * g_intros_tactic_name = nullptr;

expr mk_rename_tactic_macro(name const & from, name const & to) {
    expr args[2] = { Const(from), Const(to) };
    return mk_tactic_macro(*g_rename_tactic_name, 2, args);
}

expr mk_intros_tactic_macro(buffer<name> const & ns) {
    buffer<expr> args;
    for (name const & n : ns) {
        args.push_back(Const(n));
    }
    return mk_tactic_macro(*g_intros_tactic_name, args.size(), args.data());
}

expr_to_tactic_fn const & get_tactic_macro_fn(expr const & e) {
    lean_assert(is_tactic_macro(e));
    return static_cast<tactic_macro_definition_cell const*>(macro_def(e).raw())->get_fn();
}

static void throw_failed(expr const & e) {
    throw expr_to_tactic_exception(e, "failed to convert expression into tactic");
}

/** \brief Return true if v is the constant tactic.builtin or the constant function that returns tactic.builtin_tactic */
static bool is_builtin_tactic(expr const & v) {
    if (is_lambda(v))
        return is_builtin_tactic(binding_body(v));
    else if (v == *g_builtin_tac)
        return true;
    else
        return false;
}

tactic expr_to_tactic(type_checker & tc, elaborate_fn const & fn, expr e, pos_info_provider const * p) {
    e = tc.whnf(e).first;
    if (is_tactic_macro(e)) {
        return get_tactic_macro_fn(e)(tc, fn, e, p);
    } else {
        expr f = get_app_fn(e);
        if (!is_constant(f))
            throw_failed(e);
        optional<declaration> it = tc.env().find(const_name(f));
        if (!it || !it->is_definition())
            throw_failed(e);
        expr v = it->get_value();
        if (is_builtin_tactic(v)) {
            auto const & map = get_expr_to_tactic_map();
            auto it2 = map.find(const_name(f));
            if (it2 != map.end())
                return it2->second(tc, fn, e, p);
            else
                throw expr_to_tactic_exception(e, sstream() << "implementation for builtin tactic '" <<
                                               const_name(f) << "' was not found");
        } else {
            // unfold definition
            buffer<expr> locals;
            get_app_rev_args(e, locals);
            level_param_names const & ps = it->get_univ_params();
            levels ls = const_levels(f);
            unsigned num_ps = length(ps);
            unsigned num_ls = length(ls);
            if (num_ls > num_ps)
                throw expr_to_tactic_exception(e, sstream() << "invalid number of universes");
            if (num_ls < num_ps) {
                buffer<level> extra_ls;
                name_generator ngen = tc.mk_ngen();
                for (unsigned i = num_ls; i < num_ps; i++)
                    extra_ls.push_back(mk_meta_univ(ngen.next()));
                ls = append(ls, to_list(extra_ls.begin(), extra_ls.end()));
            }
            v = instantiate_univ_params(v, ps, ls);
            v = apply_beta(v, locals.size(), locals.data());
            return expr_to_tactic(tc, fn, v, p);
        }
    }
}

static name * g_tmp_prefix = nullptr;
LEAN_THREAD_VALUE(unsigned, g_expr_tac_id, 0);
static name_generator next_name_generator() {
    unsigned r = g_expr_tac_id;
    g_expr_tac_id++;
    return name_generator(name(*g_tmp_prefix, r));
}

tactic expr_to_tactic(environment const & env, elaborate_fn const & fn, expr const & e, pos_info_provider const * p) {
    flet<bool> let(g_unfold_tactic_macros, false);
    type_checker tc(env, next_name_generator());
    return expr_to_tactic(tc, fn, e, p);
}

tactic fixpoint(expr const & b, elaborate_fn const & fn) {
    return tactic([=](environment const & env, io_state const & ios, proof_state const & s) -> proof_state_seq {
            return expr_to_tactic(env, fn, b, nullptr)(env, ios, s);
        });
}

void register_simple_tac(name const & n, std::function<tactic()> f) {
    register_tac(n, [=](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
            if (!is_constant(e))
                throw expr_to_tactic_exception(e, "invalid constant tactic");
            return f();
        });
}

void register_bin_tac(name const & n, std::function<tactic(tactic const &, tactic const &)> f) {
    register_tac(n, [=](type_checker & tc, elaborate_fn const & fn, expr const & e, pos_info_provider const * p) {
            buffer<expr> args;
            get_app_args(e, args);
            if (args.size() != 2)
                throw expr_to_tactic_exception(e, "invalid binary tactic, it must have two arguments");
            tactic t1 = expr_to_tactic(tc, fn, args[0], p);
            tactic t2 = expr_to_tactic(tc, fn, args[1], p);
            return f(t1, t2);
        });
}

void register_unary_tac(name const & n, std::function<tactic(tactic const &)> f) {
    register_tac(n, [=](type_checker & tc, elaborate_fn const & fn, expr const & e, pos_info_provider const * p) {
            buffer<expr> args;
            get_app_args(e, args);
            if (args.size() != 1)
                throw expr_to_tactic_exception(e, "invalid unary tactic, it must have one argument");
            return f(expr_to_tactic(tc, fn, args[0], p));
        });
}

void register_unary_num_tac(name const & n, std::function<tactic(tactic const &, unsigned k)> f) {
    register_tac(n, [=](type_checker & tc, elaborate_fn const & fn, expr const & e, pos_info_provider const * p) {
            buffer<expr> args;
            get_app_args(e, args);
            if (args.size() != 2)
                throw expr_to_tactic_exception(e, "invalid tactic, it must have two arguments");
            tactic t = expr_to_tactic(tc, fn, args[0], p);
            optional<mpz> k = to_num(args[1]);
            if (!k)
                k = to_num(tc.whnf(args[1]).first);
            if (!k)
                throw expr_to_tactic_exception(e, "invalid tactic, second argument must be a numeral");
            if (!k->is_unsigned_int())
                throw expr_to_tactic_exception(e,
                                               "invalid tactic, second argument does not fit in "
                                               "a machine unsigned integer");
            return f(t, k->get_unsigned_int());
        });
}

static name * g_by_name = nullptr;

expr mk_by(expr const & e) { return mk_annotation(*g_by_name, e); }
bool is_by(expr const & e) { return is_annotation(e, *g_by_name); }
expr const & get_by_arg(expr const & e) { lean_assert(is_by(e)); return get_annotation_arg(e); }

void check_macro_args(expr const & e, unsigned num_args, char const * msg) {
    if (!is_macro(e) || macro_num_args(e) != num_args)
        throw expr_to_tactic_exception(e, msg);
}

void initialize_expr_to_tactic() {
    g_tmp_prefix        = new name(name::mk_internal_unique_name());

    g_by_name           = new name("by");
    register_annotation(*g_by_name);

    g_map               = new expr_to_tactic_map();

    g_tactic_name       = new name("tactic");
    g_tactic_opcode     = new std::string("TAC");

    g_tactic_macros     = new tactic_macros();

    register_macro_deserializer(*g_tactic_opcode,
                                [](deserializer & d, unsigned num, expr const * args) {
                                    name kind;
                                    d >> kind;
                                    return mk_tactic_macro(kind, num, args);
                                });

    g_rename_tactic_name = new name(*g_tactic_name, "rename");
    g_intros_tactic_name = new name(*g_tactic_name, "intros");

    name builtin_tac_name(*g_tactic_name, "builtin");
    name exact_tac_name(*g_tactic_name, "exact");
    name and_then_tac_name(*g_tactic_name, "and_then");
    name or_else_tac_name(*g_tactic_name, "or_else");
    name repeat_tac_name(*g_tactic_name, "repeat");
    name fixpoint_name(*g_tactic_name, "fixpoint");
    name determ_tac_name(*g_tactic_name, "determ");
    name id_tac_name(*g_tactic_name, "id");
    g_exact_tac_fn      = new expr(Const(exact_tac_name));
    g_and_then_tac_fn   = new expr(Const(and_then_tac_name));
    g_or_else_tac_fn    = new expr(Const(or_else_tac_name));
    g_id_tac_fn         = new expr(Const(id_tac_name));
    g_repeat_tac_fn     = new expr(Const(repeat_tac_name));
    g_determ_tac_fn     = new expr(Const(determ_tac_name));
    g_tac_type          = new expr(Const(*g_tactic_name));
    g_builtin_tac       = new expr(Const(builtin_tac_name));
    g_fixpoint_tac      = new expr(Const(fixpoint_name));

    register_simple_tac(id_tac_name,
                        []() { return id_tactic(); });
    register_simple_tac(name(*g_tactic_name, "now"),
                        []() { return now_tactic(); });
    register_simple_tac(name(*g_tactic_name, "assumption"),
                        []() { return assumption_tactic(); });
    register_simple_tac(name(*g_tactic_name, "fail"),
                        []() { return fail_tactic(); });
    register_simple_tac(name(*g_tactic_name, "beta"),
                        []() { return beta_tactic(); });
    register_bin_tac(and_then_tac_name,
                     [](tactic const & t1, tactic const & t2) { return then(t1, t2); });
    register_bin_tac(name(*g_tactic_name, "append"),
                     [](tactic const & t1, tactic const & t2) { return append(t1, t2); });
    register_bin_tac(name(*g_tactic_name, "interleave"),
                     [](tactic const & t1, tactic const & t2) { return interleave(t1, t2); });
    register_bin_tac(name(*g_tactic_name, "par"),
                     [](tactic const & t1, tactic const & t2) { return par(t1, t2); });
    register_bin_tac(or_else_tac_name,
                     [](tactic const & t1, tactic const & t2) { return orelse(t1, t2); });
    register_unary_tac(repeat_tac_name,
                       [](tactic const & t1) { return repeat(t1); });
    register_tac(name(*g_tactic_name, "state"),
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const * p) {
                     if (p)
                         if (auto it = p->get_pos_info(e))
                             return trace_state_tactic(std::string(p->get_file_name()), *it);
                     return trace_state_tactic();
                 });
    register_tac(name(*g_tactic_name, "trace"),
                 [](type_checker & tc, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     buffer<expr> args;
                     get_app_args(e, args);
                     if (args.size() != 1)
                         throw expr_to_tactic_exception(e, "invalid trace tactic, argument expected");
                     if (auto str = to_string(args[0]))
                         return trace_tactic(*str);
                     else if (auto str = to_string(tc.whnf(args[0]).first))
                         return trace_tactic(*str);
                     else
                         throw expr_to_tactic_exception(e, "invalid trace tactic, string value expected");
                 });
    register_tacm(*g_rename_tactic_name,
                  [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                      check_macro_args(e, 2, "invalid 'rename' tactic, it must have two arguments");
                      if (!is_constant(macro_arg(e, 0)) || !is_constant(macro_arg(e, 1)))
                          throw expr_to_tactic_exception(e, "invalid 'rename' tactic, arguments must be identifiers");
                      return rename_tactic(const_name(macro_arg(e, 0)), const_name(macro_arg(e, 1)));
                  });
    register_tacm(*g_intros_tactic_name,
                  [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                      buffer<name> ns;
                      for (unsigned i = 0; i < macro_num_args(e); i++) {
                          expr const & arg = macro_arg(e, i);
                          if (!is_constant(arg))
                              throw expr_to_tactic_exception(e, "invalid 'intros' tactic, arguments must be identifiers");
                          ns.push_back(const_name(arg));
                      }
                      return intros_tactic(to_list(ns.begin(), ns.end()));
                  });
    register_tac(exact_tac_name,
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     // TODO(Leo): use elaborate_fn
                     return exact_tactic(app_arg(e));
                 });
    register_tac(name(*g_tactic_name, "unfold"),
                 [](type_checker &, elaborate_fn const &, expr const & e, pos_info_provider const *) {
                     expr id = get_app_fn(app_arg(e));
                     if (!is_constant(id))
                         return fail_tactic();
                     else
                         return unfold_tactic(const_name(id));
                 });
    register_unary_num_tac(name(*g_tactic_name, "at_most"),
                           [](tactic const & t, unsigned k) { return take(t, k); });
    register_unary_num_tac(name(*g_tactic_name, "discard"),
                           [](tactic const & t, unsigned k) { return discard(t, k); });
    register_unary_num_tac(name(*g_tactic_name, "focus_at"),
                           [](tactic const & t, unsigned k) { return focus(t, k); });
    register_unary_num_tac(name(*g_tactic_name, "try_for"),
                           [](tactic const & t, unsigned k) { return try_for(t, k); });
    register_tac(fixpoint_name,
                 [](type_checker & tc, elaborate_fn const & fn, expr const & e, pos_info_provider const *) {
                     if (!is_constant(app_fn(e)))
                         throw expr_to_tactic_exception(e, "invalid fixpoint tactic, it must have one argument");
                     expr r = tc.whnf(mk_app(app_arg(e), e)).first;
                     return fixpoint(r, fn);
                 });
}

void finalize_expr_to_tactic() {
    delete g_fixpoint_tac;
    delete g_builtin_tac;
    delete g_tac_type;
    delete g_determ_tac_fn;
    delete g_repeat_tac_fn;
    delete g_or_else_tac_fn;
    delete g_and_then_tac_fn;
    delete g_id_tac_fn;
    delete g_exact_tac_fn;
    delete g_rename_tactic_name;
    delete g_intros_tactic_name;
    delete g_tactic_macros;
    delete g_map;
    delete g_tactic_name;
    delete g_tactic_opcode;
    delete g_by_name;
    delete g_tmp_prefix;
}
}
