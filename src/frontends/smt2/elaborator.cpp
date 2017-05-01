/*
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Daniel Selsam
*/
#include <string>
#include <unordered_set>
#include "util/name_hash_map.h"
#include "kernel/environment.h"
#include "kernel/abstract.h"
#include "kernel/instantiate.h"
#include "library/type_context.h"
#include "library/constants.h"
#include "frontends/smt2/elaborator.h"

namespace lean {
namespace smt2 {

static name * g_smt2_user_name_prefix;

// Util
static inline level l1() { return mk_level_one(); }

// Dispatch
// (1) constants that can be elaborated independently of their arguments
static std::unordered_map<std::string, expr> * g_constant_map = nullptr;

// (2) arithmetic operators
enum class arith_app_type { MOD, ABS, DIV, SLASH, ADD, MUL, MINUS, LT, LE, GT, GE };
enum class fun_attr { DEFAULT, LEFT_ASSOC, RIGHT_ASSOC, CHAINABLE }; // pairwise treated specially

struct arith_app_info {
    name              m_op;
    name              m_int_inst;
    name              m_real_inst;
    fun_attr          m_fun_attr;
    arith_app_info(name const & op, name const & int_inst, name const & real_inst, fun_attr const & fattr):
        m_op(op), m_int_inst(int_inst), m_real_inst(real_inst), m_fun_attr(fattr) {}
    arith_app_info(name const & op, name const & int_inst, name const & real_inst):
        m_op(op), m_int_inst(int_inst), m_real_inst(real_inst), m_fun_attr(fun_attr::DEFAULT) {}
    arith_app_info(name const & op, name const & int_inst):
        m_op(op), m_int_inst(int_inst), m_fun_attr(fun_attr::DEFAULT) {}

    name const & get_op_name() const { return m_op; }

    bool has_int_inst_name() const { return !m_int_inst.is_anonymous(); }
    name const & get_int_inst_name() const {
        lean_assert(has_int_inst_name());
        return m_int_inst;
    }

    bool has_real_inst_name() const { return !m_real_inst.is_anonymous(); }
    name const & get_real_inst_name() const {
        lean_assert(has_real_inst_name());
        return m_real_inst;
    }

    fun_attr const & get_fun_attr() const { return m_fun_attr; }
};

static name_hash_map<arith_app_info> * g_arith_symbol_map  = nullptr;

// (3) operators that do not have implicit arguments but that require e.g. left-assoc
static name_hash_map<pair<expr, fun_attr>> * g_constant_fun_attr_map = nullptr;

// (4) special operators that require custom procedures
enum class special_app_kind { IMPLIES, ITE, DISTINCT, EQ, SELECT, STORE };
static name_hash_map<special_app_kind> * g_special_map               = nullptr;

// (5) hash-set of all symbols in (2-4), so that the constant-elaborator knows to skip them
static std::unordered_set<std::string> * g_skip_constant_map = nullptr;

// Makers for functions with attributes
static expr mk_left_assoc_app(buffer<expr> const & args) {
    lean_assert(args.size() >= 2);
    // f x1 x2 x3 ==> f (f x1 x2) x3
    expr e = mk_app(args[0], args[1], args[2]);
    for (unsigned i = 3; i < args.size(); ++i) {
        e = mk_app(args[0], e, args[i]);
    }
    return e;
}

static expr mk_right_assoc_app(buffer<expr> const & args) {
    lean_assert(args.size() >= 3);
    // f x1 x2 x3 ==> f x1 (f x2 x3)
    int k = args.size();
    expr e = mk_app(args[0], args[k - 2], args[k - 1]);
    for (int i = k - 3; i > 0; --i) {
        e = mk_app(args[0], args[i], e);
    }
    return e;
}

static expr mk_chainable_app(buffer<expr> const & args) {
    // f x1 x2 x3 ==> and (f x1 x2) (f x2 x3)
    if (args.size() == 3) {
        return mk_app(args);
    }
    lean_assert(args.size() >= 3);
    buffer<expr> args_to_and;
    args_to_and.push_back(mk_constant(get_and_name()));
    for (unsigned i = 1; i < args.size() - 1; ++i) {
        args_to_and.push_back(mk_app(args[0], args[i], args[i+1]));
    }
    return mk_left_assoc_app(args_to_and);
}

// TODO(dhs): use a macro for this? It scales quadratically.
// At this stage in elaboration: ["@distinct A", arg1, ... ,argN]
static expr mk_distinct_app(buffer<expr> const & args) {
    unsigned num_args = args.size() - 1;
    if (num_args == 1)
        return mk_constant(get_true_name());
    expr eq = mk_app(mk_constant(get_eq_name(), {l1()}), app_arg(args[0]));
    if (num_args == 2)
        return mk_app(mk_constant(get_not_name()), mk_app(eq, args[1], args[2]));
    buffer<expr> new_args;
    new_args.push_back(mk_constant(get_and_name()));
    for (unsigned i = 0; i < num_args - 1; ++i) {
        for (unsigned j = i + 1; j < num_args; ++j) {
            new_args.push_back(mk_app(mk_constant(get_not_name()), mk_app(eq, args[1+i], args[1+j])));
        }
    }
    return mk_left_assoc_app(new_args);
}

expr mk_app_attrs(buffer<expr> & args, fun_attr const & fattr) {
    switch (fattr) {
    case fun_attr::DEFAULT:      return mk_app(args);
    case fun_attr::LEFT_ASSOC:   return mk_left_assoc_app(args);
    case fun_attr::RIGHT_ASSOC:  return mk_right_assoc_app(args);
    case fun_attr::CHAINABLE:    return mk_chainable_app(args);
    }
    lean_unreachable();
}

class elaborate_app_fn {
    type_context & m_tctx;

private:
    // Elaborators for special symbols
    expr elaborate_ite(buffer<expr> & args) {
        lean_assert(is_constant(args[0]) && const_name(args[0]) == get_ite_name());
        // Have: ite.{} <P:Prop> <x:A> <y:A>
        // Want: ite.{1} P (classical.prop_decidable P) A x y
        expr ty = m_tctx.infer(args[2]);
        buffer<expr> new_args;
        new_args.push_back(mk_constant(get_ite_name(), {l1()}));
        new_args.push_back(args[1]);
        new_args.push_back(mk_app(mk_constant(get_classical_prop_decidable_name()), args[1]));
        new_args.push_back(ty);
        new_args.push_back(args[2]);
        new_args.push_back(args[3]);
        return mk_app(new_args);
    }

    expr elaborate_distinct(buffer<expr> & args) {
        expr ty = m_tctx.infer(args[1]);
        args[0] = mk_app(mk_constant(get_ne_name(), {l1()}), ty);
        return mk_distinct_app(args);
    }

    expr elaborate_eq(buffer<expr> & args) {
        lean_assert(is_constant(args[0]) && const_name(args[0]) == "=");
        expr ty = m_tctx.infer(args[1]);
        args[0] = mk_app(mk_constant(get_eq_name(), {l1()}), ty);
        return mk_chainable_app(args);
    }

    expr elaborate_implies(buffer<expr> & args) {
        lean_assert(is_constant(args[0]) && const_name(args[0]) == "=>");
        int k = args.size();
        expr e = mk_arrow(args[k - 2], args[k - 1]);
        for (int i = k - 3; i > 0; --i) {
            e = mk_arrow(args[i], e);
        }
        return e;
    }

    expr elaborate_select(buffer<expr> & args) {
        expr ty = m_tctx.infer(args[1]);
        buffer<expr> array_args;
        expr array = get_app_args(ty, array_args);
        lean_assert(is_constant(array) && const_name(array) == get_smt_array_name());
        args[0] = mk_app(mk_constant(get_smt_select_name(), {l1(), l1()}), array_args[0], array_args[1]);
        return mk_app(args);
    }

    expr elaborate_store(buffer<expr> & args) {
        expr ty = m_tctx.infer(args[1]);
        buffer<expr> array_args;
        expr array = get_app_args(ty, array_args);
        lean_assert(is_constant(array) && const_name(array) == get_smt_array_name());
        expr dec_eq = mk_app(mk_constant(get_classical_type_decidable_eq_name(), {l1()}), array_args[0]);
        args[0] = mk_app(mk_constant(get_smt_store_name(), {l1(), l1()}), array_args[0], array_args[1], dec_eq);
        return mk_app(args);
    }

    expr elaborate_arith(buffer<expr> & args, arith_app_info const & info) {
        lean_assert(args.size() > 1);
        expr ty = m_tctx.infer(args[1]);
        if (ty == mk_constant(get_int_name())) {
            args[0] = mk_app(mk_constant(info.get_op_name(), {mk_level_one()}), mk_constant(get_int_name()), mk_constant(info.get_int_inst_name()));
        } else {
            lean_assert(ty == mk_constant(get_real_name()));
            args[0] = mk_app(mk_constant(info.get_op_name(), {mk_level_one()}), mk_constant(get_real_name()), mk_constant(info.get_real_inst_name()));
        }
        return mk_app_attrs(args, info.get_fun_attr());
    }

    // Note: we do not coerce [Array Int Int] to [Array Real Real]
    void coerce_mixed_int_real(buffer<expr> & args) {
        bool found_int = false;
        bool found_real = false;

        buffer<bool> is_int;
        buffer<bool> is_real;

        for (unsigned i = 1; i < args.size(); ++i) {
            expr ty = m_tctx.infer(args[i]);
            if (ty == mk_constant(get_int_name())) {
                is_int.push_back(true);
                is_real.push_back(false);
                found_int = true;
            } else if (ty == mk_constant(get_real_name())) {
                is_int.push_back(false);
                is_real.push_back(true);
                found_real = true;
            } else {
                is_int.push_back(false);
                is_real.push_back(false);
            }
        }
        // The arith-normalizer will push the coercions inside.
        bool coerce_all_ints = is_constant(args[0]) && const_name(args[0]) == "/";
        if (found_int && (found_real || coerce_all_ints)) {
            for (unsigned i = 0; i < is_real.size(); ++i) {
                if (is_int[i]) {
                    args[i+1] = mk_app(mk_constant(get_real_of_int_name()), args[i+1]);
                }
            }
        }
    }

    // Main function
    expr elaborate_app(buffer<expr> & args) {
        lean_assert(args.size() > 0);
        if (!is_constant(args[0])) {
            // TODO(dhs): (extract i j) requires elaboration
            return mk_app(args);
        }

        lean_assert(is_constant(args[0]));
        name n = const_name(args[0]);

        // Special case
        // (the map stores "-" ==> sub)
        if (n == "-" && args.size() == 2) {
            arith_app_info info(get_has_neg_neg_name(), get_int_has_neg_name(), get_real_has_neg_name());
            return elaborate_arith(args, info);
        }

        auto it_fun_attr = g_constant_fun_attr_map->find(n);
        if (it_fun_attr != g_constant_fun_attr_map->end()) {
            args[0] = it_fun_attr->second.first;
            return mk_app_attrs(args, it_fun_attr->second.second);
        }

        auto it_arith = g_arith_symbol_map->find(n);
        if (it_arith != g_arith_symbol_map->end()) {
            coerce_mixed_int_real(args);
            return elaborate_arith(args, it_arith->second);
        }

        auto it_special = g_special_map->find(n);
        if (it_special != g_special_map->end()) {
            switch (it_special->second) {
            case special_app_kind::EQ:             coerce_mixed_int_real(args); return elaborate_eq(args);
            case special_app_kind::ITE:            coerce_mixed_int_real(args); return elaborate_ite(args);
            case special_app_kind::DISTINCT:       coerce_mixed_int_real(args); return elaborate_distinct(args);
            case special_app_kind::IMPLIES:                                     return elaborate_implies(args);
            case special_app_kind::SELECT:                                      return elaborate_select(args);
            case special_app_kind::STORE:                                       return elaborate_store(args);
            }
        }

        return mk_app(args);
    }


public:
    elaborate_app_fn(type_context & tctx): m_tctx(tctx) {}
    expr operator()(buffer<expr> & args) { return elaborate_app(args); }
};

// Setup and teardown
void initialize_elaborator() {
    g_smt2_user_name_prefix = new name(name::mk_internal_unique_name());

    g_constant_map = new std::unordered_map<std::string, expr>({
            {"Bool", mk_Prop()},
            {"true", mk_constant(get_true_name())},
            {"false", mk_constant(get_false_name())},
            {"not", mk_constant(get_not_name())},
            {"Int", mk_constant(get_int_name())},
            {"Real", mk_constant(get_real_name())},
            {"Array", mk_constant(get_smt_array_name(), {l1(), l1()})},
            {"to_real", mk_constant(get_real_of_int_name())},
            {"to_int", mk_constant(get_real_to_int_name())},
            {"is_int", mk_constant(get_real_is_int_name())}
        });

    g_constant_fun_attr_map = new name_hash_map<pair<expr, fun_attr>>({
            {"and", mk_pair(mk_constant(get_and_name()), fun_attr::LEFT_ASSOC)},
            {"or", mk_pair(mk_constant(get_or_name()), fun_attr::LEFT_ASSOC)},
            {"xor", mk_pair(mk_constant(get_xor_name()), fun_attr::LEFT_ASSOC)}
        });

    g_arith_symbol_map = new name_hash_map<arith_app_info>({
            // Int-specific
            {"mod", arith_app_info(get_has_mod_mod_name(), get_int_has_mod_name())},
            {"abs", arith_app_info(get_abs_name(), get_int_decidable_linear_ordered_comm_group_name())},
            {"div", arith_app_info(get_has_div_div_name(), get_int_has_div_name(), name(), fun_attr::LEFT_ASSOC)},

            // Real-specific
            {"/", arith_app_info(get_has_div_div_name(), name(), get_real_has_div_name(), fun_attr::LEFT_ASSOC)},

            // Overloaded operators
            {"+", arith_app_info(get_has_add_add_name(), get_int_has_add_name(), get_real_has_add_name(), fun_attr::LEFT_ASSOC)},
            {"*", arith_app_info(get_has_mul_mul_name(), get_int_has_mul_name(), get_real_has_mul_name(), fun_attr::LEFT_ASSOC)},
            {"-", arith_app_info(get_has_sub_sub_name(), get_int_has_sub_name(), get_real_has_sub_name(), fun_attr::LEFT_ASSOC)},

            {"<", arith_app_info(get_has_lt_lt_name(), get_int_has_lt_name(), get_real_has_lt_name(), fun_attr::CHAINABLE)},
            {"<=", arith_app_info(get_has_le_le_name(), get_int_has_le_name(), get_real_has_le_name(), fun_attr::CHAINABLE)},
            {">", arith_app_info(get_gt_name(), get_int_has_lt_name(), get_real_has_lt_name(), fun_attr::CHAINABLE)},
            {">=", arith_app_info(get_ge_name(), get_int_has_le_name(), get_real_has_le_name(), fun_attr::CHAINABLE)},
                });

    g_special_map = new name_hash_map<special_app_kind>({
            {"ite", special_app_kind::ITE},
            {"distinct", special_app_kind::DISTINCT},
            {"=", special_app_kind::EQ},
            {"=>", special_app_kind::IMPLIES},
            {"select", special_app_kind::SELECT},
            {"store", special_app_kind::STORE}
        });

    g_skip_constant_map = new std::unordered_set<std::string>();
    for (auto p : *g_constant_fun_attr_map) g_skip_constant_map->insert(p.first.get_string());
    for (auto p : *g_arith_symbol_map) g_skip_constant_map->insert(p.first.get_string());
    for (auto p : *g_special_map) g_skip_constant_map->insert(p.first.get_string());
}

void finalize_elaborator() {
    delete g_smt2_user_name_prefix;

    delete g_skip_constant_map;
    delete g_special_map;
    delete g_arith_symbol_map;
    delete g_constant_fun_attr_map;
    delete g_constant_map;
}

// Entry points
name mk_user_name(std::string const & s) { return name(*g_smt2_user_name_prefix, s.c_str()); }

expr elaborate_constant(std::string const & symbol) {
    // Note: true, false, and not do not need elaboration at the constant level nor the app level
    auto it = g_constant_map->find(symbol);
    if (it != g_constant_map->end()) {
        return it->second;
    }

    auto it_skip = g_skip_constant_map->find(symbol);
    if (it_skip != g_skip_constant_map->end()) {
        return mk_constant(symbol);
    }

    return mk_constant(mk_user_name(symbol));
}

expr elaborate_app(type_context & tctx, buffer<expr> & args) {
    return elaborate_app_fn(tctx)(args);
}


}}
