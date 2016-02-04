/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#pragma once
#include <vector>
#include "util/debug.h"
#include "util/buffer.h"
#include "util/numerics/numeric_traits.h"
#include "util/numerics/xnumeral.h"
#include <unordered_map>
#include <unordered_set>
#include <string>
#include "util/lp/lar_constraints.h"
#include <functional>
#include "util/lp/lar_core_solver.h"
#include <algorithm>
#include "util/lp/numeric_pair.h"
#include "util/lp/lar_solution_signature.h"
#include "util/lp/scaler.h"
#include "util/lp/lp_primal_core_solver.h"

namespace lean {
template <typename V>
struct conversion_helper {
    static V get_low_bound(const column_info<mpq> & ci) {
        return V(ci.get_low_bound(), ci.low_bound_is_strict()? 1 : 0);
    }

    static V get_upper_bound(const column_info<mpq> & ci) {
        return V(ci.get_upper_bound(), ci.upper_bound_is_strict()? -1 : 0);
    }
};

template<>
struct conversion_helper <double> {
    static double get_low_bound(const column_info<mpq> & ci);
    static double get_upper_bound(const column_info<mpq> & ci);
};

class lar_solver {
    unsigned m_available_var_index = 0;
    unsigned m_available_constr_index = 0;
    lp_status m_status = UNKNOWN;
    std::unordered_map<std::string, var_index> m_var_names_to_var_index;
    std::unordered_map<var_index, canonic_left_side*> m_map_from_var_index_to_left_side;
    std::unordered_set<canonic_left_side*, hash_and_equal_of_canonic_left_side_struct, hash_and_equal_of_canonic_left_side_struct> m_canonic_left_sides;
    std::unordered_map<unsigned, canonic_left_side*> m_column_indices_to_canonic_left_sides;
    std::unordered_map<constraint_index, lar_normalized_constraint> m_normalized_constraints;
    static_matrix<mpq, numeric_pair<mpq>> m_A;
    lar_core_solver<mpq, numeric_pair<mpq>> m_mpq_core_solver;
    lp_settings m_settings;
    std::vector<column_type> m_column_types; // this field is passed to the core solver
    std::vector<numeric_pair<mpq>> m_low_bounds; // passed to the core solver
    std::vector<numeric_pair<mpq>> m_upper_bounds; // passed to the core solver
    std::vector<unsigned> m_basis;
    std::vector<numeric_pair<mpq>> m_x; // the solution
    std::unordered_map<unsigned, std::string> m_column_names;
    std::vector<numeric_pair<mpq>> m_right_side_vector; // this vector will be all zeroes, it might change when the optimization with fixed variables will used
    std::vector<mpq> m_costs;
    canonic_left_side * m_infeasible_canonic_left_side = nullptr; // such can be found at the initialization step
    canonic_left_side * create_or_fetch_existing_left_side(const buffer<pair<mpq, var_index>>& left_side_par);


    bool var_is_fixed(unsigned j);

    mpq find_ratio(canonic_left_side * ls, const lar_constraint & constraint);

    void add_canonic_left_side_for_var(var_index i, std::string var_name);

    void map_left_side_to_column_of_A(canonic_left_side*  left_side, unsigned & j);


    void map_left_sides_to_columns_of_A();

    bool valid_index(unsigned j) { return static_cast<int>(j) >= 0;}


    // this adds a row to A
    template <typename U, typename V>
    void add_row_to_A(static_matrix<U, V> & A, unsigned i, canonic_left_side * ls);

    template <typename U, typename V>
    void create_matrix_A(static_matrix<U, V> & A);

    // void fill_column_info_names() {
    //     for (unsigned j = 0; j < m_A.column_count(); j++) {
    //         column_info<mpq> t;
    //         m_column_infos.push_back(t);
    //         if (j < m_map_from_var_index_to_name_left_side_pair.size()) {
    //             m_column_infos.back().set_name(m_map_from_var_index_to_name_left_side_pair[j]);
    //         } else {
    //             string pref("_s_");
    //             m_column_infos.back().set_name(pref + T_to_string(j));
    //         }
    //         m_column_names
    //     }
    // }
    void set_upper_bound_for_column_info(lar_normalized_constraint * norm_constr);

    bool try_to_set_fixed(column_info<mpq> & ci);

    void set_low_bound_for_column_info(lar_normalized_constraint * norm_constr);

    void update_column_info_of_normalized_constraint(lar_normalized_constraint & norm_constr);

    column_type get_column_type(column_info<mpq> & ci);

    void fill_column_names();

    void fill_column_types();

    template <typename V>
    void fill_bounds_for_core_solver(std::vector<V> & lb, std::vector<V> & ub);


    template <typename V>
    void resize_x_and_init_with_zeros(std::vector<V> & x, unsigned n);

    template <typename V>
    void resize_x_and_init_with_signature(std::vector<V> & x, std::vector<V> & low_bound,
                                          std::vector<V> & upper_bound, const lar_solution_signature & signature);

    template <typename V> V get_column_val(std::vector<V> & low_bound, std::vector<V> & upper_bound, non_basic_column_value_position pos_type, unsigned j);

public:
    ~lar_solver();

    lp_settings & settings() { return m_settings;}

    void clear() {lean_assert(false); // not implemented
    }

    lar_solver() : m_mpq_core_solver(m_x,
                                     m_column_types,
                                     m_low_bounds,
                                     m_upper_bounds,
                                     m_basis,
                                     m_A,
                                     m_settings,
                                     m_column_names,
                                     m_right_side_vector,
                                     m_costs) {
    }


    var_index add_var(std::string s);

    constraint_index add_constraint(const buffer<pair<mpq, var_index>>& left_side, lconstraint_kind kind_par, mpq right_side_par);

    bool is_infeasible(const column_info<mpq> & ci) {
        return ci.low_bound_is_set() && ci.upper_bound_is_set() && ci.get_low_bound() > ci.get_upper_bound();
    }

    bool all_constraints_hold();

    bool constraint_holds(const lar_constraint & constr, std::unordered_map<var_index, mpq> & var_map);

    lp_status get_status() const { return m_status;}

    void solve_with_core_solver();

    bool the_relations_are_of_same_type(const buffer<pair<mpq, unsigned>> & evidence, lconstraint_kind & the_kind_of_sum);

    void register_in_map(std::unordered_map<var_index, mpq> & coeffs, lar_constraint & cn, const mpq & a);
    bool the_left_sides_sum_to_zero(const buffer<pair<mpq, unsigned>> & evidence);

    bool the_righ_sides_do_not_sum_to_zero(const buffer<pair<mpq, unsigned>> & evidence);

    bool the_evidence_is_correct();

    void update_column_info_of_normalized_constraints();

    template <typename V>
    void init_right_sides_with_zeros(std::vector<V> & rs);

    mpq sum_of_right_sides_of_evidence(const buffer<pair<mpq, unsigned>> & evidence);
    void prepare_independently_of_numeric_type();

    template <typename U, typename V>
    void prepare_core_solver_fields(static_matrix<U, V> & A, std::vector<V> & x,
                                    std::vector<V> & right_side_vector,
                                    std::vector<V> & low_bound,
                                    std::vector<V> & upper_bound);

    template <typename U, typename V>
    void prepare_core_solver_fields_with_signature(static_matrix<U, V> & A, std::vector<V> & x,
                                                   std::vector<V> & right_side_vector,
                                                   std::vector<V> & low_bound,
                                                   std::vector<V> & upper_bound, const lar_solution_signature & signature);

    void find_solution_signature_with_doubles(lar_solution_signature & signature);

    template <typename U, typename V>
    void extract_signature_from_lp_core_solver(lp_primal_core_solver<U, V> & core_solver, lar_solution_signature & signature);

    void solve_on_signature(const lar_solution_signature & signature);

    void solve();

    lp_status check();
    void get_infeasibility_evidence(buffer<pair<mpq, constraint_index>> & evidence);

    void get_infeasibility_evidence_for_inf_sign(buffer<pair<mpq, constraint_index>> & evidence,
                                                 const std::vector<pair<mpq, unsigned>> & inf_row,
                                                 int inf_sign);


    mpq find_delta_for_strict_bounds();

    void restrict_delta_on_low_bound_column(mpq& delta, unsigned j);
    void restrict_delta_on_upper_bound(mpq& delta, unsigned j);

    void get_model(std::unordered_map<var_index, mpq> & variable_values);

    std::string get_variable_name(var_index vi);

    void print_constraint(constraint_index ci, std::ostream & out);

    void print_canonic_left_side(const canonic_left_side & c, std::ostream & out);

    void print_left_side_of_constraint(const lar_base_constraint * c, std::ostream & out);

    numeric_pair<mpq> get_infeasibility_from_core_solver(std::unordered_map<std::string, mpq> & solution);

    void print_info_on_column(unsigned j, std::ostream & out);

    mpq get_infeasibility_of_solution(std::unordered_map<std::string, mpq> & solution);

    mpq get_infeasibility_of_constraint(const lar_normalized_constraint & norm_constr, std::unordered_map<std::string, mpq> & solution);

    mpq get_canonic_left_side_val(canonic_left_side * ls, std::unordered_map<std::string, mpq> & solution);

    mpq get_left_side_val(const lar_constraint &  cns, const std::unordered_map<var_index, mpq> & var_map);

    void print_constraint(const lar_base_constraint * c, std::ostream & out);
    unsigned get_total_iterations() const { return m_mpq_core_solver.m_total_iterations; }
};
}
