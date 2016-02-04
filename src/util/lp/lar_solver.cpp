/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <string>
#include <algorithm>
#include <vector>
#include "util/lp/lar_solver.h"
namespace lean {
double conversion_helper <double>::get_low_bound(const column_info<mpq> & ci) {
    if (!ci.low_bound_is_strict())
        return ci.get_low_bound().get_double();
    double eps = 0.00001;
    if (!ci.upper_bound_is_set())
        return ci.get_low_bound().get_double() + eps;
    eps = std::min((ci.get_upper_bound() - ci.get_low_bound()).get_double()/1000, eps);
    return ci.get_low_bound().get_double() + eps;
}

double conversion_helper <double>::get_upper_bound(const column_info<mpq> & ci) {
    if (!ci.upper_bound_is_strict())
        return ci.get_upper_bound().get_double();
    double eps = 0.00001;
    if (!ci.low_bound_is_set())
        return ci.get_upper_bound().get_double() - eps;
    eps = std::min((ci.get_upper_bound() - ci.get_low_bound()).get_double()/1000, eps);
    return ci.get_upper_bound().get_double() - eps;
}

canonic_left_side * lar_solver::create_or_fetch_existing_left_side(const buffer<pair<mpq, var_index>>& left_side_par) {
    auto left_side = new canonic_left_side(left_side_par);
    lean_assert(left_side->size() > 0);
    auto it = m_canonic_left_sides.find(left_side);
    if (it == m_canonic_left_sides.end()) {
        m_canonic_left_sides.insert(left_side);
    } else {
        delete left_side;
        left_side = *it;
    }
    return left_side;
}


bool lar_solver::var_is_fixed(unsigned j) {
    auto it = m_map_from_var_index_to_left_side.find(j);
    lean_assert(it != m_map_from_var_index_to_left_side.end());
    return it->second->m_column_info.is_fixed();
}

mpq lar_solver::find_ratio(canonic_left_side * ls, const lar_constraint & constraint) {
    lean_assert(ls->m_coeffs.size() > 0);
    auto first_pair = ls->m_coeffs[0];
    lean_assert(first_pair.first == numeric_traits<mpq>::one());
    var_index i = first_pair.second;
    auto it = constraint.m_left_side.find(i);
    lean_assert(it != constraint.m_left_side.end());
    return it->second;
}

void lar_solver::add_canonic_left_side_for_var(var_index i, std::string var_name) {
    buffer<pair<mpq, var_index>> b;
    b.push_back(std::make_pair(numeric_traits<mpq>::one(), i));
    auto can_ls = new canonic_left_side(b);
    can_ls->set_name(var_name);

    lean_assert(m_canonic_left_sides.find(can_ls) == m_canonic_left_sides.end());
    m_canonic_left_sides.insert(can_ls);
    m_map_from_var_index_to_left_side[i] = can_ls;
}

void lar_solver::map_left_side_to_column_of_A(canonic_left_side*  left_side, unsigned & j) {
    lean_assert(m_column_indices_to_canonic_left_sides.find(j) == m_column_indices_to_canonic_left_sides.end());
    left_side->m_column_index = j; // assigning this index does not change the hash of canonic_left_side
    if (left_side->size() > 1) { // if size is one we will not create a row for this left side
        left_side->m_row_index = m_basis.size();
        m_basis.push_back(j); // j will be a basis column, so we put it into the basis as well
    }
    m_column_indices_to_canonic_left_sides[j++] = left_side; // pointing from the column to the left side
}


void lar_solver::map_left_sides_to_columns_of_A() {
    unsigned j = 0;
    for (auto it : m_canonic_left_sides)
        map_left_side_to_column_of_A(it, j);
}

bool valid_index(unsigned j) { return static_cast<int>(j) >= 0;}


// this adds a row to A
template <typename U, typename V>
void lar_solver::add_row_to_A(static_matrix<U, V> & A, unsigned i, canonic_left_side * ls) {
    for (auto & t : ls->m_coeffs) {
        var_index vi = t.second;
        canonic_left_side *var_left_side = m_map_from_var_index_to_left_side[vi];
        unsigned column = var_left_side->m_column_index;
        lean_assert(valid_index(column));
        A.set(i, column, convert_struct<U, mpq>::convert(t.first));
    }
    A.set(i, ls->m_column_index, - one_of_type<U>());
}

template <typename U, typename V>
void lar_solver::create_matrix_A(static_matrix<U, V> & A) {
    unsigned n = m_column_indices_to_canonic_left_sides.size();
    unsigned m = m_basis.size();
    A.init_empty_matrix(m, n);
    unsigned i = 0;
    for (auto & t : m_column_indices_to_canonic_left_sides)
        if (valid_index(t.second->m_row_index))
            add_row_to_A(A, i++, t.second);
#ifdef LEAN_DEBUG
    // print_matrix(m_A);
#endif
}

// void lar_solver::fill_column_info_names() {
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
void lar_solver::set_upper_bound_for_column_info(lar_normalized_constraint * norm_constr) {
    const mpq & v = norm_constr->m_right_side;
    canonic_left_side * ls = norm_constr->m_canonic_left_side;
    column_info<mpq> & ci = ls->m_column_info;
    lean_assert(norm_constr->m_kind == LE || norm_constr->m_kind == LT || norm_constr->m_kind == EQ);
    bool strict = norm_constr->m_kind == LT;
    if (!ci.upper_bound_is_set()) {
        ls->m_upper_bound_witness = norm_constr;
        ci.set_upper_bound(v);
        ci.set_upper_bound_strict(strict);
    } else if (ci.get_upper_bound() > v) {
        ci.set_upper_bound(v);
        ls->m_upper_bound_witness = norm_constr;
        ci.set_upper_bound_strict(strict);
    }
    if (ci.is_infeasible()) {
        m_status= INFEASIBLE;
        m_infeasible_canonic_left_side = ls;
        return;
    }
    try_to_set_fixed(ci);
}

bool lar_solver::try_to_set_fixed(column_info<mpq> & ci) {
    if (ci.upper_bound_is_set() && ci.low_bound_is_set() && ci.get_upper_bound() == ci.get_low_bound() && !ci.is_fixed()) {
        ci.set_fixed_value(ci.get_upper_bound());
        return true;
    }
    return false;
}

void lar_solver::set_low_bound_for_column_info(lar_normalized_constraint * norm_constr) {
    const mpq & v = norm_constr->m_right_side;
    canonic_left_side * ls = norm_constr->m_canonic_left_side;
    column_info<mpq> & ci = ls->m_column_info;
    lean_assert(norm_constr->m_kind == GE || norm_constr->m_kind == GT || norm_constr->m_kind == EQ);
    bool strict = norm_constr->m_kind == GT;
    if (!ci.low_bound_is_set()) {
        ci.set_low_bound(v);
        ls->m_low_bound_witness = norm_constr;
        ci.set_low_bound_strict(strict);
    } else if (ci.get_low_bound() < v) {
        ci.set_low_bound(v);
        ls->m_low_bound_witness = norm_constr;
        ci.set_low_bound_strict(strict);
    }

    if (ci.is_infeasible()) {
        m_status= INFEASIBLE;
        m_infeasible_canonic_left_side = ls;
        return;
    }

    try_to_set_fixed(ci);
}

void lar_solver::update_column_info_of_normalized_constraint(lar_normalized_constraint & norm_constr) {
    lean_assert(norm_constr.size() > 0);
    switch (norm_constr.m_kind) {
    case LE:
    case LT:
        set_upper_bound_for_column_info(&norm_constr);
        break;
    case GE:
    case GT:
        set_low_bound_for_column_info(&norm_constr);
        break;

    case EQ:
        {
            set_upper_bound_for_column_info(&norm_constr);
            set_low_bound_for_column_info(&norm_constr);
        }
        break;
    default:
        lean_unreachable();
    }
}

column_type lar_solver::get_column_type(column_info<mpq> & ci) {
    auto ret = ci.get_column_type_no_flipping();
    if (ret == boxed) { // changing boxed to fixed because of the no span
        if (ci.get_low_bound() == ci.get_upper_bound())
            ret = fixed;
    }
    return ret;
}

void lar_solver::fill_column_names() {
    m_column_names.clear();
    for (auto t : m_canonic_left_sides) {
        auto & ci = t->m_column_info;
        unsigned j = t->m_column_index;
        lean_assert(valid_index(j));
        std::string name = ci.get_name();
        if (name.size() == 0)
            name = std::string("_s") + T_to_string(j);
        m_column_names[j] = name;
    }
}

void lar_solver::fill_column_types() {
    m_column_types.clear();
    m_column_types.resize(m_canonic_left_sides.size(), free_column);
    for (auto t : m_canonic_left_sides) {
        auto & ci = t->m_column_info;
        unsigned j = t->m_column_index;
        lean_assert(valid_index(j));
        m_column_types[j] = get_column_type(ci);
    }
}

template <typename V>
void lar_solver::fill_bounds_for_core_solver(std::vector<V> & lb, std::vector<V> & ub) {
    unsigned n = m_canonic_left_sides.size(); // this is the number of columns
    lb.resize(n);
    ub.resize(n);
    for (auto t : m_canonic_left_sides) {
        auto & ci = t->m_column_info;
        unsigned j = t->m_column_index;
        lean_assert(valid_index(j));
        if (ci.low_bound_is_set())
            lb[j] = conversion_helper<V>::get_low_bound(ci);
        if (ci.upper_bound_is_set())
            ub[j] = conversion_helper<V>::get_upper_bound(ci);
    }
}


template <typename V>
void lar_solver::resize_x_and_init_with_zeros(std::vector<V> & x, unsigned n) {
    x.clear();
    x.resize(n, zero_of_type<V>()); // init with zeroes
}

template <typename V>
void lar_solver::resize_x_and_init_with_signature(std::vector<V> & x, std::vector<V> & low_bound,
                                                  std::vector<V> & upper_bound, const lar_solution_signature & signature) {
    x.clear();
    x.resize(low_bound.size());
    for (auto & t : signature.non_basic_column_value_positions) {
        x[t.first] = get_column_val(low_bound, upper_bound, t.second, t.first);
    }
}

template <typename V> V lar_solver::get_column_val(std::vector<V> & low_bound, std::vector<V> & upper_bound, non_basic_column_value_position pos_type, unsigned j) {
    switch (pos_type) {
    case at_low_bound: return low_bound[j];
    case at_fixed:
    case at_upper_bound: return upper_bound[j];
    case free_of_bounds: return zero_of_type<V>();
    default:
        lean_unreachable();
    }
}

lar_solver::~lar_solver() {
    std::vector<canonic_left_side*> to_delete;
    for (auto it : m_canonic_left_sides)
        to_delete.push_back(it);
    for (auto t : to_delete)
        delete t;
}




var_index lar_solver::add_var(std::string s) {
    auto got = m_var_names_to_var_index.find(s);
    if (got != m_var_names_to_var_index.end()) return got->second;

    var_index i = m_available_var_index++;
    m_var_names_to_var_index[s] = i;
    add_canonic_left_side_for_var(i, s);
    return i;
}

constraint_index lar_solver::add_constraint(const buffer<pair<mpq, var_index>>& left_side, lconstraint_kind kind_par, mpq right_side_par) {
    lean_assert(left_side.size());
    constraint_index i = m_available_constr_index++;
    lar_constraint original_constr(left_side, kind_par, right_side_par, i);
    canonic_left_side * ls = create_or_fetch_existing_left_side(left_side);
    mpq ratio = find_ratio(ls, original_constr);
    auto kind = ratio.is_neg()? flip_kind(kind_par): kind_par;
    mpq right_side = right_side_par / ratio;
    lar_normalized_constraint normalized_constraint(ls, ratio, kind, right_side, original_constr);
    m_normalized_constraints[i] = normalized_constraint;
    return i;
}

bool lar_solver::all_constraints_hold() {
    std::unordered_map<var_index, mpq> var_map;
    get_model(var_map);
    for ( auto & it : m_normalized_constraints )
        if (!constraint_holds(it.second.m_origin_constraint, var_map)) {
            return false;
        }
    return true;
}

bool lar_solver::constraint_holds(const lar_constraint & constr, std::unordered_map<var_index, mpq> & var_map) {
    mpq left_side_val = get_left_side_val(constr, var_map);
    switch (constr.m_kind) {
    case LE: return left_side_val <= constr.m_right_side;
    case LT: return left_side_val <= constr.m_right_side;
    case GE: return left_side_val >= constr.m_right_side;
    case GT: return left_side_val >= constr.m_right_side;
    case EQ: return left_side_val == constr.m_right_side;
    default:
        lean_unreachable();
    }
}

void lar_solver::solve_with_core_solver() {
    m_mpq_core_solver.solve();
    m_status = m_mpq_core_solver.m_status;
    lean_assert(m_status != OPTIMAL  || all_constraints_hold());
#ifdef LEAN_DEBUG
    lean_assert(!settings().row_feasibility || m_status != INFEASIBLE || the_evidence_is_correct());
#endif
}

bool lar_solver::the_relations_are_of_same_type(const buffer<pair<mpq, unsigned>> & evidence, lconstraint_kind & the_kind_of_sum) {
    unsigned n_of_G = 0, n_of_L = 0;
    bool strict = false;
    for (auto & it : evidence) {
        mpq coeff = it.first;
        constraint_index con_ind = it.second;
        lar_constraint & constr = m_normalized_constraints[con_ind].m_origin_constraint;

        lconstraint_kind kind = coeff.is_pos()?  constr.m_kind: flip_kind(constr.m_kind);
        if (kind == GT || kind == LT)
            strict = true;
        if (kind == GE || kind == GT) n_of_G++;
        else if (kind == LE || kind == LT) n_of_L++;
    }
    the_kind_of_sum = n_of_G? GE : (n_of_L? LE : EQ);
    if (strict)
        the_kind_of_sum = static_cast<lconstraint_kind>((static_cast<int>(the_kind_of_sum)/2));

    return n_of_G == 0 || n_of_L == 0;
}

void lar_solver::register_in_map(std::unordered_map<var_index, mpq> & coeffs, lar_constraint & cn, const mpq & a) {
    for (auto & it : cn.m_left_side) {
        unsigned j = it.first;
        auto p = coeffs.find(j);
        if (p == coeffs.end()) coeffs[j] = it.second * a;
        else p->second += it.second * a;
    }
}
bool lar_solver::the_left_sides_sum_to_zero(const buffer<pair<mpq, unsigned>> & evidence) {
    std::unordered_map<var_index, mpq> coeff_map;
    for (auto & it : evidence) {
        mpq coeff = it.first;
        constraint_index con_ind = it.second;
        lar_constraint & constr = m_normalized_constraints[con_ind].m_origin_constraint;
        register_in_map(coeff_map, constr, coeff);
    }
    for (auto & it : coeff_map) {
        if (!numeric_traits<mpq>::is_zero(it.second)) return false;
    }
    return true;
}

bool lar_solver::the_righ_sides_do_not_sum_to_zero(const buffer<pair<mpq, unsigned>> & evidence) {
    mpq ret = numeric_traits<mpq>::zero();
    for (auto & it : evidence) {
        mpq coeff = it.first;
        constraint_index con_ind = it.second;
        lar_constraint & constr = m_normalized_constraints[con_ind].m_origin_constraint;
        ret += constr.m_right_side * coeff;
    }
    return !numeric_traits<mpq>::is_zero(ret);
}
#ifdef LEAN_DEBUG
bool lar_solver::the_evidence_is_correct() {
    buffer<pair<mpq, unsigned>> evidence;
    get_infeasibility_evidence(evidence);
    lconstraint_kind kind;
    lean_assert(the_relations_are_of_same_type(evidence, kind));
    lean_assert(the_left_sides_sum_to_zero(evidence));
    mpq rs = sum_of_right_sides_of_evidence(evidence);
    switch (kind) {
    case LE: lean_assert(rs < zero_of_type<mpq>());
        break;
    case LT: lean_assert(rs <= zero_of_type<mpq>());
        break;
    case GE: lean_assert(rs > zero_of_type<mpq>());
        break;
    case GT: lean_assert(rs >= zero_of_type<mpq>());
        break;
    case EQ: lean_assert(rs != zero_of_type<mpq>());
        break;
    default:
        lean_assert(false);
        return false;
    }
    return true;
}
#endif
void lar_solver::update_column_info_of_normalized_constraints() {
    for (auto & it : m_normalized_constraints)
        update_column_info_of_normalized_constraint(it.second);
}

template <typename V>
void lar_solver::init_right_sides_with_zeros(std::vector<V> & rs) {
    rs.clear();
    rs.resize(m_basis.size(), zero_of_type<V>());
}

mpq lar_solver::sum_of_right_sides_of_evidence(const buffer<pair<mpq, unsigned>> & evidence) {
    mpq ret = numeric_traits<mpq>::zero();
    for (auto & it : evidence) {
        mpq coeff = it.first;
        constraint_index con_ind = it.second;
        lar_constraint & constr = m_normalized_constraints[con_ind].m_origin_constraint;
        ret += constr.m_right_side * coeff;
    }
    return ret;
}
void lar_solver::prepare_independently_of_numeric_type() {
    update_column_info_of_normalized_constraints();
    map_left_sides_to_columns_of_A();
    fill_column_names();
    fill_column_types();
}

template <typename U, typename V>
void lar_solver::prepare_core_solver_fields(static_matrix<U, V> & A, std::vector<V> & x,
                                            std::vector<V> & right_side_vector,
                                            std::vector<V> & low_bound,
                                            std::vector<V> & upper_bound) {
    create_matrix_A(A);
    fill_bounds_for_core_solver(low_bound, upper_bound);
    if (m_status == INFEASIBLE) {
        lean_assert(false); // not implemented
    }
    init_right_sides_with_zeros(right_side_vector);
    resize_x_and_init_with_zeros(x, A.column_count());
    lean_assert(m_basis.size() == A.row_count());
}

template <typename U, typename V>
void lar_solver::prepare_core_solver_fields_with_signature(static_matrix<U, V> & A, std::vector<V> & x,
                                                           std::vector<V> & right_side_vector,
                                                           std::vector<V> & low_bound,
                                                           std::vector<V> & upper_bound, const lar_solution_signature & signature) {
    create_matrix_A(A);
    fill_bounds_for_core_solver(low_bound, upper_bound);
    if (m_status == INFEASIBLE) {
        lean_assert(false); // not implemented
    }
    init_right_sides_with_zeros(right_side_vector);
    resize_x_and_init_with_signature(x, low_bound, upper_bound, signature);
}

void lar_solver::find_solution_signature_with_doubles(lar_solution_signature & signature) {
    static_matrix<double, double> A;
    std::vector<double> x, right_side_vector, low_bounds, upper_bounds;
    prepare_core_solver_fields<double, double>(A, x, right_side_vector, low_bounds, upper_bounds);
    std::vector<double> column_scale_vector;
    scaler<double, double > scaler(right_side_vector, A, m_settings.scaling_minimum, m_settings.scaling_maximum, column_scale_vector, this->m_settings);
    if (!scaler.scale()) {
        // the scale did not succeed, unscaling
        A.clear();
        create_matrix_A(A);
        for (auto & s : column_scale_vector)
            s = one_of_type<double>();
    }
    std::vector<double> costs(A.column_count());
    auto core_solver = lp_primal_core_solver<double, double>(A,
                                                             right_side_vector,
                                                             x,
                                                             m_basis,
                                                             costs,
                                                             m_column_types,
                                                             low_bounds,
                                                             upper_bounds,
                                                             m_settings,
                                                             m_column_names);
    core_solver.find_feasible_solution();
    extract_signature_from_lp_core_solver(core_solver, signature);
}

template <typename U, typename V>
void lar_solver::extract_signature_from_lp_core_solver(lp_primal_core_solver<U, V> & core_solver, lar_solution_signature & signature) {
    for (auto j : core_solver.m_non_basic_columns)
        signature.non_basic_column_value_positions[j] = core_solver.get_non_basic_column_value_position(j);
}

void lar_solver::solve_on_signature(const lar_solution_signature & signature) {
    prepare_core_solver_fields_with_signature(m_A, m_x, m_right_side_vector, m_low_bounds, m_upper_bounds, signature);
    solve_with_core_solver();
}

void lar_solver::solve() {
    prepare_independently_of_numeric_type();
    if (m_settings.use_double_solver_for_lar) {
        lar_solution_signature solution_signature;
        find_solution_signature_with_doubles(solution_signature);
        // here the basis that is kept in m_basis is the same that was used in the double solver
        solve_on_signature(solution_signature);
        return;
    }
    prepare_core_solver_fields(m_A, m_x, m_right_side_vector, m_low_bounds, m_upper_bounds);
    solve_with_core_solver();
}

lp_status lar_solver::check() {
    // for the time being just call solve()
    solve();
    return m_status;
}
void lar_solver::get_infeasibility_evidence(buffer<pair<mpq, constraint_index>> & evidence){
    if (!m_mpq_core_solver.get_infeasible_row_sign()) {
        return;
    }
    // the infeasibility sign
    int inf_sign;
    auto inf_row =  m_mpq_core_solver.get_infeasibility_info(inf_sign);
    lean_assert(inf_sign != 0);
    get_infeasibility_evidence_for_inf_sign(evidence, inf_row, inf_sign);
}

void lar_solver::get_infeasibility_evidence_for_inf_sign(buffer<pair<mpq, constraint_index>> & evidence,
                                                         const std::vector<pair<mpq, unsigned>> & inf_row,
                                                         int inf_sign) {
    for (auto & it : inf_row) {
        mpq coeff = it.first;
        unsigned j = it.second;
        canonic_left_side * ls = m_column_indices_to_canonic_left_sides[j];
        int adj_sign = coeff.is_pos() ? inf_sign : -inf_sign;

        lar_normalized_constraint * bound_constr = adj_sign < 0? ls->m_upper_bound_witness : ls->m_low_bound_witness;
        lean_assert(bound_constr != nullptr);
        evidence.push_back(std::make_pair(coeff / bound_constr->m_ratio_to_original, bound_constr->m_index));
    }
}


mpq lar_solver::find_delta_for_strict_bounds() {
    mpq delta = numeric_traits<mpq>::one();
    for (auto t : m_canonic_left_sides) {
        auto & ci = t->m_column_info;
        unsigned j = t->m_column_index;
        lean_assert (valid_index(j));
        if (ci.low_bound_is_set())
            restrict_delta_on_low_bound_column(delta, j);
        if (ci.upper_bound_is_set())
            restrict_delta_on_upper_bound(delta, j);
    }
    return delta;
}

void lar_solver::restrict_delta_on_low_bound_column(mpq& delta, unsigned j) {
    numeric_pair<mpq> & x = m_x[j];
    numeric_pair<mpq> & l = m_low_bounds[j];
    mpq & xx = x.x;
    mpq & xy = x.y;
    mpq & lx = l.x;
    if (xx == lx) {
        lean_assert(xy >= numeric_traits<mpq>::zero());
    } else {
        lean_assert(xx >= lx); // we need lx <= xx + delta*xy, or delta*xy >= lx - xx, or - delta*xy <= xx - ls.
        // The right part is not negative. The delta is positive. If xy >= 0 we have the ineqality
        // otherwise we need to have delta not greater than - (xx - lx)/xy. We use the 2 coefficient to handle the strict case
        if (xy >= zero_of_type<mpq>()) return;
        delta = std::min(delta, (lx - xx)/ (2 * xy)); // we need to have delta * xy < xx - lx for the strict case
    }
}
void lar_solver::restrict_delta_on_upper_bound(mpq& delta, unsigned j) {
    numeric_pair<mpq> & x = m_x[j];
    numeric_pair<mpq> & u = m_upper_bounds[j];
    mpq & xx = x.x;
    mpq & xy = x.y;
    mpq & ux = u.x;
    if (xx == ux) {
        lean_assert(xy <= numeric_traits<mpq>::zero());
    } else {
        lean_assert(xx < ux);
        if (xy <= zero_of_type<mpq>()) return;
        delta = std::min(delta, (ux - xx)/ (2 * xy)); // we need to have delta * xy < ux - xx, for the strict case
    }
}

void lar_solver::get_model(std::unordered_map<var_index, mpq> & variable_values){
    lean_assert(m_status == OPTIMAL);
    mpq delta = find_delta_for_strict_bounds();
    for (auto & it : m_map_from_var_index_to_left_side) {
        numeric_pair<mpq> & rp = m_x[it.second->m_column_index];
        variable_values[it.first] =  rp.x + delta * rp.y;
    }
}

std::string lar_solver::get_variable_name(var_index vi) {
    if (m_map_from_var_index_to_left_side.size() <= vi) {
        std::string s = "variable " + T_to_string(vi) + " is not found";
        return s;
    }
    return m_map_from_var_index_to_left_side[vi]->m_column_info.get_name();
}

// ********** print region start
void lar_solver::print_constraint(constraint_index ci, std::ostream & out) {
    if (m_normalized_constraints.size() <= ci) {
        std::string s = "constraint " + T_to_string(ci) + " is not found";
        out << s << std::endl;
        return;
    }

    print_constraint(&m_normalized_constraints[ci], out);
}

void lar_solver::print_canonic_left_side(const canonic_left_side & c, std::ostream & out) {
    bool first = true;
    for (auto it : c.m_coeffs) {
        auto val = it.first;
        if (first) {
            first = false;
        } else {
            if (val.is_pos()) {
                out << " + ";
            } else {
                out << " - ";
                val = -val;
            }
        }
        if (val != numeric_traits<mpq>::one())
            out << T_to_string(val);
        out << m_map_from_var_index_to_left_side[it.second]->m_column_info.get_name();
    }
}

void lar_solver::print_left_side_of_constraint(const lar_base_constraint * c, std::ostream & out) {
    bool first = true;
    for (auto it : c->get_left_side_coefficients()) {
        auto val = it.first;
        if (numeric_traits<mpq>::is_zero(val)) continue;
        if (first) {
            first = false;
        } else {
            if (val.is_pos()) {
                out << " + ";
            } else {
                out << " - ";
                val = -val;
            }
        }

        if (val != numeric_traits<mpq>::one())
            out << val;
        out << m_map_from_var_index_to_left_side[it.second]->m_column_info.get_name();
    }
}

void lar_solver::print_info_on_column(unsigned j, std::ostream & out) {
    for (auto ls : m_canonic_left_sides) {
        if (static_cast<unsigned>(ls->m_column_index) == j) {
            auto & ci = ls->m_column_info;
            if (ci.low_bound_is_set()) {
                out << "l = " << ci.get_low_bound();
            }
            if (ci.upper_bound_is_set()) {
                out << "u = " << ci.get_upper_bound();
            }
            out << std::endl;
            m_mpq_core_solver.print_column_info(j, out);
        }
    }
}

mpq lar_solver::get_infeasibility_of_solution(std::unordered_map<std::string, mpq> & solution) {
    mpq ret = numeric_traits<mpq>::zero();
    for (auto it : m_normalized_constraints) {
        ret += get_infeasibility_of_constraint(it.second, solution);
    }
    return ret;
}

mpq lar_solver::get_infeasibility_of_constraint(const lar_normalized_constraint & norm_constr, std::unordered_map<std::string, mpq> & solution) {
    auto kind = norm_constr.m_kind;
    mpq left_side_val = get_canonic_left_side_val(norm_constr.m_canonic_left_side, solution);

    switch (kind) {
    case LT:
    case LE: return std::max(left_side_val - norm_constr.m_right_side, numeric_traits<mpq>::zero());
    case GT:
    case GE: return std::max(- (left_side_val - norm_constr.m_right_side), numeric_traits<mpq>::zero());

    case EQ:
        return abs(left_side_val - norm_constr.m_right_side);

    default:
        lean_unreachable();
    }
}

mpq lar_solver::get_canonic_left_side_val(canonic_left_side * ls, std::unordered_map<std::string, mpq> & solution) {
    mpq ret = numeric_traits<mpq>::zero();
    for (auto it : ls->m_coeffs) {
        var_index j = it.second;
        auto vi = m_map_from_var_index_to_left_side.find(j);
        lean_assert(vi != m_map_from_var_index_to_left_side.end());
        canonic_left_side * var_ls = vi->second;
        std::string s = var_ls->m_column_info.get_name();
        auto t = solution.find(s);
        lean_assert(t != solution.end());
        ret += it.first * (t->second);
    }
    return ret;
}

mpq lar_solver::get_left_side_val(const lar_constraint &  cns, const std::unordered_map<var_index, mpq> & var_map) {
    mpq ret = numeric_traits<mpq>::zero();
    for (auto it : cns.m_left_side) {
        var_index j = it.first;
        auto vi = var_map.find(j);
        lean_assert(vi != var_map.end());
        ret += it.second * vi->second;
    }
    return ret;
}

void lar_solver::print_constraint(const lar_base_constraint * c, std::ostream & out) {
    print_left_side_of_constraint(c, out);
    out <<" " << lconstraint_kind_string(c->m_kind) << " " << c->m_right_side;
}
}

