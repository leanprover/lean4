/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <string>
#include <vector>
#include "util/lp/lar_core_solver.h"
namespace lean {
template <typename T, typename X>
lar_core_solver<T, X>::lar_core_solver(std::vector<X> & x, std::vector<column_type> & column_types,
                                       std::vector<X> & low_bounds, std::vector<X> & upper_bounds,
                                       std::vector<unsigned> & basis,
                                       static_matrix<T, X> & A,
                                       lp_settings & settings,
                                       std::unordered_map<unsigned, std::string> & column_names,
                                       std::vector<X> & right_side,
                                       std::vector<T> & costs) : // right_side and costs are redundant
    lp_core_solver_base<T, X>(A,
                              right_side,
                              basis,
                              x,
                              costs,
                              settings,
                              column_names,
                              column_types,
                              low_bounds,
                              upper_bounds) {
}

template <typename T, typename X> void lar_core_solver<T, X>::init_costs() {
    lean_assert(this->m_x.size() >= this->m_n);
    lean_assert(this->m_column_type.size() >= this->m_n);
    X inf = m_infeasibility;
    m_infeasibility = zero_of_type<X>();
    for (unsigned j = this->m_n; j--;)
        init_cost_for_column(j);
    if (!(this->m_total_iterations ==0 || inf >= m_infeasibility)) {
        std::cout << "inf was " << T_to_string(inf) << " and now " << T_to_string(m_infeasibility) << std::endl;
        lean_unreachable();
    }
    if (inf == m_infeasibility)
        this->m_iters_with_no_cost_growing++;
}


template <typename T, typename X>    void lar_core_solver<T, X>::init_cost_for_column(unsigned j) {
    // If j is a breakpoint column, then we set the cost zero.
    // When anylyzing an entering column candidate we update the cost of the breakpoints columns to get the left or the right derivative if the infeasibility function
    const X & x = this->m_x[j];
    // set zero cost for each non-basis column
    if (this->m_basis_heading[j] < 0) {
        this->m_costs[j] = numeric_traits<T>::zero();
        return;
    }
    // j is a basis column
    switch (this->m_column_type[j]) {
    case fixed:
    case boxed:
        if (x > this->m_upper_bound_values[j]) {
            this->m_costs[j] = 1;
            m_infeasibility += x - this->m_upper_bound_values[j];
        } else if (x < this->m_low_bound_values[j]) {
            m_infeasibility += this->m_low_bound_values[j] - x;
            this->m_costs[j] = -1;
        } else {
            this->m_costs[j] = numeric_traits<T>::zero();
        }
        break;
    case low_bound:
        if (x < this->m_low_bound_values[j]) {
            this->m_costs[j] = -1;
            m_infeasibility += this->m_low_bound_values[j] - x;
        } else {
            this->m_costs[j] = numeric_traits<T>::zero();
        }
        break;
    case upper_bound:
        if (x > this->m_upper_bound_values[j]) {
            this->m_costs[j] = 1;
            m_infeasibility += x - this->m_upper_bound_values[j];
        } else {
            this->m_costs[j] = numeric_traits<T>::zero();
        }
        break;
    case free_column:
        this->m_costs[j] = numeric_traits<T>::zero();
        break;
    default:
        lean_assert(false);
        break;
    }
}

template <typename T, typename X>    void lar_core_solver<T, X>::init_local() {
    this->m_start_time = get_millisecond_count();
    this->m_m = this->m_A.row_count();
    this->m_n = this->m_A.column_count();
    this->m_pivot_row_of_B_1.resize(this->m_m);
    this->m_pivot_row.resize(this->m_n);
    this->m_b.resize(this->m_m);
    this->m_y.resize(this->m_m);
    this->m_w.resize(this->m_m);
    this->m_d.resize(this->m_n);
    this->m_ed.resize(this->m_m);
    this->m_costs.resize(this->m_n);
    this->m_breakpoint_indices_queue.resize(this->m_n);
    this->m_copy_of_xB.resize(this->m_n);
}

// returns m_sign_of_alpha_r
template <typename T, typename X>    int lar_core_solver<T, X>::column_is_out_of_bounds(unsigned j) {
    switch (this->m_column_type[j]) {
    case fixed:
    case boxed:
        if (this->x_below_low_bound(j)) {
            return -1;
        }
        if (this->x_above_upper_bound(j)) {
            return 1;
        }
        return 0;
    case low_bound:
        if (this->x_below_low_bound(j)) {
            return -1;
        }
        return 0;
    case upper_bound:
        if (this->x_above_upper_bound(j)) {
            return 1;
        }
        return 0;
    default:
        return 0;
        break;
    }
}

template <typename T, typename X>    bool lar_core_solver<T, X>::can_enter_basis_mpq(unsigned j) {
    switch (this->m_column_type[j]) {
    case low_bound:
        lean_assert(this->x_is_at_low_bound(j));
        return this->m_d[j] < numeric_traits<T>::zero();
    case upper_bound:
        lean_assert(this->x_is_at_upper_bound(j));
        return this->m_d[j] > numeric_traits<T>::zero();
    case fixed:
        return false;
    case boxed:
        {
            bool low_bound = this->x_is_at_low_bound(j);
            lean_assert(low_bound || this->x_is_at_upper_bound(j));
            return (low_bound && this->m_d[j] < numeric_traits<T>::zero()) || ((!low_bound) && this->m_d[j] > numeric_traits<T>::zero());
        }
    case free_column:
        return !numeric_traits<T>::is_zero(this->m_d[j]);
    default:
        return false;
    }
    return false;
}


template <typename T, typename X>    void lar_core_solver<T, X>::calculate_pivot_row(unsigned i) {
    this->calculate_pivot_row_of_B_1(i);
    this->calculate_pivot_row_when_pivot_row_of_B1_is_ready();
}

#ifdef LEAN_DEBUG
template <typename T, typename X>    X lar_core_solver<T, X>::get_deb_inf_column(unsigned j) {
    const X & x = this->m_x[j];
    switch (this->m_column_type[j]) {
    case low_bound:
        if (x < this->m_low_bound_values[j])
            return this->m_low_bound_values[j] - x;
        return zero_of_type<X>();
    case upper_bound:
        if (x > this->m_upper_bound_values[j])
            return x - this->m_upper_bound_values[j];
        return zero_of_type<X>();
    case fixed:
    case boxed:
        {
            if (x < this->m_low_bound_values[j])
                return this->m_low_bound_values[j] - x;
            if (x > this->m_upper_bound_values[j])
                return x - this->m_upper_bound_values[j];
            return zero_of_type<X>();
        }
    case free_column:
        {
            return zero_of_type<X>();
        }
    default:
        lean_assert(false);
        return zero_of_type<X>();
    }
}

template <typename T, typename X>    X lar_core_solver<T, X>::get_deb_inf() {
    X ret = zero_of_type<X>();
    for (unsigned j = 0; j < this->m_n; j++) {
        X d = get_deb_inf_column(j);
        ret += d;
    }
    return ret;
}

template <typename T, typename X> bool lar_core_solver<T, X>::debug_profit_delta(unsigned j, const T & delta, std::ostream & out) {
    this->update_x(j, delta);
    bool ret = m_infeasibility > get_deb_inf();
    if (ret) {
        out << "found profit for " << this->column_name(j) << " and delta = " << delta.get_double() << std::endl;
        out << "improvement = " << (m_infeasibility -  get_deb_inf()).get_double() << std::endl;
    }
    return ret;
}

template <typename T, typename X>    bool lar_core_solver<T, X>::debug_profit(unsigned j, std::ostream & out) {
    if (this->m_column_type[j] == fixed) return false;
    T delta = numeric_traits<T>::one() / 10000000;
    delta /= 10000000;
    return debug_profit_delta(j, -delta, out) || debug_profit_delta(j, delta, out);
}
#endif
template <typename T, typename X>    int lar_core_solver<T, X>::choose_column_entering_basis() {
    unsigned offset = my_random() % this->m_non_basic_columns.size();
    unsigned initial_offset_in_non_basis = offset;
    do {
        unsigned j = this->m_non_basic_columns[offset];
        if (can_enter_basis_mpq(j))
            return j;
        offset++;
        if (offset == this->m_non_basic_columns.size()) offset = 0;
    } while (offset != initial_offset_in_non_basis);
    return -1;
}

template <typename T, typename X>    void lar_core_solver<T, X>::one_iteration() {
    this->m_total_iterations++;
    lean_assert(this->m_non_basic_columns.size()  + this->m_basis.size() == this->m_basis_heading.size());
    if (is_zero(m_infeasibility)) {
        this->m_status = OPTIMAL;
        return;
    }
    int entering = choose_column_entering_basis();
    if (entering == -1) {
        decide_on_status_when_cannot_enter();
    } else {
        advance_on_entering(entering);
    }
}


template <typename T, typename X>    void lar_core_solver<T, X>::decide_on_status_when_cannot_enter() {
    if (!is_zero(m_infeasibility))
        this->m_status = INFEASIBLE;
    else
        this->m_status = FEASIBLE;
}

// j is the basic column, x is the value at x[j]
// d is the coefficient before m_entering in the row with j as the basis column
template <typename T, typename X>    void lar_core_solver<T, X>::try_add_breakpoint(unsigned j, const X & x, const T & d, breakpoint_type break_type, const X & break_value) {
    X diff = x - break_value;
    if (is_zero(diff)) {
        switch (break_type) {
        case low_break:
            if (!same_sign_with_entering_delta(d))
                return; // no breakpoint
            break;
        case upper_break:
            if (same_sign_with_entering_delta(d))
                return; // no breakpoint
            break;
        default: break;
        }
        add_breakpoint(j, zero_of_type<X>(), break_type);
        return;
    }
    auto delta_j =  diff / d;
    if (same_sign_with_entering_delta(delta_j))
        add_breakpoint(j, delta_j, break_type);
}


template <typename T, typename X>    void lar_core_solver<T, X>::add_breakpoint(unsigned j, X delta, breakpoint_type type) {
    m_breakpoints.push_back(breakpoint<X>(j, delta, type));
    m_breakpoint_indices_queue.enqueue(m_breakpoint_indices_queue.size(), abs(delta));
}

template <typename T, typename X>    void lar_core_solver<T, X>::try_add_breakpoint_in_row(unsigned i) {
    lean_assert(i < this->m_m);
    const T & d = this->m_ed[i]; // the coefficient before m_entering in the i-th row
    if (d == 0) return; // the change of x[m_entering] will not change the corresponding basis x
    unsigned j = this->m_basis[i];
    const X & x = this->m_x[j];
    switch (this->m_column_type[j]) {
    case fixed:
        try_add_breakpoint(j, x, d, fixed_break, this->m_low_bound_values[j]);
        break;
    case boxed:
        try_add_breakpoint(j, x, d, low_break, this->m_low_bound_values[j]);
        try_add_breakpoint(j, x, d, upper_break, this->m_upper_bound_values[j]);
        break;
    case low_bound:
        try_add_breakpoint(j, x, d, low_break, this->m_low_bound_values[j]);
        break;
    case upper_bound:
        try_add_breakpoint(j, x, d, upper_break, this->m_upper_bound_values[j]);
        break;
    case free_column:
        break;
    default:
        lean_assert(false);
        break;
    }
}

template <typename T, typename X> std::string lar_core_solver<T, X>::break_type_to_string(breakpoint_type type) {
    switch (type){
    case low_break: return "low_break";
    case upper_break: return "upper_break";
    case fixed_break: return "fixed_break";
    default:
        lean_assert(false);
        break;
    }
    return "type is not found";
}

template <typename T, typename X> void lar_core_solver<T, X>::print_breakpoint(const breakpoint<X> * b, std::ostream & out) {
    out << "(" << this->column_name(b->m_j) << "," << break_type_to_string(b->m_type) << "," << T_to_string(b->m_delta) << ")" << std::endl;
    print_bound_info_and_x(b->m_j);
}

template <typename T, typename X> void lar_core_solver<T, X>::print_bound_info_and_x(unsigned j, std::ostream & out) {
    out << "type of " << this->column_name(j) << " is " << column_type_to_string(this->m_column_type[j]) << std::endl;
    out << "x[" << this->column_name(j) << "] = " << this->m_x[j] << std::endl;
    switch (this->m_column_type[j]) {
    case fixed:
    case boxed:
        out << "[" << this->m_low_bound_values[j] << "," << this->m_upper_bound_values[j] << "]" << std::endl;
        break;
    case low_bound:
        out << "[" << this->m_low_bound_values[j] << ", inf" << std::endl;
        break;
    case upper_bound:
        out << "inf ," << this->m_upper_bound_values[j] << "]" << std::endl;
        break;
    case free_column:
        out << "inf, inf" << std::endl;
        break;
    default:
        lean_assert(false);
        break;
    }
}

template <typename T, typename X>    void lar_core_solver<T, X>::clear_breakpoints() {
    m_breakpoints.clear();
    m_breakpoint_indices_queue.clear();
}

template <typename T, typename X>    void lar_core_solver<T, X>::fill_breakpoints_array(unsigned entering) {
    clear_breakpoints();
    for (unsigned i = this->m_m; i--;)
        try_add_breakpoint_in_row(i);

    if (this->m_column_type[entering] == boxed) {
        if (m_sign_of_entering_delta < 0)
            add_breakpoint(entering, - this->bound_span(entering), low_break);
        else
            add_breakpoint(entering, this->bound_span(entering), upper_break);
    }
}

template <typename T, typename X>    void lar_core_solver<T, X>::advance_on_entering(unsigned entering) {
    this->solve_Bd(entering); // prepares the entering column to be like the one of the tableau
    m_sign_of_entering_delta = this->m_d[entering] < zero_of_type<T>() ? 1 : -1;

    fill_breakpoints_array(entering);
    advance_on_sorted_breakpoints(entering);
}

template <typename T, typename X> void lar_core_solver<T, X>::print_cost(std::ostream & out) {
    out << "reduced costs " << std::endl;
    for (unsigned j = 0; j < this->m_n; j++) {
        if (numeric_traits<T>::is_zero(this->m_d[j])) continue;
        out << T_to_string(this->m_d[j]) << this->column_name(j) << " ";
    }
    out << std::endl;
}

template <typename T, typename X> void lar_core_solver<T, X>::update_basis_and_x_with_comparison(unsigned entering, unsigned leaving, X delta) {
    if (entering != leaving)
        this->update_basis_and_x(entering, leaving, delta);
    else
        this->update_x(entering, delta);
}

template <typename T, typename X>    void lar_core_solver<T, X>::advance_on_sorted_breakpoints(unsigned entering) {
    T slope_at_entering = this->m_d[entering];
    breakpoint<X> * last_bp = nullptr;
    while (m_breakpoint_indices_queue.is_empty() == false) {
        unsigned bi = m_breakpoint_indices_queue.dequeue();
        breakpoint<X> *b = &m_breakpoints[bi];
        change_slope_on_breakpoint(entering, b, slope_at_entering);
        last_bp = b;
        if (slope_at_entering * m_sign_of_entering_delta > 0) { // the slope started to increase infeasibility
            break;
        } else {
            if (numeric_traits<T>::is_zero(slope_at_entering) && my_random() % 2 == 0) {
                // it is not cost benefitial to advance the delta more, so just break to increas the randomness
                break;
            }
        }
    }
    update_basis_and_x_with_comparison(entering, last_bp->m_j, last_bp->m_delta);
}

template <typename T, typename X>    void lar_core_solver<T, X>::change_slope_on_breakpoint(unsigned entering, breakpoint<X> * b, T & slope_at_entering) {
    if (b->m_j == entering) {
        lean_assert(b->m_type != fixed_break && (!is_zero(b->m_delta)));
        slope_at_entering += m_sign_of_entering_delta;
        return;
    }

    lean_assert(this->m_basis_heading[b->m_j] >= 0);
    unsigned i_row = this->m_basis_heading[b->m_j];
    const T & d = - this->m_ed[i_row];
    if (numeric_traits<T>::is_zero(d)) return;

    T delta = m_sign_of_entering_delta * abs(d);
    switch (b->m_type) {
    case fixed_break:
        if (is_zero(b->m_delta)) {
            slope_at_entering += delta;
        } else {
            slope_at_entering += 2 * delta;
        }
        break;
    case low_break:
    case upper_break:
        slope_at_entering += delta;
        break;
    default:
        lean_unreachable();
    }
}

template <typename T, typename X>    bool lar_core_solver<T, X>::row_is_infeasible(unsigned row, int & inf_sign) {
    unsigned j = this->m_basis[row];
    inf_sign = get_infeasibility_sign(j);
    return inf_sign != 0;
}

template <typename T, typename X>    bool lar_core_solver<T, X>::row_is_evidence(unsigned row, int & inf_sign) {
    if (!row_is_infeasible(row, inf_sign)) return false;
    calculate_pivot_row(row);
    int entering = choose_entering_column_for_row_inf_strategy(inf_sign);
    if (entering == -1) {
        return true;
    }
    return false;
}

template <typename T, typename X>    bool lar_core_solver<T, X>::find_evidence_row() {
    for (unsigned i = this->m_m; --i;) {
        int inf_sign;
        if (row_is_evidence(i, inf_sign)) {
            fill_evidence(i, inf_sign);
            return true;
        }
    }
    return false;
}


template <typename T, typename X> bool lar_core_solver<T, X>::done() {
    if (this->m_status == OPTIMAL) return true;
    if (this->m_status == INFEASIBLE) {
        if (this->m_settings.row_feasibility == false) {
            if (!find_evidence_row()) {
                this->m_status = FEASIBLE;
                row_feasibility_loop();
            }
        }
        return true;
    }

    if (this->m_iters_with_no_cost_growing >= this->m_settings.max_number_of_iterations_with_no_improvements) {
        this->m_status = ITERATIONS_EXHAUSTED; return true;
    }
    if (this->m_total_iterations >= this->m_settings.max_total_number_of_iterations) {
        this->m_status = ITERATIONS_EXHAUSTED; return true;
    }
    return false;
}

template <typename T, typename X>    void lar_core_solver<T, X>::move_as_many_as_possible_fixed_columns_to_non_basis() {
    unsigned i = 0; // points to basis
    auto& bs = this->m_basis;
    unsigned j = 0; // points to m_column_types
    auto & ct = this->m_column_type;
    std::vector<int> heading(this->m_n, -1);
    for (int i = 0; i < bs.size(); i ++) heading[bs[j]] = i;
    lean_assert(this->m_basis.size() == this->m_m);
    while (i < this->m_m && j < ct.size()) {
        unsigned basis_j = bs[i];
        if (ct[basis_j] != fixed) {i++; continue;}
        do {
            if (heading[j] == -numeric_traits<T>::one() && ct[j] != fixed)
                break;
            j++;
        } while (j < ct.size());
        if (j == ct.size()) break;
        bs[i++] = j++;
    }
}

template <typename T, typename X>    bool lar_core_solver<T, X>::non_basis_columns_are_set_correctly() {
    for (unsigned j : this->m_non_basic_columns) {
        if (!this->x_is_at_bound(j))
            return false;
    }
    return true;
}

template <typename T, typename X>    void lar_core_solver<T, X>::prefix() {
    init_local();
    this->init();
    this->init_basis_heading();
}

template <typename T, typename X>    void lar_core_solver<T, X>::feasibility_loop() {
    while (true) {
        init_costs();
        this->init_reduced_costs_for_one_iteration();
        if (this->print_statistics_with_cost_and_check_that_the_time_is_over(this->m_total_iterations, m_infeasibility)){
            this->m_status = lp_status::TIME_EXHAUSTED;
            return; // this->m_total_iterations;
        }
        one_iteration();
        if (done()) {
            break;
        }
    }
}

template <typename T, typename X>    unsigned lar_core_solver<T, X>::get_number_of_inf_rows() const {
    unsigned r = 0;
    for (unsigned k = this->m_m; --k;) {
        unsigned j = this->m_basis[k];
        if (get_infeasibility_sign(j)) r++;
    }
    return r;
}


template <typename T, typename X>    void lar_core_solver<T, X>::row_feasibility_loop() {
    while (true) {
        if (this->print_statistics_with_iterations_and_check_that_the_time_is_over(this->m_total_iterations++)){
            this->m_status = lp_status::TIME_EXHAUSTED;
            return; // this->m_total_iterations;
        }
        int inf_sign;
        int i = find_infeasible_row(inf_sign);
        if (i == -1) {
            this->m_status = OPTIMAL;
            break;
        }
        advance_on_infeasible_row(i, inf_sign);
        if (done())
            break;
    }
}

template <typename T, typename X>    int lar_core_solver<T, X>::find_infeasible_row(int & inf_sign) {
    unsigned offset = my_random() % this->m_m;
    unsigned initial_offset_in_basis = offset;
    do {
        unsigned j = this->m_basis[offset];
        inf_sign = get_infeasibility_sign(j);
        if (inf_sign)
            return offset;
        if (++offset == this->m_m) offset = 0;
    } while (offset != initial_offset_in_basis);
    return -1;
}

template <typename T, typename X>    int lar_core_solver<T, X>::get_infeasibility_sign(unsigned j) const {
    const auto & x = this->m_x[j];
    switch (this->m_column_type[j]) {
    case fixed:
    case boxed:
        if (x < this->m_low_bound_values[j]) return 1;
        if (x > this->m_upper_bound_values[j]) return -1;
        return 0;
    case low_bound:
        return x < this->m_low_bound_values[j] ? 1 : 0;
    case upper_bound:
        return x > this->m_upper_bound_values[j]? -1 :0;
    default:
        return 0;
    }
}

template <typename T, typename X>    bool lar_core_solver<T, X>::improves_pivot_row_inf(unsigned j, int inf_sign) {
    lean_assert(this->m_basis_heading[j] < 0);
    // we have x[basis[i]] = sum (mj*x[j]), where mj = -m_pivot_row[j]

    switch (this->m_column_type[j]) {
    case fixed:
        return false;
    case boxed:
        {
            lean_assert(this->x_is_at_bound(j));
            int j_sign = - get_sign(this->m_pivot_row[j]) * inf_sign;
            if (this->x_is_at_low_bound(j))
                return j_sign > 0;
            return j_sign < 0;
        }
    case low_bound:
        {
            lean_assert(this->x_is_at_low_bound(j));
            int j_sign = - get_sign(this->m_pivot_row[j]) * inf_sign;
            return j_sign > 0;
        }
    case upper_bound:
        {
            lean_assert(this->x_is_at_upper_bound(j));
            int j_sign = - get_sign(this->m_pivot_row[j]) * inf_sign;
            return j_sign < 0;
        }
        break;
    case free_column: {
        return numeric_traits<T>::is_zero(this->m_pivot_row[j]) == false;
    }
    default:
        lean_unreachable();
    }
}

template <typename T, typename X>    int lar_core_solver<T, X>::choose_entering_column_for_row_inf_strategy(int inf_sign) {
    unsigned offset = my_random() % this->m_non_basic_columns.size();
    unsigned initial_offset_in_non_basis = offset;
    do {
        unsigned j = this->m_non_basic_columns[offset];
        if (improves_pivot_row_inf(j, inf_sign))
            return j;
        if (++offset == this->m_non_basic_columns.size()) offset = 0;
    } while (offset != initial_offset_in_non_basis);
    return -1;
}

template <typename T, typename X>    void lar_core_solver<T, X>::fill_evidence(unsigned row, int inf_sign) {
    m_infeasible_row_sign = inf_sign;
    m_infeasible_row.push_back(std::make_pair(numeric_traits<T>::one(), this->m_basis[row]));
    for (auto j : this->m_non_basic_columns) {
        T aj = this->m_pivot_row[j];
        if (!numeric_traits<T>::is_zero(aj)) {
            m_infeasible_row.push_back(std::make_pair(aj, j));
        }
    }
}


template <typename T, typename X>    void lar_core_solver<T, X>::update_delta_of_entering_and_leaving_candidates(X del, X & delta,
                                                                                                                 std::vector<unsigned> & leaving_candidates,
                                                                                                                 unsigned bj) {
    if (del < delta) {
        leaving_candidates.clear();
        leaving_candidates.push_back(bj);
        delta = del;
    } else if (del == delta) {
        leaving_candidates.push_back(bj);
    }
}

template <typename T, typename X>    void lar_core_solver<T, X>::update_delta_of_entering(int delta_sign, unsigned row, X & delta,
                                                                                          std::vector<unsigned> & leaving_candidates) {
    unsigned bj = this->m_basis[row]; // bj - the basis column for the row
    const T & ed = this->m_ed[row]; // this is the coefficent before x[entering] in the sum representing the basis column of this row taken with minus
    if (numeric_traits<T>::is_zero(ed)) return;
    const X & x = this->m_x[bj]; // the value of the basis column
    // adjusted sign
    int adj_sign = ed < zero_of_type<T>() ? delta_sign : - delta_sign;

    switch (this->m_column_type[bj]) {
    case fixed:
    case boxed:
        if (adj_sign > 0 && x <= this->m_upper_bound_values[bj])
            update_delta_of_entering_and_leaving_candidates((this->m_upper_bound_values[bj] - x) / abs(ed), delta, leaving_candidates, bj);
        else if (adj_sign < 0 && x >= this->m_low_bound_values[bj])
            update_delta_of_entering_and_leaving_candidates((x - this->m_low_bound_values[bj]) / abs(ed), delta, leaving_candidates, bj);
        break;
    case low_bound:
        if (adj_sign < 0 && x >= this->m_low_bound_values[bj])
            update_delta_of_entering_and_leaving_candidates((x - this->m_low_bound_values[bj]) / abs(ed), delta, leaving_candidates, bj);
        break;
    case upper_bound:
        if (adj_sign > 0 && x <= this->m_upper_bound_values[bj])
            update_delta_of_entering_and_leaving_candidates((this->m_upper_bound_values[bj] - x) / abs(ed), delta, leaving_candidates, bj);
        break;
    default:
        break;
    }
}

template <typename T, typename X>    X lar_core_solver<T, X>::find_initial_delta_and_its_sign(unsigned row, unsigned entering,
                                                                                              int inf_sign, int & entering_delta_sign,
                                                                                              std::vector<unsigned> & leaving_candidates) {
    lean_assert(inf_sign != 0);
    unsigned bj = this->m_basis[row]; // this is the infeasible basis column
    const X & x = this->m_x[bj];
    entering_delta_sign = - get_sign(this->m_pivot_row[entering]) * inf_sign;
    lean_assert(entering_delta_sign != 0);
    X delta = (inf_sign > 0? (this->m_low_bound_values[bj] - x) : (x - this->m_upper_bound_values[bj])) / abs(this->m_pivot_row[entering]);
    if (this->m_column_type[entering] == boxed) {
        X span = this->bound_span(entering);
        if (span < delta) {
            delta = span;
            leaving_candidates.push_back(entering);
        } else {
            leaving_candidates.push_back(bj);
        }
    } else {
        leaving_candidates.push_back(bj);
    }

    return delta;
}

template <typename T, typename X>    void lar_core_solver<T, X>::advance_on_infeasible_row_and_entering(unsigned inf_row, unsigned entering, int inf_sign) {
    this->solve_Bd(entering); // puts the tableau column of entering into this->m_ed
    int entering_delta_sign;
    std::vector<unsigned> leaving_candidates;
    X delta = find_initial_delta_and_its_sign(inf_row, entering, inf_sign, entering_delta_sign, leaving_candidates);
    lean_assert(leaving_candidates.size());
    lean_assert(delta > zero_of_type<X>());
    unsigned row = my_random() % this->m_m;
    unsigned initial_row = row;
    do {
        if (row != inf_row)
            update_delta_of_entering(entering_delta_sign, row, delta, leaving_candidates);
        if (++row == this->m_m) row = 0;
    } while (row != initial_row);
    unsigned leaving = find_leaving_for_inf_row_strategy(leaving_candidates);
    update_basis_and_x_with_comparison(entering, leaving, delta * entering_delta_sign);
}

template <typename T, typename X>    void lar_core_solver<T, X>::advance_on_infeasible_row(unsigned i, int inf_sign) {
    calculate_pivot_row(i);
    int entering = choose_entering_column_for_row_inf_strategy(inf_sign);
    if (entering == -1) {
        fill_evidence(i, inf_sign);
        this->m_status = INFEASIBLE;
        return;
    }
    advance_on_infeasible_row_and_entering(i, entering, inf_sign);
}

template <typename T, typename X>    void lar_core_solver<T, X>::solve() {
    prefix();
    if (is_empty()) {
        this->m_status = OPTIMAL;
        return;
    }
    this->snap_xN_to_bounds(); // we start with non-basic variables at their bounds
    lean_assert(non_basis_columns_are_set_correctly());

    if (this->m_settings.row_feasibility) {
        row_feasibility_loop();
    } else {
        feasibility_loop();
    }
}

template <typename T, typename X> void lar_core_solver<T, X>::print_column_info(unsigned j, std::ostream & out) {
    out << "type = " << column_type_to_string(this->m_column_type[j]) << std::endl;
    switch (this->m_column_type[j]) {
    case fixed:
    case boxed:
        out << "(" << this->m_low_bound_values[j] << ", " << this->m_upper_bound_values[j] << ")" << std::endl;
        break;
    case low_bound:
        out << this->m_low_bound_values[j] << std::endl;
        break;
    case upper_bound:
        out << this->m_upper_bound_values[j] << std::endl;
        break;
    default:
        lean_unreachable();
    }
}
}

