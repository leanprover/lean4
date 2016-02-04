/*
  Copyright (c) 2013 Microsoft Corporation. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.

  Author: Lev Nachmanson
*/
#include <cmath>
#include <string>
#include <vector>
#include "util/numerics/double.h"
#include "util/lp/lp_settings.h"
namespace lean {
std::string column_type_to_string(column_type t) {
    switch (t) {
    case fixed:
        return std::string("fixed");
    case boxed:
        return std::string("boxed");
    case low_bound:
        return std::string("low_bound");
    case upper_bound:
        return std::string("upper_bound");
    case free_column:
        return std::string("free_column");
    default:
        lean_unreachable();
    }
}

const char* lp_status_to_string(lp_status status) {
    switch (status) {
    case UNKNOWN: return "UNKNOWN";
    case INFEASIBLE: return "INFEASIBLE";
    case UNBOUNDED: return "UNBOUNDED";
    case TENTATIVE_DUAL_UNBOUNDED: return "TENTATIVE_DUAL_UNBOUNDED";
    case DUAL_UNBOUNDED: return "DUAL_UNBOUNDED";
    case OPTIMAL: return "OPTIMAL";
    case FEASIBLE: return "FEASIBLE";
    case FLOATING_POINT_ERROR: return "FLOATING_POINT_ERROR";
    case TIME_EXHAUSTED: return "TIME_EXHAUSTED";
    case ITERATIONS_EXHAUSTED: return "ITERATIONS_EXHAUSTED";
    case EMPTY: return "EMPTY";
    case UNSTABLE: return "UNSTABLE";
    default:
        lean_unreachable();
    }
}

lp_status lp_status_from_string(std::string status) {
    if (status == "UNKNOWN") return  lp_status::UNKNOWN;
    if (status == "INFEASIBLE") return lp_status::INFEASIBLE;
    if (status == "UNBOUNDED") return lp_status::UNBOUNDED;
    if (status == "OPTIMAL") return lp_status::OPTIMAL;
    if (status == "FEASIBLE") return lp_status::FEASIBLE;
    if (status == "FLOATING_POINT_ERROR") return lp_status::FLOATING_POINT_ERROR;
    if (status == "TIME_EXHAUSTED") return lp_status::TIME_EXHAUSTED;
    if (status == "ITERATIONS_EXHAUSTED") return lp_status::ITERATIONS_EXHAUSTED;
    if (status == "EMPTY") return lp_status::EMPTY;
    lean_unreachable();
}
int get_millisecond_count() {
    timeb tb;
    ftime(&tb);
    return tb.millitm + (tb.time & 0xfffff) * 1000;
}

int get_millisecond_span(int start_time) {
    int span = get_millisecond_count() - start_time;
    if (span < 0)
        span += 0x100000 * 1000;
    return span;
}
void my_random_init(unsigned * seed) {
#ifdef LEAN_WINDOWS
    srand(*seed);
#else
    rand_r(seed);
#endif
}
unsigned my_random() {
#ifdef LEAN_WINDOWS
    return rand(); // NOLINT
#else
    return lrand48();
#endif
}

template <typename T>
bool vectors_are_equal(T * a, std::vector<T>  &b, unsigned n) {
    if (numeric_traits<T>::precise()) {
        for (unsigned i = 0; i < n; i ++){
            if (!numeric_traits<T>::is_zero(a[i] - b[i])) {
                std::cout << "a[" << i <<"]" << a[i] << ", " << "b[" << i <<"]" << b[i] << std::endl;
                return false;
            }
        }
    } else {
        for (unsigned i = 0; i < n; i ++){
            if (std::abs(numeric_traits<T>::get_double(a[i] - b[i])) > 0.000001) {
                std::cout << "a[" << i <<"]" << a[i] << ", " << "b[" << i <<"]" << b[i] << std::endl;
                return false;
            }
        }
    }
    return true;
}

template <typename T>
bool vectors_are_equal(const std::vector<T> & a, const buffer<T>  &b) {
    unsigned n = a.size();
    if (n != b.size()) return false;
    if (numeric_traits<T>::precise()) {
        for (unsigned i = 0; i < n; i ++){
            if (!numeric_traits<T>::is_zero(a[i] - b[i])) {
                std::cout << "a[" << i <<"]" << a[i] << ", " << "b[" << i <<"]" << b[i] << std::endl;
                return false;
            }
        }
    } else {
        for (unsigned i = 0; i < n; i ++){
            if (fabs(numeric_traits<T>::get_double(a[i] - b[i])) > 0.000001) {
                std::cout << "a[" << i <<"] = " << a[i] << ", but " << "b[" << i <<"] = " << b[i] << std::endl;
                return false;
            }
        }
    }
    return true;
}

template <typename T>
bool vectors_are_equal(const std::vector<T> & a, const std::vector<T>  &b) {
    unsigned n = a.size();
    if (n != b.size()) return false;
    if (numeric_traits<T>::precise()) {
        for (unsigned i = 0; i < n; i ++){
            if (!numeric_traits<T>::is_zero(a[i] - b[i])) {
                std::cout << "a[" << i <<"]" << a[i] << ", " << "b[" << i <<"]" << b[i] << std::endl;
                return false;
            }
        }
    } else {
        for (unsigned i = 0; i < n; i ++){
            if (fabs(numeric_traits<T>::get_double(a[i] - b[i])) > 0.000001) {
                std::cout << "a[" << i <<"] = " << a[i] << ", but " << "b[" << i <<"] = " << b[i] << std::endl;
                return false;
            }
        }
    }
    return true;
}
}
