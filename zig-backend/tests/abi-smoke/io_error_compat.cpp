#include <cstdlib>

extern "C" {

#define WEAK __attribute__((weak))

WEAK void leanrt_cpp_partial_hidden_lean_initialize_runtime_module() {}

WEAK void leanrt_cpp_partial_hidden_lean_initialize_thread() {}

WEAK void leanrt_cpp_partial_hidden_lean_finalize_thread() {}

WEAK void leanrt_cpp_partial_hidden_lean_io_mark_end_initialization() {}

WEAK char **leanrt_cpp_partial_hidden_lean_setup_args(int argc, char **argv) {
    (void)argc;
    return argv;
}

WEAK void *leanrt_cpp_partial_hidden_lean_task_spawn_core_impl(void *c, unsigned prio, bool keep_alive) {
    (void)c;
    (void)prio;
    (void)keep_alive;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_task_bind_core_impl(void *x, void *f, unsigned prio, bool sync, bool keep_alive) {
    (void)x;
    (void)f;
    (void)prio;
    (void)sync;
    (void)keep_alive;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_task_map_core_impl(void *f, void *t, unsigned prio, bool sync, bool keep_alive) {
    (void)f;
    (void)t;
    (void)prio;
    (void)sync;
    (void)keep_alive;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_task_get_impl(void *t) {
    (void)t;
    std::abort();
}

WEAK bool leanrt_cpp_partial_hidden_lean_io_check_canceled_core_impl() {
    std::abort();
}

WEAK void leanrt_cpp_partial_hidden_lean_io_cancel_core_impl(void *t) {
    (void)t;
    std::abort();
}

WEAK unsigned char leanrt_cpp_partial_hidden_lean_io_get_task_state_core_impl(void *t) {
    (void)t;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_io_wait_any_core_impl(void *task_list) {
    (void)task_list;
    std::abort();
}

WEAK void *mi_malloc_small(size_t size) {
    return std::malloc(size);
}

WEAK void *mi_malloc(size_t size) {
    return std::malloc(size);
}

WEAK void mi_free(void *ptr) {
    std::free(ptr);
}

WEAK void mi_free_size(void *ptr, size_t size) {
    (void)size;
    std::free(ptr);
}

WEAK void leanrt_cpp_partial_hidden_lean_free_object_impl(void *o) {
    (void)o;
    std::abort();
}

WEAK void lean_notify_assert(const char *fileName, int line, const char *condition) {
    (void)fileName;
    (void)line;
    (void)condition;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_cstr_to_nat_impl(const char *n) {
    (void)n;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_big_usize_to_nat_impl(size_t n) {
    (void)n;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_big_uint64_to_nat_impl(unsigned long long n) {
    (void)n;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_cstr_to_int_impl(const char *n) {
    (void)n;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_big_int_to_int_impl(int n) {
    (void)n;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_big_size_t_to_int_impl(size_t n) {
    (void)n;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_big_int64_to_int_impl(long long n) {
    (void)n;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_big_int_to_nat_impl(void *a) {
    (void)a;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_int_big_neg_impl(void *a) {
    (void)a;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_int_big_add_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_int_big_sub_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_int_big_mul_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_int_big_div_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_int_big_div_exact_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_int_big_mod_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_int_big_ediv_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_int_big_emod_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK bool leanrt_cpp_partial_hidden_lean_int_big_eq_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK bool leanrt_cpp_partial_hidden_lean_int_big_le_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK bool leanrt_cpp_partial_hidden_lean_int_big_lt_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK bool leanrt_cpp_partial_hidden_lean_int_big_nonneg_impl(void *a) {
    (void)a;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_nat_big_succ_impl(void *a) {
    (void)a;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_nat_big_add_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_nat_big_sub_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_nat_big_mul_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_nat_big_div_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_nat_big_div_exact_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_nat_big_mod_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_nat_overflow_mul_impl(size_t a1, size_t a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK bool leanrt_cpp_partial_hidden_lean_nat_big_eq_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK bool leanrt_cpp_partial_hidden_lean_nat_big_le_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK bool leanrt_cpp_partial_hidden_lean_nat_big_lt_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_nat_big_land_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_nat_big_lor_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_nat_big_xor_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_nat_shiftl_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_nat_big_shiftr_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_nat_pow_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_nat_gcd_impl(void *a1, void *a2) {
    (void)a1;
    (void)a2;
    std::abort();
}

WEAK void *leanrt_cpp_partial_hidden_lean_nat_log2_impl(void *a) {
    (void)a;
    std::abort();
}

}
