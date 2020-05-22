// Lean compiler output
// Module: Std.Data
// Imports: Init
#include <lean/runtime/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_test;
lean_object* _init_l_test() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(10u);
return x_1;
}
}
lean_object* initialize_Init(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Std_Data(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_test = _init_l_test();
lean_mark_persistent(l_test);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
