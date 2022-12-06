// Lean compiler output
// Module: Init.Data.Fin.Log2
// Imports: Init.Data.Nat.Log2
#include <lean/lean.h>
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
lean_object* lean_nat_log2(lean_object*);
LEAN_EXPORT lean_object* l_Fin_log2___rarg(lean_object*);
LEAN_EXPORT lean_object* l_Fin_log2(lean_object*);
LEAN_EXPORT lean_object* l_Fin_log2___rarg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_log2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Fin_log2___rarg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_log2(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_log2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Fin_log2___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_log2___rarg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_log2___rarg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Fin_log2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Fin_log2(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Nat_Log2(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Fin_Log2(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Log2(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
