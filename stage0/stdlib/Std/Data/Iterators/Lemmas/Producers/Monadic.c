// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Producers.Monadic
// Imports: public import Std.Data.Iterators.Lemmas.Producers.Monadic.Array public import Std.Data.Iterators.Lemmas.Producers.Monadic.Vector public import Std.Data.Iterators.Lemmas.Producers.Monadic.Empty public import Std.Data.Iterators.Lemmas.Producers.Monadic.List
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
lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_Monadic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Vector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_Empty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Producers_Monadic_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
