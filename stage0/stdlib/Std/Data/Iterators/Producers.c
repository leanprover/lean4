// Lean compiler output
// Module: Std.Data.Iterators.Producers
// Imports: public import Std.Data.Iterators.Producers.Monadic public import Std.Data.Iterators.Producers.Array public import Std.Data.Iterators.Producers.Vector public import Std.Data.Iterators.Producers.Empty public import Std.Data.Iterators.Producers.Range public import Std.Data.Iterators.Producers.Repeat public import Std.Data.Iterators.Producers.Slice
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
lean_object* initialize_Std_Data_Iterators_Producers_Monadic(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Producers_Array(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Producers_Vector(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Producers_Empty(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Producers_Range(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Producers_Repeat(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Producers_Slice(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Producers(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Producers_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Producers_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Producers_Vector(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Producers_Empty(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Producers_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Producers_Repeat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Producers_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
