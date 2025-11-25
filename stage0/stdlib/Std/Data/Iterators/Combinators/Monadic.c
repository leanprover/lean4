// Lean compiler output
// Module: Std.Data.Iterators.Combinators.Monadic
// Imports: public import Std.Data.Iterators.Combinators.Monadic.TakeWhile public import Std.Data.Iterators.Combinators.Monadic.Drop public import Std.Data.Iterators.Combinators.Monadic.DropWhile public import Std.Data.Iterators.Combinators.Monadic.StepSize public import Std.Data.Iterators.Combinators.Monadic.Zip
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
lean_object* initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Combinators_Monadic_Drop(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Combinators_Monadic_Zip(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Combinators_Monadic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Combinators_Monadic_TakeWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Combinators_Monadic_Drop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Combinators_Monadic_DropWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Combinators_Monadic_StepSize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Combinators_Monadic_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
