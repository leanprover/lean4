// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators
// Imports: public import Std.Data.Iterators.Lemmas.Combinators.Monadic public import Std.Data.Iterators.Lemmas.Combinators.TakeWhile public import Std.Data.Iterators.Lemmas.Combinators.Drop public import Std.Data.Iterators.Lemmas.Combinators.DropWhile public import Std.Data.Iterators.Lemmas.Combinators.Zip
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
lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Combinators_TakeWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Combinators_Drop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Combinators_DropWhile(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Combinators_Zip(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
