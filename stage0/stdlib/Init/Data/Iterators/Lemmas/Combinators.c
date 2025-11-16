// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators
// Imports: public import Init.Data.Iterators.Lemmas.Combinators.Attach public import Init.Data.Iterators.Lemmas.Combinators.Monadic public import Init.Data.Iterators.Lemmas.Combinators.FilterMap public import Init.Data.Iterators.Lemmas.Combinators.FlatMap public import Init.Data.Iterators.Lemmas.Combinators.Take public import Init.Data.Iterators.Lemmas.Combinators.ULift
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
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Attach(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_FlatMap(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Take(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Lemmas_Combinators_Attach(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_FlatMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_Take(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_ULift(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
