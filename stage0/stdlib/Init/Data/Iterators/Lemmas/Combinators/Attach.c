// Lean compiler output
// Module: Init.Data.Iterators.Lemmas.Combinators.Attach
// Imports: public import Init.Data.Iterators.Combinators.Attach import all Init.Data.Iterators.Combinators.Attach import all Init.Data.Iterators.Combinators.Monadic.Attach public import Init.Data.Iterators.Lemmas.Combinators.Monadic.Attach public import Init.Data.Iterators.Lemmas.Consumers.Collect public import Init.Data.Array.Attach
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
lean_object* initialize_Init_Data_Iterators_Combinators_Attach(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Iterators_Combinators_Attach(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_Attach(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Array_Attach(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators_Attach(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Combinators_Attach(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_Attach(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_Monadic_Attach(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators_Monadic_Attach(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Attach(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
