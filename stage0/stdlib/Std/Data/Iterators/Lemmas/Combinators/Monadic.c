// Lean compiler output
// Module: Std.Data.Iterators.Lemmas.Combinators.Monadic
// Imports: Std.Data.Iterators.Lemmas.Combinators.Monadic.Take Std.Data.Iterators.Lemmas.Combinators.Monadic.TakeWhile Std.Data.Iterators.Lemmas.Combinators.Monadic.Drop Std.Data.Iterators.Lemmas.Combinators.Monadic.DropWhile Std.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap Std.Data.Iterators.Lemmas.Combinators.Monadic.Zip
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
lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Take(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Drop(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_DropWhile(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Take(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_TakeWhile(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Drop(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_DropWhile(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_FilterMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Combinators_Monadic_Zip(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
