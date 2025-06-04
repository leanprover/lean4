// Lean compiler output
// Module: Std.Data.Iterators
// Imports: Std.Data.Iterators.Basic Std.Data.Iterators.Producers Std.Data.Iterators.Consumers Std.Data.Iterators.Combinators Std.Data.Iterators.Lemmas Std.Data.Iterators.PostConditionMonad Std.Data.Iterators.Internal
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
lean_object* initialize_Std_Data_Iterators_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Iterators_Producers(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Iterators_Consumers(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Iterators_Combinators(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Iterators_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Iterators_PostConditionMonad(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Data_Iterators_Internal(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Producers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Consumers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Combinators(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_PostConditionMonad(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Internal(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
