// Lean compiler output
// Module: Init.Data.String
// Imports: Init.Data.String.Basic Init.Data.String.Bootstrap Init.Data.String.Decode Init.Data.String.Extra Init.Data.String.Lemmas Init.Data.String.Repr Init.Data.String.Bootstrap Init.Data.String.Slice Init.Data.String.Pattern
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
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_String_Bootstrap(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_String_Decode(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_String_Extra(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_String_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_String_Repr(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_String_Bootstrap(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_String_Pattern(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Bootstrap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Decode(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Extra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Repr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Bootstrap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Pattern(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
