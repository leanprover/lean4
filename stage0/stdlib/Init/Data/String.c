// Lean compiler output
// Module: Init.Data.String
// Imports: public import Init.Data.String.Basic public import Init.Data.String.Bootstrap public import Init.Data.String.Decode public import Init.Data.String.Defs public import Init.Data.String.Extra public import Init.Data.String.Iterator public import Init.Data.String.Lemmas public import Init.Data.String.Bootstrap public import Init.Data.String.Slice public import Init.Data.String.Pattern public import Init.Data.String.Stream public import Init.Data.String.PosRaw public import Init.Data.String.Substring public import Init.Data.String.TakeDrop public import Init.Data.String.Modify public import Init.Data.String.Termination public import Init.Data.String.ToSlice public import Init.Data.String.Search public import Init.Data.String.Legacy public import Init.Data.String.OrderInstances public import Init.Data.String.FindPos public import Init.Data.String.Subslice public import Init.Data.String.Iter public import Init.Data.String.Iterate
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
lean_object* initialize_Init_Data_String_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_String_Decode(uint8_t builtin);
lean_object* initialize_Init_Data_String_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_String_Extra(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iterator(uint8_t builtin);
lean_object* initialize_Init_Data_String_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_String_Slice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Pattern(uint8_t builtin);
lean_object* initialize_Init_Data_String_Stream(uint8_t builtin);
lean_object* initialize_Init_Data_String_PosRaw(uint8_t builtin);
lean_object* initialize_Init_Data_String_Substring(uint8_t builtin);
lean_object* initialize_Init_Data_String_TakeDrop(uint8_t builtin);
lean_object* initialize_Init_Data_String_Modify(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* initialize_Init_Data_String_ToSlice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Search(uint8_t builtin);
lean_object* initialize_Init_Data_String_Legacy(uint8_t builtin);
lean_object* initialize_Init_Data_String_OrderInstances(uint8_t builtin);
lean_object* initialize_Init_Data_String_FindPos(uint8_t builtin);
lean_object* initialize_Init_Data_String_Subslice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iter(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iterate(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Decode(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Extra(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_PosRaw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Substring(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_TakeDrop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Modify(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_ToSlice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Legacy(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_OrderInstances(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_FindPos(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Subslice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iterate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
