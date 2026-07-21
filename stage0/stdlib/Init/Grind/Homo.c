// Lean compiler output
// Module: Init.Grind.Homo
// Imports: public import Init.Grind.Homo.BitVec public import Init.Grind.Homo.Fin public import Init.Grind.Homo.Nat public import Init.Grind.Homo.Int public import Init.Grind.Homo.List public import Init.Grind.Homo.UInt8 public import Init.Grind.Homo.UInt16 public import Init.Grind.Homo.UInt32 public import Init.Grind.Homo.UInt64 public import Init.Grind.Homo.USize public import Init.Grind.Homo.Int8 public import Init.Grind.Homo.Int16 public import Init.Grind.Homo.Int32 public import Init.Grind.Homo.Int64 public import Init.Grind.Homo.ISize
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
lean_object* runtime_initialize_Init_Grind_Homo_BitVec(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Homo_Fin(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Homo_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Homo_Int(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Homo_List(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Homo_UInt8(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Homo_UInt16(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Homo_UInt32(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Homo_UInt64(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Homo_USize(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Homo_Int8(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Homo_Int16(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Homo_Int32(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Homo_Int64(uint8_t builtin);
lean_object* runtime_initialize_Init_Grind_Homo_ISize(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Homo(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_Homo_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Homo_Fin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Homo_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Homo_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Homo_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Homo_UInt8(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Homo_UInt16(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Homo_UInt32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Homo_UInt64(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Homo_USize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Homo_Int8(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Homo_Int16(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Homo_Int32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Homo_Int64(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Homo_ISize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Homo(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Homo_BitVec(uint8_t builtin);
lean_object* initialize_Init_Grind_Homo_Fin(uint8_t builtin);
lean_object* initialize_Init_Grind_Homo_Nat(uint8_t builtin);
lean_object* initialize_Init_Grind_Homo_Int(uint8_t builtin);
lean_object* initialize_Init_Grind_Homo_List(uint8_t builtin);
lean_object* initialize_Init_Grind_Homo_UInt8(uint8_t builtin);
lean_object* initialize_Init_Grind_Homo_UInt16(uint8_t builtin);
lean_object* initialize_Init_Grind_Homo_UInt32(uint8_t builtin);
lean_object* initialize_Init_Grind_Homo_UInt64(uint8_t builtin);
lean_object* initialize_Init_Grind_Homo_USize(uint8_t builtin);
lean_object* initialize_Init_Grind_Homo_Int8(uint8_t builtin);
lean_object* initialize_Init_Grind_Homo_Int16(uint8_t builtin);
lean_object* initialize_Init_Grind_Homo_Int32(uint8_t builtin);
lean_object* initialize_Init_Grind_Homo_Int64(uint8_t builtin);
lean_object* initialize_Init_Grind_Homo_ISize(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Homo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Homo_BitVec(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Homo_Fin(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Homo_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Homo_Int(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Homo_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Homo_UInt8(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Homo_UInt16(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Homo_UInt32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Homo_UInt64(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Homo_USize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Homo_Int8(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Homo_Int16(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Homo_Int32(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Homo_Int64(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Homo_ISize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Homo(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Homo(builtin);
}
#ifdef __cplusplus
}
#endif
