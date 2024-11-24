// Lean compiler output
// Module: Init.Data.List.Nat
// Imports: Init.Data.List.Nat.Basic Init.Data.List.Nat.Pairwise Init.Data.List.Nat.Range Init.Data.List.Nat.Sublist Init.Data.List.Nat.TakeDrop Init.Data.List.Nat.Count Init.Data.List.Nat.Erase Init.Data.List.Nat.Find Init.Data.List.Nat.BEq Init.Data.List.Nat.Modify Init.Data.List.Nat.InsertIdx
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
lean_object* initialize_Init_Data_List_Nat_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Nat_Pairwise(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Nat_Range(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Nat_Sublist(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Nat_Count(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Nat_Erase(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Nat_Find(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Nat_BEq(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Nat_Modify(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Nat_InsertIdx(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Nat(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Nat_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Pairwise(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Range(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Sublist(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_TakeDrop(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Count(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Erase(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Find(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_BEq(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_Modify(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat_InsertIdx(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
