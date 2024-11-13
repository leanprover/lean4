// Lean compiler output
// Module: Init.Data.List
// Imports: Init.Data.List.Attach Init.Data.List.Basic Init.Data.List.BasicAux Init.Data.List.Control Init.Data.List.Count Init.Data.List.Erase Init.Data.List.Find Init.Data.List.Impl Init.Data.List.Lemmas Init.Data.List.MinMax Init.Data.List.Monadic Init.Data.List.Nat Init.Data.List.Notation Init.Data.List.Pairwise Init.Data.List.Sublist Init.Data.List.TakeDrop Init.Data.List.Zip Init.Data.List.Perm Init.Data.List.Sort Init.Data.List.ToArray Init.Data.List.MapIdx Init.Data.List.OfFn
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
lean_object* initialize_Init_Data_List_Attach(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_BasicAux(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Control(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Count(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Erase(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Find(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Impl(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_MinMax(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Monadic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Nat(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Notation(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Pairwise(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_TakeDrop(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Zip(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Perm(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Sort(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_ToArray(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_MapIdx(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_OfFn(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Attach(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_BasicAux(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Control(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Count(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Erase(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Find(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Impl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MinMax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Monadic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Nat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Notation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Pairwise(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sublist(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_TakeDrop(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Zip(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Perm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sort(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_ToArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MapIdx(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_OfFn(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
