// Lean compiler output
// Module: Init.Data.List
// Imports: public import Init.Data.List.Attach public import Init.Data.List.Basic public import Init.Data.List.BasicAux public import Init.Data.List.Control public import Init.Data.List.Count public import Init.Data.List.Erase public import Init.Data.List.Find public import Init.Data.List.Impl public import Init.Data.List.Lemmas public import Init.Data.List.MinMax public import Init.Data.List.Monadic public import Init.Data.List.Nat public import Init.Data.List.Notation public import Init.Data.List.Pairwise public import Init.Data.List.Sublist public import Init.Data.List.TakeDrop public import Init.Data.List.Zip public import Init.Data.List.Perm public import Init.Data.List.Sort public import Init.Data.List.ToArray public import Init.Data.List.ToArrayImpl public import Init.Data.List.MapIdx public import Init.Data.List.OfFn public import Init.Data.List.FinRange public import Init.Data.List.Lex
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
lean_object* initialize_Init_Data_List_ToArrayImpl(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_MapIdx(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_OfFn(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_FinRange(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Lex(uint8_t builtin, lean_object*);
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
res = initialize_Init_Data_List_ToArrayImpl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_MapIdx(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_OfFn(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_FinRange(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
