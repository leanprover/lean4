// Lean compiler output
// Module: Lean.Server.FileWorker.SignatureHelp
// Imports: Lean.Server.InfoUtils Lean.Data.Lsp Init.Data.List.Sort.Basic
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at_Lean_Syntax_structRangeEq___spec__1(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__5;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___closed__2;
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__1;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__18;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__1___boxed(lean_object*, lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__2;
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__4___closed__1;
lean_object* l_List_mergeSort___rarg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__1(size_t, size_t, lean_object*);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__14;
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__7;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_noConfusion(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getRangeWithTrailing_x3f(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_toCtorIdx___boxed(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion___rarg___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(uint8_t);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1;
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__4;
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Elab_InfoTree_smallestInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__4(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__3;
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__19;
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__6;
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__4___closed__2;
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__9;
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__2___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__20;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__1(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion___rarg___closed__1;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_FileMap_lineStart(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio___boxed(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__4;
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__8;
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__16;
lean_object* l_Lean_PrettyPrinter_ppTerm(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Format_defWidth;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__2___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__5___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__4;
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___spec__1(lean_object*, lean_object*);
uint8_t l_String_Range_contains(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__13;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__5(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_hasArgs(lean_object*);
lean_object* l_Lean_PrettyPrinter_Delaborator_delabForallWithSignature(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__4(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_findStack_x3f(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___lambda__1___boxed(lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__3___boxed(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__12;
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__11;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__17;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__15;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1;
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__2;
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__1;
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_noConfusion___rarg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__2___boxed(lean_object*);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__4___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___lambda__1(lean_object*);
static lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_noConfusion___rarg(uint8_t, uint8_t, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__2(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__3;
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion(lean_object*);
lean_object* l_Lean_PrettyPrinter_delabCore___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Elab_ContextInfo_runMetaM___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_toCtorIdx(uint8_t);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(lean_object*);
static lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__10;
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_4, 1);
x_6 = 0;
x_7 = l_Lean_Syntax_getRangeWithTrailing_x3f(x_5, x_6);
x_8 = l_Lean_Syntax_getRangeWithTrailing_x3f(x_1, x_6);
x_9 = l_Option_beqOption____x40_Init_Data_Option_Basic___hyg_160____at_Lean_Syntax_structRangeEq___spec__1(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Delaborator_delabForallWithSignature), 7, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__2___closed__1;
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_PrettyPrinter_delabCore___rarg(x_1, x_8, x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_PrettyPrinter_ppTerm(x_13, x_5, x_6, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 0);
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_6);
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_10);
if (x_26 == 0)
{
return x_10;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_10, 0);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_10);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_8, x_2, x_3, x_4, x_5, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_Expr_isForall(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(0);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_free_object(x_10);
x_16 = lean_box(0);
x_17 = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__2(x_12, x_16, x_2, x_3, x_4, x_5, x_13);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = l_Lean_Expr_isForall(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_box(0);
x_24 = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__2(x_18, x_23, x_2, x_3, x_4, x_5, x_19);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__1___boxed), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = l_Lean_Elab_InfoTree_smallestInfo_x3f(x_4, x_1);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 1)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_8, 0);
x_12 = lean_ctor_get(x_8, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__3), 6, 1);
lean_closure_set(x_16, 0, x_14);
x_17 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_11, x_15, x_16, x_3);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_free_object(x_8);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_17, 0, x_21);
return x_17;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_dec(x_17);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_17, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = l_Std_Format_defWidth;
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_format_pretty(x_28, x_29, x_30, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_32);
x_34 = lean_box(0);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 1, x_34);
lean_ctor_set(x_8, 0, x_33);
x_35 = lean_array_mk(x_8);
x_36 = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__1;
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_37, 2, x_32);
lean_ctor_set(x_18, 0, x_37);
return x_17;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_38 = lean_ctor_get(x_18, 0);
lean_inc(x_38);
lean_dec(x_18);
x_39 = l_Std_Format_defWidth;
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_format_pretty(x_38, x_39, x_40, x_40);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
lean_ctor_set(x_43, 2, x_42);
lean_ctor_set(x_43, 3, x_42);
x_44 = lean_box(0);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 1, x_44);
lean_ctor_set(x_8, 0, x_43);
x_45 = lean_array_mk(x_8);
x_46 = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__1;
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
lean_ctor_set(x_47, 2, x_42);
x_48 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_17, 0, x_48);
return x_17;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_49 = lean_ctor_get(x_17, 1);
lean_inc(x_49);
lean_dec(x_17);
x_50 = lean_ctor_get(x_18, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 x_51 = x_18;
} else {
 lean_dec_ref(x_18);
 x_51 = lean_box(0);
}
x_52 = l_Std_Format_defWidth;
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_format_pretty(x_50, x_52, x_53, x_53);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_55);
lean_ctor_set(x_56, 3, x_55);
x_57 = lean_box(0);
lean_ctor_set_tag(x_8, 1);
lean_ctor_set(x_8, 1, x_57);
lean_ctor_set(x_8, 0, x_56);
x_58 = lean_array_mk(x_8);
x_59 = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__1;
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_55);
if (lean_is_scalar(x_51)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_51;
}
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_49);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_free_object(x_8);
x_63 = !lean_is_exclusive(x_17);
if (x_63 == 0)
{
return x_17;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_17, 0);
x_65 = lean_ctor_get(x_17, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_17);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_8, 0);
lean_inc(x_67);
lean_dec(x_8);
x_68 = lean_ctor_get(x_9, 0);
lean_inc(x_68);
lean_dec(x_9);
x_69 = lean_ctor_get(x_68, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__3), 6, 1);
lean_closure_set(x_71, 0, x_69);
x_72 = l_Lean_Elab_ContextInfo_runMetaM___rarg(x_67, x_70, x_71, x_3);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = lean_box(0);
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_78 = lean_ctor_get(x_72, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_79 = x_72;
} else {
 lean_dec_ref(x_72);
 x_79 = lean_box(0);
}
x_80 = lean_ctor_get(x_73, 0);
lean_inc(x_80);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 x_81 = x_73;
} else {
 lean_dec_ref(x_73);
 x_81 = lean_box(0);
}
x_82 = l_Std_Format_defWidth;
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_format_pretty(x_80, x_82, x_83, x_83);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_85);
lean_ctor_set(x_86, 3, x_85);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_array_mk(x_88);
x_90 = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__1;
x_91 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_91, 2, x_85);
if (lean_is_scalar(x_81)) {
 x_92 = lean_alloc_ctor(1, 1, 0);
} else {
 x_92 = x_81;
}
lean_ctor_set(x_92, 0, x_91);
if (lean_is_scalar(x_79)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_79;
}
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_78);
return x_93;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_72, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_72, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_96 = x_72;
} else {
 lean_dec_ref(x_72);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_9);
x_98 = !lean_is_exclusive(x_8);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_8, 1);
lean_dec(x_99);
x_100 = lean_ctor_get(x_8, 0);
lean_dec(x_100);
x_101 = lean_box(0);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 0, x_101);
return x_8;
}
else
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_8);
x_102 = lean_box(0);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_3);
return x_103;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion___rarg___lambda__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion___rarg___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
default: 
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_toCtorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_noConfusion___rarg(uint8_t x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion___rarg___closed__1;
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_noConfusion(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_SearchControl_noConfusion___rarg___boxed), 3, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_SearchControl_noConfusion___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Server_FileWorker_SignatureHelp_SearchControl_noConfusion___rarg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 0);
lean_dec(x_5);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_string_utf8_byte_size(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint32_t x_13; uint32_t x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_4, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_4, 0);
lean_dec(x_12);
x_13 = 45;
x_14 = lean_string_utf8_get_fast(x_6, x_7);
x_15 = lean_uint32_dec_eq(x_14, x_13);
x_16 = lean_string_utf8_next_fast(x_6, x_7);
lean_inc(x_16);
lean_inc(x_6);
lean_ctor_set(x_4, 1, x_16);
if (x_15 == 0)
{
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_lt(x_16, x_8);
lean_dec(x_8);
if (x_18 == 0)
{
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_inc(x_1);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
else
{
uint32_t x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
x_20 = lean_string_utf8_get_fast(x_6, x_16);
x_21 = lean_uint32_dec_eq(x_20, x_13);
x_22 = lean_string_utf8_next_fast(x_6, x_16);
lean_dec(x_16);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_22);
if (x_21 == 0)
{
lean_dec(x_7);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_23);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_1);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_7);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_2, 1, x_23);
lean_ctor_set(x_2, 0, x_26);
return x_2;
}
}
}
}
else
{
uint32_t x_27; uint32_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
x_27 = 45;
x_28 = lean_string_utf8_get_fast(x_6, x_7);
x_29 = lean_uint32_dec_eq(x_28, x_27);
x_30 = lean_string_utf8_next_fast(x_6, x_7);
lean_inc(x_30);
lean_inc(x_6);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_30);
if (x_29 == 0)
{
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_31);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_lt(x_30, x_8);
lean_dec(x_8);
if (x_33 == 0)
{
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_31);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
else
{
uint32_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_31);
x_35 = lean_string_utf8_get_fast(x_6, x_30);
x_36 = lean_uint32_dec_eq(x_35, x_27);
x_37 = lean_string_utf8_next_fast(x_6, x_30);
lean_dec(x_30);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_37);
if (x_36 == 0)
{
lean_dec(x_7);
lean_inc(x_1);
lean_ctor_set(x_2, 1, x_38);
lean_ctor_set(x_2, 0, x_1);
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_1);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_7);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_2, 1, x_38);
lean_ctor_set(x_2, 0, x_41);
return x_2;
}
}
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
lean_dec(x_2);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
x_45 = lean_string_utf8_byte_size(x_43);
x_46 = lean_nat_dec_lt(x_44, x_45);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_42);
return x_47;
}
else
{
lean_object* x_48; uint32_t x_49; uint32_t x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_48 = x_42;
} else {
 lean_dec_ref(x_42);
 x_48 = lean_box(0);
}
x_49 = 45;
x_50 = lean_string_utf8_get_fast(x_43, x_44);
x_51 = lean_uint32_dec_eq(x_50, x_49);
x_52 = lean_string_utf8_next_fast(x_43, x_44);
lean_inc(x_52);
lean_inc(x_43);
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_43);
lean_ctor_set(x_53, 1, x_52);
if (x_51 == 0)
{
lean_object* x_54; 
lean_dec(x_52);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_inc(x_1);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_1);
lean_ctor_set(x_54, 1, x_53);
x_2 = x_54;
goto _start;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_lt(x_52, x_45);
lean_dec(x_45);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_52);
lean_dec(x_44);
lean_dec(x_43);
lean_inc(x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_53);
x_2 = x_57;
goto _start;
}
else
{
uint32_t x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_53);
x_59 = lean_string_utf8_get_fast(x_43, x_52);
x_60 = lean_uint32_dec_eq(x_59, x_49);
x_61 = lean_string_utf8_next_fast(x_43, x_52);
lean_dec(x_52);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_43);
lean_ctor_set(x_62, 1, x_61);
if (x_60 == 0)
{
lean_object* x_63; 
lean_dec(x_44);
lean_inc(x_1);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_62);
x_2 = x_63;
goto _start;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_1);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_44);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
return x_67;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1;
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = l_Lean_Loop_forIn_loop___at___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___spec__1(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2;
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_3 = l_Lean_FileMap_toPosition(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_Lean_FileMap_lineStart(x_1, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_8 = l_Lean_FileMap_lineStart(x_1, x_7);
lean_dec(x_7);
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_string_utf8_extract(x_9, x_5, x_8);
lean_dec(x_8);
lean_dec(x_9);
x_11 = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f(x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_5);
x_12 = 0;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_13);
lean_dec(x_5);
x_15 = lean_nat_dec_le(x_14, x_2);
lean_dec(x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 1;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___closed__2() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___closed__1;
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___closed__2;
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term_<|_", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("term_$__", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Parser", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Term", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("pipeProj", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__5;
x_2 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__6;
x_3 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__7;
x_4 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__8;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dotIdent", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__5;
x_2 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__6;
x_3 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__7;
x_4 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__10;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("proj", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__5;
x_2 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__6;
x_3 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__7;
x_4 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__12;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__14;
x_2 = lean_box(0);
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__16() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__17() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ident", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__17;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__19() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 0;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__20() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__19;
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__2;
lean_inc(x_1);
x_5 = l_Lean_Syntax_isOfKind(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__4;
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__9;
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__11;
lean_inc(x_1);
x_11 = l_Lean_Syntax_isOfKind(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__13;
lean_inc(x_1);
x_13 = l_Lean_Syntax_isOfKind(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
lean_dec(x_1);
x_14 = lean_array_get_size(x_2);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_dec_le(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__15;
return x_17;
}
else
{
lean_object* x_18; 
x_18 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__16;
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
lean_dec(x_1);
x_21 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__18;
x_22 = l_Lean_Syntax_isOfKind(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_array_get_size(x_2);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_dec_le(x_23, x_24);
lean_dec(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__15;
return x_26;
}
else
{
lean_object* x_27; 
x_27 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__16;
return x_27;
}
}
else
{
lean_object* x_28; 
x_28 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___closed__2;
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = l_Lean_Syntax_getArg(x_1, x_29);
lean_dec(x_1);
x_31 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__18;
x_32 = l_Lean_Syntax_isOfKind(x_30, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_array_get_size(x_2);
x_34 = lean_nat_dec_le(x_33, x_29);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__15;
return x_35;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__16;
return x_36;
}
}
else
{
lean_object* x_37; 
x_37 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___closed__2;
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_unsigned_to_nat(2u);
x_39 = l_Lean_Syntax_getArg(x_1, x_38);
lean_dec(x_1);
x_40 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__18;
x_41 = l_Lean_Syntax_isOfKind(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_array_get_size(x_2);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__15;
return x_45;
}
else
{
lean_object* x_46; 
x_46 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__16;
return x_46;
}
}
else
{
lean_object* x_47; 
x_47 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__20;
return x_47;
}
}
}
else
{
lean_object* x_48; 
lean_dec(x_1);
x_48 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__20;
return x_48;
}
}
else
{
lean_object* x_49; 
lean_dec(x_1);
x_49 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__20;
return x_49;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("app", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__5;
x_2 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__6;
x_3 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__7;
x_4 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__1;
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 2;
x_2 = lean_box(x_1);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__4() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__3;
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__2;
x_6 = lean_name_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2(x_1, x_2, x_7);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__4;
return x_9;
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("null", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__4___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__4(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
x_5 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__4___closed__2;
x_6 = lean_name_eq(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3(x_1, x_4, x_3, x_7);
lean_dec(x_3);
lean_dec(x_4);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_9 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__16;
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__16;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_4; uint8_t x_5; 
lean_dec(x_1);
x_4 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__9;
lean_inc(x_2);
x_5 = l_Lean_Syntax_isOfKind(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__13;
lean_inc(x_2);
x_7 = l_Lean_Syntax_isOfKind(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__11;
lean_inc(x_2);
x_9 = l_Lean_Syntax_isOfKind(x_2, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_2);
x_10 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___closed__2;
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = l_Lean_Syntax_getArg(x_2, x_11);
lean_dec(x_2);
x_13 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__18;
x_14 = l_Lean_Syntax_isOfKind(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___closed__2;
return x_15;
}
else
{
lean_object* x_16; 
x_16 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__16;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_unsigned_to_nat(2u);
x_18 = l_Lean_Syntax_getArg(x_2, x_17);
lean_dec(x_2);
x_19 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__18;
x_20 = l_Lean_Syntax_isOfKind(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___closed__2;
return x_21;
}
else
{
lean_object* x_22; 
x_22 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__16;
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_unsigned_to_nat(2u);
x_24 = l_Lean_Syntax_getArg(x_2, x_23);
lean_dec(x_2);
x_25 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__18;
x_26 = l_Lean_Syntax_isOfKind(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___closed__2;
return x_27;
}
else
{
lean_object* x_28; 
x_28 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__16;
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_2);
x_29 = lean_box(0);
x_30 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__4(x_1, x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
lean_inc(x_1);
x_8 = l_Lean_FileMap_toPosition(x_1, x_2);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = l_Lean_FileMap_toPosition(x_1, x_3);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_nat_dec_eq(x_9, x_11);
lean_dec(x_11);
lean_dec(x_9);
if (lean_obj_tag(x_6) == 0)
{
if (x_12 == 0)
{
lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_4);
x_24 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__16;
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_box(0);
x_26 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__5(x_4, x_5, x_25);
return x_26;
}
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_6, 0);
x_28 = lean_ctor_get_uint8(x_27, sizeof(void*)*2);
x_29 = lean_box(x_28);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = 1;
x_13 = x_30;
x_14 = x_27;
goto block_23;
}
else
{
uint8_t x_31; 
lean_dec(x_29);
x_31 = 0;
x_13 = x_31;
x_14 = x_27;
goto block_23;
}
}
block_23:
{
if (x_12 == 0)
{
if (x_13 == 0)
{
uint8_t x_15; 
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*2 + 1);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_4);
x_16 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__16;
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(0);
x_18 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__5(x_4, x_5, x_17);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
x_20 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__5(x_4, x_5, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__5(x_4, x_5, x_21);
return x_22;
}
}
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1() {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = 1;
x_7 = l_Lean_Syntax_getTailPos_x3f(x_4, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_8 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__16;
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_nat_dec_lt(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__6(x_1, x_3, x_9, x_4, x_5, x_2, x_11);
lean_dec(x_9);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_13 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1;
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__4___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__4(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__5(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__2___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_1 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_7, 1);
x_14 = lean_nat_dec_lt(x_9, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_array_fget(x_5, x_9);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_9, x_17);
x_19 = lean_nat_dec_lt(x_18, x_6);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
x_20 = lean_box(0);
lean_inc(x_16);
lean_inc(x_1);
x_21 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(x_1, x_2, x_3, x_16, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_16);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = lean_unbox(x_23);
lean_dec(x_23);
x_26 = l_Std_Range_forIn_x27_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__2___lambda__1(x_25, x_8, x_24, x_12);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_9);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_dec(x_26);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec(x_27);
x_36 = lean_ctor_get(x_7, 2);
x_37 = lean_nat_add(x_9, x_36);
lean_dec(x_9);
x_8 = x_35;
x_9 = x_37;
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = x_34;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; 
x_39 = lean_ctor_get(x_21, 1);
lean_inc(x_39);
lean_dec(x_21);
x_40 = lean_ctor_get(x_22, 0);
lean_inc(x_40);
lean_dec(x_22);
x_41 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_41, 0, x_16);
x_42 = lean_unbox(x_40);
lean_dec(x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*1, x_42);
x_43 = lean_array_push(x_8, x_41);
x_44 = lean_box(0);
x_45 = lean_unbox(x_39);
lean_dec(x_39);
x_46 = l_Std_Range_forIn_x27_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__2___lambda__1(x_45, x_43, x_44, x_12);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
uint8_t x_48; 
lean_dec(x_9);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_46, 0);
lean_dec(x_49);
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_ctor_get(x_47, 0);
lean_inc(x_52);
lean_dec(x_47);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_46, 1);
lean_inc(x_54);
lean_dec(x_46);
x_55 = lean_ctor_get(x_47, 0);
lean_inc(x_55);
lean_dec(x_47);
x_56 = lean_ctor_get(x_7, 2);
x_57 = lean_nat_add(x_9, x_56);
lean_dec(x_9);
x_8 = x_55;
x_9 = x_57;
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = x_54;
goto _start;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_array_fget(x_5, x_18);
lean_dec(x_18);
lean_inc(x_16);
lean_inc(x_1);
x_60 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind(x_1, x_2, x_3, x_16, x_59);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_16);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_box(0);
x_64 = lean_unbox(x_62);
lean_dec(x_62);
x_65 = l_Std_Range_forIn_x27_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__2___lambda__1(x_64, x_8, x_63, x_12);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
lean_dec(x_9);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_65);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_65, 0);
lean_dec(x_68);
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
lean_ctor_set(x_65, 0, x_69);
return x_65;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_dec(x_65);
x_71 = lean_ctor_get(x_66, 0);
lean_inc(x_71);
lean_dec(x_66);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_65, 1);
lean_inc(x_73);
lean_dec(x_65);
x_74 = lean_ctor_get(x_66, 0);
lean_inc(x_74);
lean_dec(x_66);
x_75 = lean_ctor_get(x_7, 2);
x_76 = lean_nat_add(x_9, x_75);
lean_dec(x_9);
x_8 = x_74;
x_9 = x_76;
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = x_73;
goto _start;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; 
x_78 = lean_ctor_get(x_60, 1);
lean_inc(x_78);
lean_dec(x_60);
x_79 = lean_ctor_get(x_61, 0);
lean_inc(x_79);
lean_dec(x_61);
x_80 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_80, 0, x_16);
x_81 = lean_unbox(x_79);
lean_dec(x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_81);
x_82 = lean_array_push(x_8, x_80);
x_83 = lean_box(0);
x_84 = lean_unbox(x_78);
lean_dec(x_78);
x_85 = l_Std_Range_forIn_x27_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__2___lambda__1(x_84, x_82, x_83, x_12);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
lean_dec(x_9);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_85, 0);
lean_dec(x_88);
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
lean_dec(x_86);
lean_ctor_set(x_85, 0, x_89);
return x_85;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_85, 1);
lean_inc(x_90);
lean_dec(x_85);
x_91 = lean_ctor_get(x_86, 0);
lean_inc(x_91);
lean_dec(x_86);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_85, 1);
lean_inc(x_93);
lean_dec(x_85);
x_94 = lean_ctor_get(x_86, 0);
lean_inc(x_94);
lean_dec(x_86);
x_95 = lean_ctor_get(x_7, 2);
x_96 = lean_nat_add(x_9, x_95);
lean_dec(x_9);
x_8 = x_94;
x_9 = x_96;
x_10 = lean_box(0);
x_11 = lean_box(0);
x_12 = x_93;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_7, x_6);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
x_12 = lean_array_uget(x_5, x_7);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_1);
x_14 = l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp(x_1, x_13, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = 1;
x_18 = lean_usize_add(x_7, x_17);
lean_inc(x_4);
{
size_t _tmp_6 = x_18;
lean_object* _tmp_7 = x_4;
lean_object* _tmp_8 = x_16;
x_7 = _tmp_6;
x_8 = _tmp_7;
x_9 = _tmp_8;
}
goto _start;
}
else
{
uint8_t x_20; 
lean_dec(x_4);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_14, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_15);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_14, 0, x_25);
return x_14;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_14, 0, x_30);
return x_14;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_ctor_get(x_15, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_33 = x_15;
} else {
 lean_dec_ref(x_15);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_4);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_14);
if (x_39 == 0)
{
return x_14;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_14, 0);
x_41 = lean_ctor_get(x_14, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_14);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = 1;
x_4 = l_Lean_Syntax_getRangeWithTrailing_x3f(x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_String_Range_contains(x_6, x_1, x_3);
lean_dec(x_6);
return x_7;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__2(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Syntax_hasArgs(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__3(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_4 = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(x_3);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_6 = l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_prio(x_5);
x_7 = lean_nat_dec_le(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__2___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__3___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__1___boxed), 2, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__1;
x_10 = l_Lean_Syntax_findStack_x3f(x_2, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; lean_object* x_33; lean_object* x_34; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_13);
x_14 = lean_array_mk(x_13);
x_15 = lean_array_size(x_14);
x_16 = 0;
x_17 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__1(x_15, x_16, x_14);
x_18 = lean_array_get_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_unsigned_to_nat(1u);
lean_inc(x_18);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_20);
x_22 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__2;
x_23 = l_Std_Range_forIn_x27_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__2(x_3, x_4, x_1, x_13, x_17, x_18, x_21, x_22, x_19, lean_box(0), lean_box(0), x_7);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_1);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_array_to_list(x_24);
x_27 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__3;
x_28 = l_List_mergeSort___rarg(x_26, x_27);
x_29 = lean_array_mk(x_28);
x_30 = lean_box(0);
x_31 = lean_box(0);
x_32 = lean_array_size(x_29);
x_33 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__4;
x_34 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__3(x_5, x_29, x_30, x_33, x_29, x_32, x_16, x_33, x_25);
lean_dec(x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
lean_ctor_set(x_34, 0, x_31);
return x_34;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_dec(x_34);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_34);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_34, 0);
lean_dec(x_42);
x_43 = lean_ctor_get(x_36, 0);
lean_inc(x_43);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_43);
return x_34;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_dec(x_34);
x_45 = lean_ctor_get(x_36, 0);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_34);
if (x_47 == 0)
{
return x_34;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_34, 0);
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_34);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
lean_inc(x_1);
x_7 = l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_isPositionInLineComment(x_1, x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5(x_5, x_3, x_1, x_2, x_4, x_8, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Std_Range_forIn_x27_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__2___lambda__1(x_5, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_11 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_12 = l_Array_forIn_x27Unsafe_loop___at_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___spec__3(x_1, x_2, x_3, x_4, x_5, x_10, x_11, x_8, x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__3(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__4(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* initialize_Lean_Server_InfoUtils(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Sort_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Server_FileWorker_SignatureHelp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Server_InfoUtils(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sort_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__2___closed__1 = _init_l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___lambda__2___closed__1);
l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__1 = _init_l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_determineSignatureHelp___closed__1);
l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion___rarg___closed__1 = _init_l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion___rarg___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_CandidateKind_noConfusion___rarg___closed__1);
l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1 = _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1();
lean_mark_persistent(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__1);
l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2 = _init_l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2();
lean_mark_persistent(l___private_Lean_Server_FileWorker_SignatureHelp_0__Lean_Server_FileWorker_SignatureHelp_lineCommentPosition_x3f___closed__2);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___closed__1 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___closed__1);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___closed__2 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__1___closed__2);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__1 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__1);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__2 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__2);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__3 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__3);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__4 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__4);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__5 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__5();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__5);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__6 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__6();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__6);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__7 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__7();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__7);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__8 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__8();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__8);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__9 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__9();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__9);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__10 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__10();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__10);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__11 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__11();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__11);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__12 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__12();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__12);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__13 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__13();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__13);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__14 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__14();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__14);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__15 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__15();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__15);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__16 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__16();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__16);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__17 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__17();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__17);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__18 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__18();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__18);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__19 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__19();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__19);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__20 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__20();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__2___closed__20);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__1 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__1);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__2 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__2);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__3 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__3);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__4 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__3___closed__4);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__4___closed__1 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__4___closed__1);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__4___closed__2 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___lambda__4___closed__2);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f_determineCandidateKind___closed__1);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__1 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__1);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__2 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__2);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__3 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__3);
l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__4 = _init_l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__4();
lean_mark_persistent(l_Lean_Server_FileWorker_SignatureHelp_findSignatureHelp_x3f___lambda__5___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
