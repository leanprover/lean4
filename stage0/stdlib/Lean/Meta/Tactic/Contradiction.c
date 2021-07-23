// Lean compiler output
// Module: Lean.Meta.Tactic.Contradiction
// Imports: Init Lean.Meta.MatchUtil Lean.Meta.Tactic.Assumption Lean.Meta.Tactic.Cases
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
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__3;
static lean_object* l_Lean_Meta_contradiction___closed__2;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__7;
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_elimEmptyInductive_match__3(lean_object*);
lean_object* l_Lean_Meta_elimEmptyInductive___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkSort(lean_object*);
lean_object* l_Lean_Meta_elimEmptyInductive_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_contradictionCore___spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
static lean_object* l_Lean_Meta_contradictionCore___closed__3;
static lean_object* l_Lean_Meta_contradiction___closed__1;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__3;
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_contradictionCore___spec__1___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_contradiction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_Meta_elimEmptyInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_commitWhen___at_Lean_Meta_elimEmptyInductive___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_contradictionCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_commitWhen___at_Lean_Meta_elimEmptyInductive___spec__3___at_Lean_Meta_elimEmptyInductive___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_contradictionCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_contradictionCore___closed__2;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
extern lean_object* l_Lean_levelZero;
lean_object* l_Lean_Meta_contradictionCore_match__2(lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchNot_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__1;
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_contradictionCore_match__3(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_contradiction___closed__3;
lean_object* l_Lean_Meta_contradictionCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_contradictionCore___lambda__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_contradictionCore_match__5(lean_object*);
lean_object* l_Lean_Meta_elimEmptyInductive_match__1(lean_object*);
lean_object* l_Lean_Meta_contradictionCore_match__4(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__2___closed__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__10;
lean_object* l_Lean_Meta_mkAbsurd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_contradictionCore___spec__2___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_findLocalDeclWithType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__2___closed__2;
lean_object* l_Lean_Meta_elimEmptyInductive_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_elimEmptyInductive_match__2(lean_object*);
lean_object* l_Lean_Meta_contradictionCore_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_contradiction(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_contradictionCore___lambda__2___closed__1;
lean_object* l_Lean_Meta_contradictionCore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_contradictionCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_instMonadMetaM;
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Cases_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux(lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__2;
lean_object* l_Lean_Meta_elimEmptyInductive___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_contradictionCore_match__1(lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__1;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__2;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__8;
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__4;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_contradictionCore_match__4___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchNe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__9;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_contradictionCore___spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_contradictionCore_match__3___rarg(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_elimEmptyInductive___lambda__2___closed__1;
uint8_t l_Lean_Expr_isFVar(lean_object*);
static lean_object* l_Lean_Meta_contradictionCore___closed__1;
lean_object* l_Lean_Meta_contradictionCore_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_elimEmptyInductive___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__6;
lean_object* l_Lean_Meta_contradictionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_elimEmptyInductive___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_contradictionCore_match__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_elimEmptyInductive___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_elimEmptyInductive___lambda__2___closed__2;
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_elimEmptyInductive_match__3___rarg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_List_lengthAux___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_elimEmptyInductive___lambda__3___closed__1;
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_contradictionCore___spec__2___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__5;
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_elimEmptyInductive_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_contradictionCore___spec__1___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_elimEmptyInductive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadControlT__1___rarg(lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_contradictionCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_elimEmptyInductive_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Meta_elimEmptyInductive_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_elimEmptyInductive_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_elimEmptyInductive_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_3, x_6);
return x_7;
}
}
}
lean_object* l_Lean_Meta_elimEmptyInductive_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_elimEmptyInductive_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_elimEmptyInductive_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_9 = lean_box(0);
x_10 = lean_apply_1(x_2, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Meta_elimEmptyInductive_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_elimEmptyInductive_match__3___rarg___boxed), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_elimEmptyInductive_match__3___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_elimEmptyInductive_match__3___rarg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_5 < x_4;
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_13 = lean_box(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_array_uget(x_3, x_5);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = l_Lean_Meta_FVarSubst_apply(x_16, x_15);
lean_dec(x_16);
x_18 = l_Lean_Expr_isFVar(x_17);
if (x_18 == 0)
{
size_t x_19; size_t x_20; 
lean_dec(x_17);
x_19 = 1;
x_20 = x_5 + x_19;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = l_Lean_Expr_fvarId_x21(x_17);
lean_dec(x_17);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_24 = l_Lean_Meta_elimEmptyInductive(x_22, x_23, x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; size_t x_28; size_t x_29; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = 1;
x_29 = x_5 + x_28;
x_5 = x_29;
x_11 = x_27;
goto _start;
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
lean_object* x_32; uint8_t x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 0);
lean_dec(x_32);
x_33 = 1;
x_34 = lean_box(x_33);
lean_ctor_set(x_24, 0, x_34);
return x_24;
}
else
{
lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_24, 1);
lean_inc(x_35);
lean_dec(x_24);
x_36 = 1;
x_37 = lean_box(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
return x_24;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_24, 0);
x_41 = lean_ctor_get(x_24, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_24);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__2___closed__1() {
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
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__2___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = x_5 < x_4;
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; uint8_t x_20; lean_object* x_21; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_array_get_size(x_16);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
x_20 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_21 = l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__1(x_1, x_15, x_16, x_18, x_19, x_20, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__2___closed__2;
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__2___closed__2;
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; size_t x_31; size_t x_32; 
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_dec(x_21);
x_31 = 1;
x_32 = x_5 + x_31;
lean_inc(x_2);
{
size_t _tmp_4 = x_32;
lean_object* _tmp_5 = x_2;
lean_object* _tmp_10 = x_30;
x_5 = _tmp_4;
x_6 = _tmp_5;
x_11 = _tmp_10;
}
goto _start;
}
}
else
{
uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_21);
if (x_34 == 0)
{
return x_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_21, 0);
x_36 = lean_ctor_get(x_21, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_21);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
lean_object* l_Lean_commitWhen___at_Lean_Meta_elimEmptyInductive___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = 0;
x_18 = lean_box(x_17);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = 0;
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_10);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_10, 0);
lean_dec(x_24);
x_25 = 1;
x_26 = lean_box(x_25);
lean_ctor_set(x_10, 0, x_26);
return x_10;
}
else
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_10, 1);
lean_inc(x_27);
lean_dec(x_10);
x_28 = 1;
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_10, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_dec(x_10);
x_33 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_32);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_dec(x_35);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
lean_object* l_Lean_commitWhen___at_Lean_Meta_elimEmptyInductive___spec__3___at_Lean_Meta_elimEmptyInductive___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Meta_saveState___rarg(x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_Meta_Cases_cases(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = lean_apply_6(x_3, x_14, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_Meta_SavedState_restore(x_11, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_11);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = 0;
x_24 = lean_box(x_23);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = 0;
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
lean_dec(x_30);
x_31 = 1;
x_32 = lean_box(x_31);
lean_ctor_set(x_16, 0, x_32);
return x_16;
}
else
{
lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_dec(x_16);
x_34 = 1;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_16, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_16, 1);
lean_inc(x_38);
lean_dec(x_16);
x_39 = l_Lean_Meta_SavedState_restore(x_11, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_11);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
lean_ctor_set_tag(x_39, 1);
lean_ctor_set(x_39, 0, x_37);
return x_39;
}
else
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_37);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_3);
x_44 = lean_ctor_get(x_13, 1);
lean_inc(x_44);
lean_dec(x_13);
x_45 = l_Lean_Meta_SavedState_restore(x_11, x_5, x_6, x_7, x_8, x_44);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_11);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
x_48 = 0;
x_49 = lean_box(x_48);
lean_ctor_set(x_45, 0, x_49);
return x_45;
}
else
{
lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
lean_dec(x_45);
x_51 = 0;
x_52 = lean_box(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
}
}
}
lean_object* l_Lean_Meta_elimEmptyInductive___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 1;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_elimEmptyInductive___lambda__2___closed__1() {
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
static lean_object* _init_l_Lean_Meta_elimEmptyInductive___lambda__2___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_elimEmptyInductive___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_elimEmptyInductive___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_array_get_size(x_2);
x_9 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_10 = 0;
x_11 = l_Lean_Meta_elimEmptyInductive___lambda__2___closed__1;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__2(x_1, x_11, x_2, x_9, x_10, x_11, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Meta_elimEmptyInductive___lambda__2___closed__2;
x_17 = lean_box(0);
x_18 = lean_apply_6(x_16, x_17, x_3, x_4, x_5, x_6, x_15);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_12, 0);
lean_dec(x_20);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_21);
return x_12;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_dec(x_12);
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
return x_12;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
static lean_object* _init_l_Lean_Meta_elimEmptyInductive___lambda__3___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_elimEmptyInductive___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_Meta_getLocalDecl(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_LocalDecl_type(x_10);
lean_dec(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Meta_whnfD(x_12, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Expr_getAppFn(x_15);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 4)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_free_object(x_13);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_7, x_16);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_environment_find(x_23, x_18);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; lean_object* x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = 0;
x_26 = lean_box(x_25);
lean_ctor_set(x_19, 0, x_26);
return x_19;
}
else
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
if (lean_obj_tag(x_27) == 5)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_28, 4);
lean_inc(x_29);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_List_lengthAux___rarg(x_29, x_30);
lean_dec(x_29);
x_32 = lean_nat_dec_eq(x_31, x_30);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_28, 2);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_nat_dec_lt(x_30, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = 0;
x_36 = lean_box(x_35);
lean_ctor_set(x_19, 0, x_36);
return x_19;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_free_object(x_19);
x_37 = lean_alloc_closure((void*)(l_Lean_Meta_elimEmptyInductive___lambda__2___boxed), 7, 1);
lean_closure_set(x_37, 0, x_2);
x_38 = l_Lean_Meta_elimEmptyInductive___lambda__3___closed__1;
x_39 = l_Lean_commitWhen___at_Lean_Meta_elimEmptyInductive___spec__3___at_Lean_Meta_elimEmptyInductive___spec__4(x_3, x_1, x_37, x_38, x_4, x_5, x_6, x_7, x_22);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_28);
lean_free_object(x_19);
x_40 = lean_alloc_closure((void*)(l_Lean_Meta_elimEmptyInductive___lambda__2___boxed), 7, 1);
lean_closure_set(x_40, 0, x_2);
x_41 = l_Lean_Meta_elimEmptyInductive___lambda__3___closed__1;
x_42 = l_Lean_commitWhen___at_Lean_Meta_elimEmptyInductive___spec__3___at_Lean_Meta_elimEmptyInductive___spec__4(x_3, x_1, x_40, x_41, x_4, x_5, x_6, x_7, x_22);
return x_42;
}
}
else
{
uint8_t x_43; lean_object* x_44; 
lean_dec(x_27);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = 0;
x_44 = lean_box(x_43);
lean_ctor_set(x_19, 0, x_44);
return x_19;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_19, 0);
x_46 = lean_ctor_get(x_19, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_19);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_environment_find(x_47, x_18);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = 0;
x_50 = lean_box(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_46);
return x_51;
}
else
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_48, 0);
lean_inc(x_52);
lean_dec(x_48);
if (lean_obj_tag(x_52) == 5)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_ctor_get(x_53, 4);
lean_inc(x_54);
x_55 = lean_unsigned_to_nat(0u);
x_56 = l_List_lengthAux___rarg(x_54, x_55);
lean_dec(x_54);
x_57 = lean_nat_dec_eq(x_56, x_55);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_53, 2);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_nat_dec_lt(x_55, x_58);
lean_dec(x_58);
if (x_59 == 0)
{
uint8_t x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_60 = 0;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_46);
return x_62;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_alloc_closure((void*)(l_Lean_Meta_elimEmptyInductive___lambda__2___boxed), 7, 1);
lean_closure_set(x_63, 0, x_2);
x_64 = l_Lean_Meta_elimEmptyInductive___lambda__3___closed__1;
x_65 = l_Lean_commitWhen___at_Lean_Meta_elimEmptyInductive___spec__3___at_Lean_Meta_elimEmptyInductive___spec__4(x_3, x_1, x_63, x_64, x_4, x_5, x_6, x_7, x_46);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_53);
x_66 = lean_alloc_closure((void*)(l_Lean_Meta_elimEmptyInductive___lambda__2___boxed), 7, 1);
lean_closure_set(x_66, 0, x_2);
x_67 = l_Lean_Meta_elimEmptyInductive___lambda__3___closed__1;
x_68 = l_Lean_commitWhen___at_Lean_Meta_elimEmptyInductive___spec__3___at_Lean_Meta_elimEmptyInductive___spec__4(x_3, x_1, x_66, x_67, x_4, x_5, x_6, x_7, x_46);
return x_68;
}
}
else
{
uint8_t x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_52);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = 0;
x_70 = lean_box(x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_46);
return x_71;
}
}
}
}
else
{
uint8_t x_72; lean_object* x_73; 
lean_dec(x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_72 = 0;
x_73 = lean_box(x_72);
lean_ctor_set(x_13, 0, x_73);
return x_13;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_13, 0);
x_75 = lean_ctor_get(x_13, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_13);
x_76 = l_Lean_Expr_getAppFn(x_74);
lean_dec(x_74);
if (lean_obj_tag(x_76) == 4)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_st_ref_get(x_7, x_75);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_79, 0);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_environment_find(x_82, x_77);
if (lean_obj_tag(x_83) == 0)
{
uint8_t x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = 0;
x_85 = lean_box(x_84);
if (lean_is_scalar(x_81)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_81;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_80);
return x_86;
}
else
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
lean_dec(x_83);
if (lean_obj_tag(x_87) == 5)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_ctor_get(x_88, 4);
lean_inc(x_89);
x_90 = lean_unsigned_to_nat(0u);
x_91 = l_List_lengthAux___rarg(x_89, x_90);
lean_dec(x_89);
x_92 = lean_nat_dec_eq(x_91, x_90);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_ctor_get(x_88, 2);
lean_inc(x_93);
lean_dec(x_88);
x_94 = lean_nat_dec_lt(x_90, x_93);
lean_dec(x_93);
if (x_94 == 0)
{
uint8_t x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = 0;
x_96 = lean_box(x_95);
if (lean_is_scalar(x_81)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_81;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_80);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_81);
x_98 = lean_alloc_closure((void*)(l_Lean_Meta_elimEmptyInductive___lambda__2___boxed), 7, 1);
lean_closure_set(x_98, 0, x_2);
x_99 = l_Lean_Meta_elimEmptyInductive___lambda__3___closed__1;
x_100 = l_Lean_commitWhen___at_Lean_Meta_elimEmptyInductive___spec__3___at_Lean_Meta_elimEmptyInductive___spec__4(x_3, x_1, x_98, x_99, x_4, x_5, x_6, x_7, x_80);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_88);
lean_dec(x_81);
x_101 = lean_alloc_closure((void*)(l_Lean_Meta_elimEmptyInductive___lambda__2___boxed), 7, 1);
lean_closure_set(x_101, 0, x_2);
x_102 = l_Lean_Meta_elimEmptyInductive___lambda__3___closed__1;
x_103 = l_Lean_commitWhen___at_Lean_Meta_elimEmptyInductive___spec__3___at_Lean_Meta_elimEmptyInductive___spec__4(x_3, x_1, x_101, x_102, x_4, x_5, x_6, x_7, x_80);
return x_103;
}
}
else
{
uint8_t x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_87);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = 0;
x_105 = lean_box(x_104);
if (lean_is_scalar(x_81)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_81;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_80);
return x_106;
}
}
}
else
{
uint8_t x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_76);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = 0;
x_108 = lean_box(x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_75);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_13);
if (x_110 == 0)
{
return x_13;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_13, 0);
x_112 = lean_ctor_get(x_13, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_13);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_9);
if (x_114 == 0)
{
return x_9;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_9, 0);
x_116 = lean_ctor_get(x_9, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_9);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
lean_object* l_Lean_Meta_elimEmptyInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_inc(x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_elimEmptyInductive___lambda__3), 8, 3);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_1);
x_14 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__1___rarg(x_1, x_13, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
else
{
uint8_t x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_15 = 0;
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
return x_17;
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = lean_unbox(x_6);
lean_dec(x_6);
x_15 = l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__1(x_1, x_2, x_3, x_12, x_13, x_14, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__2(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Lean_Meta_elimEmptyInductive___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_elimEmptyInductive___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_elimEmptyInductive___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_elimEmptyInductive___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_elimEmptyInductive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_elimEmptyInductive(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Meta_contradictionCore_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Meta_contradictionCore_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_contradictionCore_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_contradictionCore_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Meta_contradictionCore_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_contradictionCore_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_contradictionCore_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_apply_3(x_2, x_7, x_8, x_9);
return x_10;
}
}
}
lean_object* l_Lean_Meta_contradictionCore_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_contradictionCore_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_contradictionCore_match__4___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_apply_1(x_3, x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_2, x_5);
return x_6;
}
}
}
lean_object* l_Lean_Meta_contradictionCore_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_contradictionCore_match__4___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_contradictionCore_match__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_2, x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_apply_2(x_3, x_7, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Meta_contradictionCore_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_contradictionCore_match__5___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, size_t x_9, size_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = x_10 < x_9;
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_array_uget(x_8, x_10);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 1);
x_22 = lean_ctor_get(x_11, 0);
lean_dec(x_22);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_21);
lean_inc(x_5);
lean_inc(x_1);
x_23 = l_Std_PersistentArray_forInAux___at_Lean_Meta_contradictionCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_19, x_21, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 0);
lean_dec(x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_11, 0, x_27);
lean_ctor_set(x_23, 0, x_11);
return x_23;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_11, 0, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_11);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
lean_dec(x_21);
x_31 = lean_ctor_get(x_23, 1);
lean_inc(x_31);
lean_dec(x_23);
x_32 = lean_ctor_get(x_24, 0);
lean_inc(x_32);
lean_dec(x_24);
lean_inc(x_7);
lean_ctor_set(x_11, 1, x_32);
lean_ctor_set(x_11, 0, x_7);
x_33 = 1;
x_34 = x_10 + x_33;
x_10 = x_34;
x_16 = x_31;
goto _start;
}
}
else
{
uint8_t x_36; 
lean_free_object(x_11);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
lean_dec(x_11);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_40);
lean_inc(x_5);
lean_inc(x_1);
x_41 = l_Std_PersistentArray_forInAux___at_Lean_Meta_contradictionCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_19, x_40, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_19);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_40);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; size_t x_51; size_t x_52; 
lean_dec(x_40);
x_48 = lean_ctor_get(x_41, 1);
lean_inc(x_48);
lean_dec(x_41);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
lean_dec(x_42);
lean_inc(x_7);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_7);
lean_ctor_set(x_50, 1, x_49);
x_51 = 1;
x_52 = x_10 + x_51;
x_10 = x_52;
x_11 = x_50;
x_16 = x_48;
goto _start;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_40);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_41, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_56 = x_41;
} else {
 lean_dec_ref(x_41);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(1, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Bool");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("false");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__2;
x_2 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__3;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("ofDecideEqFalse");
return x_1;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__5;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__6;
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_levelZero;
x_2 = l_Lean_mkSort(x_1);
return x_2;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__9() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = lean_box(0);
x_3 = lean_box(x_1);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
if (x_1 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_2);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
else
{
uint8_t x_25; 
x_25 = l_Lean_Expr_hasFVar(x_3);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = l_Lean_Expr_hasMVar(x_3);
if (x_26 == 0)
{
lean_object* x_27; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_27 = l_Lean_Meta_mkDecide(x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_28 = lean_ctor_get(x_7, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_ctor_get(x_7, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_7, 2);
lean_inc(x_32);
x_33 = lean_ctor_get(x_7, 3);
lean_inc(x_33);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_35 = 1;
lean_ctor_set_uint8(x_28, 5, x_35);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_31);
lean_ctor_set(x_36, 2, x_32);
lean_ctor_set(x_36, 3, x_33);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_29);
x_37 = l_Lean_Meta_whnf(x_29, x_36, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_41 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__4;
x_42 = l_Lean_Expr_isConstOf(x_39, x_41);
lean_dec(x_39);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_2);
lean_ctor_set(x_37, 0, x_43);
return x_37;
}
else
{
lean_object* x_44; 
lean_free_object(x_37);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_29);
x_44 = l_Lean_Meta_mkEqRefl(x_29, x_7, x_8, x_9, x_10, x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_unsigned_to_nat(0u);
x_48 = l_Lean_Expr_getAppNumArgsAux(x_29, x_47);
x_49 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__8;
lean_inc(x_48);
x_50 = lean_mk_array(x_48, x_49);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_sub(x_48, x_51);
lean_dec(x_48);
x_53 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_29, x_50, x_52);
x_54 = lean_array_push(x_53, x_45);
x_55 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__7;
x_56 = l_Lean_mkAppN(x_55, x_54);
lean_dec(x_54);
lean_inc(x_4);
x_57 = l_Lean_Meta_getMVarType(x_4, x_7, x_8, x_9, x_10, x_46);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_LocalDecl_toExpr(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_61 = l_Lean_Meta_mkAbsurd(x_58, x_60, x_56, x_7, x_8, x_9, x_10, x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Meta_assignExprMVar(x_4, x_62, x_7, x_8, x_9, x_10, x_63);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__9;
x_12 = x_66;
x_13 = x_65;
goto block_22;
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_dec(x_61);
x_68 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__10;
x_12 = x_68;
x_13 = x_67;
goto block_22;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_56);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_69 = lean_ctor_get(x_57, 1);
lean_inc(x_69);
lean_dec(x_57);
x_70 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__10;
x_12 = x_70;
x_13 = x_69;
goto block_22;
}
}
else
{
uint8_t x_71; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_71 = !lean_is_exclusive(x_44);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_44, 0);
lean_dec(x_72);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_2);
lean_ctor_set_tag(x_44, 0);
lean_ctor_set(x_44, 0, x_73);
return x_44;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_44, 1);
lean_inc(x_74);
lean_dec(x_44);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_2);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_77 = lean_ctor_get(x_37, 0);
x_78 = lean_ctor_get(x_37, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_37);
x_79 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__4;
x_80 = l_Lean_Expr_isConstOf(x_77, x_79);
lean_dec(x_77);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_2);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_78);
return x_82;
}
else
{
lean_object* x_83; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_29);
x_83 = l_Lean_Meta_mkEqRefl(x_29, x_7, x_8, x_9, x_10, x_78);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_unsigned_to_nat(0u);
x_87 = l_Lean_Expr_getAppNumArgsAux(x_29, x_86);
x_88 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__8;
lean_inc(x_87);
x_89 = lean_mk_array(x_87, x_88);
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_sub(x_87, x_90);
lean_dec(x_87);
x_92 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_29, x_89, x_91);
x_93 = lean_array_push(x_92, x_84);
x_94 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__7;
x_95 = l_Lean_mkAppN(x_94, x_93);
lean_dec(x_93);
lean_inc(x_4);
x_96 = l_Lean_Meta_getMVarType(x_4, x_7, x_8, x_9, x_10, x_85);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Lean_LocalDecl_toExpr(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_100 = l_Lean_Meta_mkAbsurd(x_97, x_99, x_95, x_7, x_8, x_9, x_10, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Meta_assignExprMVar(x_4, x_101, x_7, x_8, x_9, x_10, x_102);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__9;
x_12 = x_105;
x_13 = x_104;
goto block_22;
}
else
{
lean_object* x_106; lean_object* x_107; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_106 = lean_ctor_get(x_100, 1);
lean_inc(x_106);
lean_dec(x_100);
x_107 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__10;
x_12 = x_107;
x_13 = x_106;
goto block_22;
}
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_95);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_108 = lean_ctor_get(x_96, 1);
lean_inc(x_108);
lean_dec(x_96);
x_109 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__10;
x_12 = x_109;
x_13 = x_108;
goto block_22;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_110 = lean_ctor_get(x_83, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_111 = x_83;
} else {
 lean_dec_ref(x_83);
 x_111 = lean_box(0);
}
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_2);
if (lean_is_scalar(x_111)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_111;
 lean_ctor_set_tag(x_113, 0);
}
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_114 = !lean_is_exclusive(x_37);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_37, 0);
lean_dec(x_115);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_2);
lean_ctor_set_tag(x_37, 0);
lean_ctor_set(x_37, 0, x_116);
return x_37;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_37, 1);
lean_inc(x_117);
lean_dec(x_37);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_2);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
}
else
{
uint8_t x_120; uint8_t x_121; uint8_t x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_120 = lean_ctor_get_uint8(x_28, 0);
x_121 = lean_ctor_get_uint8(x_28, 1);
x_122 = lean_ctor_get_uint8(x_28, 2);
x_123 = lean_ctor_get_uint8(x_28, 3);
x_124 = lean_ctor_get_uint8(x_28, 4);
x_125 = lean_ctor_get_uint8(x_28, 6);
x_126 = lean_ctor_get_uint8(x_28, 7);
x_127 = lean_ctor_get_uint8(x_28, 8);
x_128 = lean_ctor_get_uint8(x_28, 9);
lean_dec(x_28);
x_129 = 1;
x_130 = lean_alloc_ctor(0, 0, 10);
lean_ctor_set_uint8(x_130, 0, x_120);
lean_ctor_set_uint8(x_130, 1, x_121);
lean_ctor_set_uint8(x_130, 2, x_122);
lean_ctor_set_uint8(x_130, 3, x_123);
lean_ctor_set_uint8(x_130, 4, x_124);
lean_ctor_set_uint8(x_130, 5, x_129);
lean_ctor_set_uint8(x_130, 6, x_125);
lean_ctor_set_uint8(x_130, 7, x_126);
lean_ctor_set_uint8(x_130, 8, x_127);
lean_ctor_set_uint8(x_130, 9, x_128);
x_131 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_31);
lean_ctor_set(x_131, 2, x_32);
lean_ctor_set(x_131, 3, x_33);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_29);
x_132 = l_Lean_Meta_whnf(x_29, x_131, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_135 = x_132;
} else {
 lean_dec_ref(x_132);
 x_135 = lean_box(0);
}
x_136 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__4;
x_137 = l_Lean_Expr_isConstOf(x_133, x_136);
lean_dec(x_133);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_2);
if (lean_is_scalar(x_135)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_135;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_134);
return x_139;
}
else
{
lean_object* x_140; 
lean_dec(x_135);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_29);
x_140 = l_Lean_Meta_mkEqRefl(x_29, x_7, x_8, x_9, x_10, x_134);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
x_143 = lean_unsigned_to_nat(0u);
x_144 = l_Lean_Expr_getAppNumArgsAux(x_29, x_143);
x_145 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__8;
lean_inc(x_144);
x_146 = lean_mk_array(x_144, x_145);
x_147 = lean_unsigned_to_nat(1u);
x_148 = lean_nat_sub(x_144, x_147);
lean_dec(x_144);
x_149 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_29, x_146, x_148);
x_150 = lean_array_push(x_149, x_141);
x_151 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__7;
x_152 = l_Lean_mkAppN(x_151, x_150);
lean_dec(x_150);
lean_inc(x_4);
x_153 = l_Lean_Meta_getMVarType(x_4, x_7, x_8, x_9, x_10, x_142);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_156 = l_Lean_LocalDecl_toExpr(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_157 = l_Lean_Meta_mkAbsurd(x_154, x_156, x_152, x_7, x_8, x_9, x_10, x_155);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l_Lean_Meta_assignExprMVar(x_4, x_158, x_7, x_8, x_9, x_10, x_159);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__9;
x_12 = x_162;
x_13 = x_161;
goto block_22;
}
else
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_163 = lean_ctor_get(x_157, 1);
lean_inc(x_163);
lean_dec(x_157);
x_164 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__10;
x_12 = x_164;
x_13 = x_163;
goto block_22;
}
}
else
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_152);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_165 = lean_ctor_get(x_153, 1);
lean_inc(x_165);
lean_dec(x_153);
x_166 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__10;
x_12 = x_166;
x_13 = x_165;
goto block_22;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_167 = lean_ctor_get(x_140, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_168 = x_140;
} else {
 lean_dec_ref(x_140);
 x_168 = lean_box(0);
}
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_2);
if (lean_is_scalar(x_168)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_168;
 lean_ctor_set_tag(x_170, 0);
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_167);
return x_170;
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_29);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_171 = lean_ctor_get(x_132, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_172 = x_132;
} else {
 lean_dec_ref(x_132);
 x_172 = lean_box(0);
}
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_2);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_172;
 lean_ctor_set_tag(x_174, 0);
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_171);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_175 = !lean_is_exclusive(x_27);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
x_176 = lean_ctor_get(x_27, 0);
lean_dec(x_176);
x_177 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_177, 0, x_2);
lean_ctor_set_tag(x_27, 0);
lean_ctor_set(x_27, 0, x_177);
return x_27;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_27, 1);
lean_inc(x_178);
lean_dec(x_27);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_2);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
}
else
{
lean_object* x_181; lean_object* x_182; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_181 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_181, 0, x_2);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_182, 1, x_11);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_2);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_11);
return x_184;
}
}
block_22:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
lean_dec(x_12);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
}
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__1() {
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
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__1;
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_12 = l_Lean_Meta_matchEq_x3f(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1(x_2, x_3, x_1, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_matchConstructorApp_x3f(x_20, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1(x_2, x_3, x_1, x_4, x_5, x_25, x_7, x_8, x_9, x_10, x_24);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
lean_dec(x_22);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
lean_dec(x_23);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_29 = l_Lean_Meta_matchConstructorApp_x3f(x_21, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_box(0);
x_33 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1(x_2, x_3, x_1, x_4, x_5, x_32, x_7, x_8, x_9, x_10, x_31);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_name_eq(x_37, x_39);
lean_dec(x_39);
lean_dec(x_37);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_4);
x_41 = l_Lean_Meta_getMVarType(x_4, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_LocalDecl_toExpr(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_45 = l_Lean_Meta_mkNoConfusion(x_42, x_44, x_7, x_8, x_9, x_10, x_43);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Meta_assignExprMVar(x_4, x_46, x_7, x_8, x_9, x_10, x_47);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__3;
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__3;
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_45);
if (x_55 == 0)
{
return x_45;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_45, 0);
x_57 = lean_ctor_get(x_45, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_45);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_59 = !lean_is_exclusive(x_41);
if (x_59 == 0)
{
return x_41;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_41, 0);
x_61 = lean_ctor_get(x_41, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_41);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_box(0);
x_64 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1(x_2, x_3, x_1, x_4, x_5, x_63, x_7, x_8, x_9, x_10, x_34);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_28);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_29);
if (x_65 == 0)
{
return x_29;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_29, 0);
x_67 = lean_ctor_get(x_29, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_29);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_69 = !lean_is_exclusive(x_22);
if (x_69 == 0)
{
return x_22;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_22, 0);
x_71 = lean_ctor_get(x_22, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_22);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_12);
if (x_73 == 0)
{
return x_12;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_12, 0);
x_75 = lean_ctor_get(x_12, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_12);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_12 = l_Lean_Meta_matchNe_x3f(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_15, x_7, x_8, x_9, x_10, x_14);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_13, 0);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_20);
x_22 = l_Lean_Meta_isExprDefEq(x_20, x_21, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_20);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2(x_1, x_2, x_3, x_4, x_5, x_26, x_7, x_8, x_9, x_10, x_25);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_3);
lean_dec(x_1);
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
lean_inc(x_4);
x_29 = l_Lean_Meta_getMVarType(x_4, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_32 = l_Lean_Meta_mkEqRefl(x_20, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_LocalDecl_toExpr(x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_36 = l_Lean_Meta_mkAbsurd(x_30, x_33, x_35, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Meta_assignExprMVar(x_4, x_37, x_7, x_8, x_9, x_10, x_38);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__3;
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__3;
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_36);
if (x_46 == 0)
{
return x_36;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_36, 0);
x_48 = lean_ctor_get(x_36, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_36);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_50 = !lean_is_exclusive(x_32);
if (x_50 == 0)
{
return x_32;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_32, 0);
x_52 = lean_ctor_get(x_32, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_32);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_29);
if (x_54 == 0)
{
return x_29;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_29, 0);
x_56 = lean_ctor_get(x_29, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_29);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_20);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_22);
if (x_58 == 0)
{
return x_22;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_22, 0);
x_60 = lean_ctor_get(x_22, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_22);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_12);
if (x_62 == 0)
{
return x_12;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_12, 0);
x_64 = lean_ctor_get(x_12, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_12);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_LocalDecl_fvarId(x_1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_14 = l_Lean_Meta_elimEmptyInductive(x_2, x_13, x_3, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__3(x_4, x_5, x_6, x_2, x_1, x_18, x_8, x_9, x_10, x_11, x_17);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_14);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_14, 0);
lean_dec(x_21);
x_22 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__3;
lean_ctor_set(x_14, 0, x_22);
return x_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__3;
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = x_9 < x_8;
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_array_uget(x_7, x_9);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_29 = x_10;
} else {
 lean_dec_ref(x_10);
 x_29 = lean_box(0);
}
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_42; 
lean_inc(x_28);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_28);
x_30 = x_42;
x_31 = x_15;
goto block_41;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_18, 0);
lean_inc(x_43);
lean_dec(x_18);
x_44 = l_Lean_LocalDecl_isAuxDecl(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Lean_LocalDecl_type(x_43);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_45);
x_46 = l_Lean_Meta_matchNot_x3f(x_45, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_5);
lean_inc(x_1);
x_50 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__4(x_43, x_1, x_3, x_45, x_2, x_5, x_49, x_11, x_12, x_13, x_14, x_48);
lean_dec(x_43);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_30 = x_51;
x_31 = x_52;
goto block_41;
}
else
{
uint8_t x_53; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_50);
if (x_53 == 0)
{
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_46, 1);
lean_inc(x_57);
lean_dec(x_46);
x_58 = lean_ctor_get(x_47, 0);
lean_inc(x_58);
lean_dec(x_47);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_59 = l_Lean_Meta_findLocalDeclWithType_x3f(x_58, x_11, x_12, x_13, x_14, x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_5);
lean_inc(x_1);
x_63 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__4(x_43, x_1, x_3, x_45, x_2, x_5, x_62, x_11, x_12, x_13, x_14, x_61);
lean_dec(x_43);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_30 = x_64;
x_31 = x_65;
goto block_41;
}
else
{
uint8_t x_66; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_63);
if (x_66 == 0)
{
return x_63;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_63, 0);
x_68 = lean_ctor_get(x_63, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_63);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_45);
x_70 = lean_ctor_get(x_59, 1);
lean_inc(x_70);
lean_dec(x_59);
x_71 = lean_ctor_get(x_60, 0);
lean_inc(x_71);
lean_dec(x_60);
lean_inc(x_1);
x_72 = l_Lean_Meta_getMVarType(x_1, x_11, x_12, x_13, x_14, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_mkFVar(x_71);
x_76 = l_Lean_LocalDecl_toExpr(x_43);
lean_dec(x_43);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_77 = l_Lean_Meta_mkAbsurd(x_73, x_75, x_76, x_11, x_12, x_13, x_14, x_74);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_1);
x_80 = l_Lean_Meta_assignExprMVar(x_1, x_78, x_11, x_12, x_13, x_14, x_79);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__3;
x_30 = x_82;
x_31 = x_81;
goto block_41;
}
else
{
uint8_t x_83; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_77);
if (x_83 == 0)
{
return x_77;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_77, 0);
x_85 = lean_ctor_get(x_77, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_77);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_71);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_72);
if (x_87 == 0)
{
return x_72;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_72, 0);
x_89 = lean_ctor_get(x_72, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_72);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_59);
if (x_91 == 0)
{
return x_59;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_59, 0);
x_93 = lean_ctor_get(x_59, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_59);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_45);
lean_dec(x_43);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_46);
if (x_95 == 0)
{
return x_46;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_46, 0);
x_97 = lean_ctor_get(x_46, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_46);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
else
{
lean_object* x_99; 
lean_dec(x_43);
lean_inc(x_5);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_5);
x_30 = x_99;
x_31 = x_15;
goto block_41;
}
}
block_27:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; size_t x_24; size_t x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = 1;
x_25 = x_9 + x_24;
x_9 = x_25;
x_10 = x_23;
x_15 = x_20;
goto _start;
}
}
block_41:
{
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_30);
if (lean_is_scalar(x_29)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_29;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_19 = x_34;
x_20 = x_31;
goto block_27;
}
else
{
uint8_t x_35; 
lean_dec(x_28);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_6);
if (lean_is_scalar(x_29)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_29;
}
lean_ctor_set(x_37, 0, x_6);
lean_ctor_set(x_37, 1, x_36);
lean_ctor_set(x_30, 0, x_37);
x_19 = x_30;
x_20 = x_31;
goto block_27;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_30, 0);
lean_inc(x_38);
lean_dec(x_30);
lean_inc(x_6);
if (lean_is_scalar(x_29)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_29;
}
lean_ctor_set(x_39, 0, x_6);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_19 = x_40;
x_20 = x_31;
goto block_27;
}
}
}
}
}
}
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_contradictionCore___spec__2___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_contradictionCore___spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_8);
x_17 = lean_array_get_size(x_14);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_15, x_14, x_18, x_19, x_16, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_box(0);
x_26 = l_Std_PersistentArray_forInAux___at_Lean_Meta_contradictionCore___spec__2___lambda__1(x_24, x_25, x_9, x_10, x_11, x_12, x_23);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_21);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_27 = !lean_is_exclusive(x_20);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_20, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_22, 0);
lean_inc(x_29);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_ctor_get(x_22, 0);
lean_inc(x_31);
lean_dec(x_22);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_33 = !lean_is_exclusive(x_20);
if (x_33 == 0)
{
return x_20;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_20, 0);
x_35 = lean_ctor_get(x_20, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_20);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_7, 0);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_8);
x_40 = lean_array_get_size(x_37);
x_41 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_42 = 0;
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_43 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4(x_1, x_2, x_3, x_4, x_5, x_38, x_37, x_41, x_42, x_39, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_dec(x_44);
x_48 = lean_box(0);
x_49 = l_Std_PersistentArray_forInAux___at_Lean_Meta_contradictionCore___spec__2___lambda__1(x_47, x_48, x_9, x_10, x_11, x_12, x_46);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_50 = !lean_is_exclusive(x_43);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_43, 0);
lean_dec(x_51);
x_52 = lean_ctor_get(x_45, 0);
lean_inc(x_52);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_52);
return x_43;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
lean_dec(x_43);
x_54 = lean_ctor_get(x_45, 0);
lean_inc(x_54);
lean_dec(x_45);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_56 = !lean_is_exclusive(x_43);
if (x_56 == 0)
{
return x_43;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_43, 0);
x_58 = lean_ctor_get(x_43, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_43);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__5(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, size_t x_8, size_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = x_9 < x_8;
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_array_uget(x_7, x_9);
x_28 = lean_ctor_get(x_10, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_29 = x_10;
} else {
 lean_dec_ref(x_10);
 x_29 = lean_box(0);
}
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_47; 
lean_inc(x_28);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_28);
x_30 = x_47;
x_31 = x_15;
goto block_46;
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_18, 0);
lean_inc(x_48);
lean_dec(x_18);
x_49 = l_Lean_LocalDecl_isAuxDecl(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Lean_LocalDecl_type(x_48);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_50);
x_51 = l_Lean_Meta_matchNot_x3f(x_50, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_5);
lean_inc(x_1);
x_55 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__4(x_48, x_1, x_3, x_50, x_2, x_5, x_54, x_11, x_12, x_13, x_14, x_53);
lean_dec(x_48);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_30 = x_56;
x_31 = x_57;
goto block_46;
}
else
{
uint8_t x_58; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_55);
if (x_58 == 0)
{
return x_55;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_55, 0);
x_60 = lean_ctor_get(x_55, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_55);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_51, 1);
lean_inc(x_62);
lean_dec(x_51);
x_63 = lean_ctor_get(x_52, 0);
lean_inc(x_63);
lean_dec(x_52);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_64 = l_Lean_Meta_findLocalDeclWithType_x3f(x_63, x_11, x_12, x_13, x_14, x_62);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_box(0);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_5);
lean_inc(x_1);
x_68 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__4(x_48, x_1, x_3, x_50, x_2, x_5, x_67, x_11, x_12, x_13, x_14, x_66);
lean_dec(x_48);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_30 = x_69;
x_31 = x_70;
goto block_46;
}
else
{
uint8_t x_71; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
return x_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_68, 0);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_68);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_50);
x_75 = lean_ctor_get(x_64, 1);
lean_inc(x_75);
lean_dec(x_64);
x_76 = lean_ctor_get(x_65, 0);
lean_inc(x_76);
lean_dec(x_65);
lean_inc(x_1);
x_77 = l_Lean_Meta_getMVarType(x_1, x_11, x_12, x_13, x_14, x_75);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_mkFVar(x_76);
x_81 = l_Lean_LocalDecl_toExpr(x_48);
lean_dec(x_48);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_82 = l_Lean_Meta_mkAbsurd(x_78, x_80, x_81, x_11, x_12, x_13, x_14, x_79);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_1);
x_85 = l_Lean_Meta_assignExprMVar(x_1, x_83, x_11, x_12, x_13, x_14, x_84);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_87 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__3;
x_30 = x_87;
x_31 = x_86;
goto block_46;
}
else
{
uint8_t x_88; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_82);
if (x_88 == 0)
{
return x_82;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_82, 0);
x_90 = lean_ctor_get(x_82, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_82);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_76);
lean_dec(x_48);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_77);
if (x_92 == 0)
{
return x_77;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_77, 0);
x_94 = lean_ctor_get(x_77, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_77);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_64);
if (x_96 == 0)
{
return x_64;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_64, 0);
x_98 = lean_ctor_get(x_64, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_64);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_51);
if (x_100 == 0)
{
return x_51;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_51, 0);
x_102 = lean_ctor_get(x_51, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_51);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
else
{
lean_object* x_104; 
lean_dec(x_48);
lean_inc(x_5);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_5);
x_30 = x_104;
x_31 = x_15;
goto block_46;
}
}
block_27:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
else
{
lean_object* x_23; size_t x_24; size_t x_25; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = 1;
x_25 = x_9 + x_24;
x_9 = x_25;
x_10 = x_23;
x_15 = x_20;
goto _start;
}
}
block_46:
{
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 0);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
if (lean_is_scalar(x_29)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_29;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_28);
lean_ctor_set(x_30, 0, x_35);
x_19 = x_30;
x_20 = x_31;
goto block_27;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
if (lean_is_scalar(x_29)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_29;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_28);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_19 = x_39;
x_20 = x_31;
goto block_27;
}
}
else
{
uint8_t x_40; 
lean_dec(x_28);
x_40 = !lean_is_exclusive(x_30);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_6);
if (lean_is_scalar(x_29)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_29;
}
lean_ctor_set(x_42, 0, x_6);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_30, 0, x_42);
x_19 = x_30;
x_20 = x_31;
goto block_27;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_30, 0);
lean_inc(x_43);
lean_dec(x_30);
lean_inc(x_6);
if (lean_is_scalar(x_29)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_29;
}
lean_ctor_set(x_44, 0, x_6);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_19 = x_45;
x_20 = x_31;
goto block_27;
}
}
}
}
}
}
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_contradictionCore___spec__1___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_contradictionCore___spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_5);
lean_inc(x_1);
x_14 = l_Std_PersistentArray_forInAux___at_Lean_Meta_contradictionCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_7, x_13, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_ctor_get(x_6, 1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = lean_array_get_size(x_24);
x_28 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_29 = 0;
x_30 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__5(x_1, x_2, x_3, x_4, x_5, x_25, x_24, x_28, x_29, x_26, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
lean_ctor_set(x_30, 0, x_35);
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_31);
x_39 = !lean_is_exclusive(x_30);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_30, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_41);
return x_30;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
lean_dec(x_30);
x_43 = lean_ctor_get(x_32, 0);
lean_inc(x_43);
lean_dec(x_32);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_30);
if (x_45 == 0)
{
return x_30;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_30, 0);
x_47 = lean_ctor_get(x_30, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_30);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
return x_14;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_14, 0);
x_51 = lean_ctor_get(x_14, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_14);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
lean_object* l_Lean_Meta_contradictionCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 0;
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_contradictionCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_contradictionCore___lambda__1___boxed), 6, 0);
return x_1;
}
}
lean_object* l_Lean_Meta_contradictionCore___lambda__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_Meta_checkNotAssigned(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Meta_elimEmptyInductive___lambda__2___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Std_PersistentArray_forIn___at_Lean_Meta_contradictionCore___spec__1(x_1, x_3, x_4, x_5, x_15, x_14, x_15, x_6, x_7, x_8, x_9, x_12);
lean_dec(x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = l_Lean_Meta_contradictionCore___lambda__2___closed__1;
x_21 = lean_box(0);
x_22 = lean_apply_6(x_20, x_21, x_6, x_7, x_8, x_9, x_19);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_23 = !lean_is_exclusive(x_16);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_16, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_18, 0);
lean_inc(x_25);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_25);
return x_16;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_dec(x_16);
x_27 = lean_ctor_get(x_18, 0);
lean_inc(x_27);
lean_dec(x_18);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_16);
if (x_29 == 0)
{
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 0);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_16);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_11);
if (x_33 == 0)
{
return x_11;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_11, 0);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_11);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
static lean_object* _init_l_Lean_Meta_contradictionCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Meta_instMonadMetaM;
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_instMonadControlT__1___rarg(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_contradictionCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("contradiction");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_contradictionCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_contradictionCore___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_contradictionCore(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Meta_contradictionCore___closed__3;
x_10 = l_Lean_Meta_contradictionCore___closed__1;
x_11 = lean_box(x_2);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_contradictionCore___lambda__2___boxed), 10, 5);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_9);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_3);
lean_closure_set(x_12, 4, x_10);
x_13 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__1___rarg(x_1, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_19 = lean_unbox_usize(x_10);
lean_dec(x_10);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__3(x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_18, x_19, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_20;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__3(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__4(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_14;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_18 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_17, x_18, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_contradictionCore___spec__2___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_PersistentArray_forInAux___at_Lean_Meta_contradictionCore___spec__2___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentArray_forInAux___at_Lean_Meta_contradictionCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Std_PersistentArray_forInAux___at_Lean_Meta_contradictionCore___spec__2(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox_usize(x_8);
lean_dec(x_8);
x_18 = lean_unbox_usize(x_9);
lean_dec(x_9);
x_19 = l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__5(x_1, x_16, x_3, x_4, x_5, x_6, x_7, x_17, x_18, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_contradictionCore___spec__1___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_PersistentArray_forIn___at_Lean_Meta_contradictionCore___spec__1___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l_Std_PersistentArray_forIn___at_Lean_Meta_contradictionCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = l_Std_PersistentArray_forIn___at_Lean_Meta_contradictionCore___spec__1(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
return x_14;
}
}
lean_object* l_Lean_Meta_contradictionCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_contradictionCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_contradictionCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Meta_contradictionCore___lambda__2(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
lean_object* l_Lean_Meta_contradictionCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_contradictionCore(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_contradiction___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_contradiction___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_contradiction___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_contradiction___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_contradiction___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_contradiction(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l_Lean_Meta_contradictionCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Meta_contradictionCore___closed__3;
x_14 = l_Lean_Meta_contradiction___closed__3;
x_15 = lean_box(0);
x_16 = l_Lean_Meta_throwTacticEx___rarg(x_13, x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_9, 0, x_19);
return x_9;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_9, 1);
lean_inc(x_20);
lean_dec(x_9);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Lean_Meta_contradiction___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_contradiction(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_MatchUtil(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assumption(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Cases(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Contradiction(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assumption(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_elimEmptyInductive___spec__2___closed__2);
l_Lean_Meta_elimEmptyInductive___lambda__2___closed__1 = _init_l_Lean_Meta_elimEmptyInductive___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_elimEmptyInductive___lambda__2___closed__1);
l_Lean_Meta_elimEmptyInductive___lambda__2___closed__2 = _init_l_Lean_Meta_elimEmptyInductive___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_elimEmptyInductive___lambda__2___closed__2);
l_Lean_Meta_elimEmptyInductive___lambda__3___closed__1 = _init_l_Lean_Meta_elimEmptyInductive___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_elimEmptyInductive___lambda__3___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__3);
l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__4 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__4();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__4);
l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__5 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__5();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__5);
l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__6 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__6();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__6);
l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__7 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__7();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__7);
l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__8 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__8();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__8);
l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__9 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__9();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__9);
l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__10 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__10();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__1___closed__10);
l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__1 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__1();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__1);
l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__2 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__2();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__2);
l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__3 = _init_l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__3();
lean_mark_persistent(l_Array_forInUnsafe_loop___at_Lean_Meta_contradictionCore___spec__4___lambda__2___closed__3);
l_Lean_Meta_contradictionCore___lambda__2___closed__1 = _init_l_Lean_Meta_contradictionCore___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_contradictionCore___lambda__2___closed__1);
l_Lean_Meta_contradictionCore___closed__1 = _init_l_Lean_Meta_contradictionCore___closed__1();
lean_mark_persistent(l_Lean_Meta_contradictionCore___closed__1);
l_Lean_Meta_contradictionCore___closed__2 = _init_l_Lean_Meta_contradictionCore___closed__2();
lean_mark_persistent(l_Lean_Meta_contradictionCore___closed__2);
l_Lean_Meta_contradictionCore___closed__3 = _init_l_Lean_Meta_contradictionCore___closed__3();
lean_mark_persistent(l_Lean_Meta_contradictionCore___closed__3);
l_Lean_Meta_contradiction___closed__1 = _init_l_Lean_Meta_contradiction___closed__1();
lean_mark_persistent(l_Lean_Meta_contradiction___closed__1);
l_Lean_Meta_contradiction___closed__2 = _init_l_Lean_Meta_contradiction___closed__2();
lean_mark_persistent(l_Lean_Meta_contradiction___closed__2);
l_Lean_Meta_contradiction___closed__3 = _init_l_Lean_Meta_contradiction___closed__3();
lean_mark_persistent(l_Lean_Meta_contradiction___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
