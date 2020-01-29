// Lean compiler output
// Module: Init.Lean.Meta.Tactic.Apply
// Imports: Init.Lean.Util.FindMVar Init.Lean.Meta.Message Init.Lean.Meta.ExprDefEq Init.Lean.Meta.SynthInstance Init.Lean.Meta.Tactic.Util
#include "runtime/lean.h"
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
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___closed__1;
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Name_eraseMacroScopes(lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fswap(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*);
lean_object* l_List_append___rarg(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_getAppFn___main(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_metavar_ctx_is_expr_assigned(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2;
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_apply___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l_Array_shrink___main___rarg(lean_object*, lean_object*);
lean_object* l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_apply___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_renameMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__3;
uint8_t l_coeDecidableEq(uint8_t);
lean_object* l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__1;
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__5;
extern uint8_t l_String_posOfAux___main___closed__2;
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
extern uint8_t l_String_posOfAux___main___closed__1;
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError(lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__6;
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_Lean_BinderInfo_inhabited;
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__2;
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__8;
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_apply___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__4;
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
extern lean_object* l_Lean_Expr_Inhabited;
lean_object* l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__7;
lean_object* l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__3;
uint8_t l_Lean_LocalInstance_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst___closed__1;
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_array_get_size(x_1);
x_6 = l_Lean_Expr_getAppFn___main(x_2);
x_7 = l_Lean_Expr_isMVar(x_6);
lean_dec(x_6);
x_8 = lean_box(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
return x_10;
}
}
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___lambda__1___boxed), 4, 0);
return x_1;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = 2;
lean_ctor_set_uint8(x_5, sizeof(void*)*1 + 6, x_7);
x_8 = l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___closed__1;
x_9 = l_Lean_Meta_forallTelescopeReducing___rarg(x_1, x_8, x_2, x_3);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
x_12 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_13 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 2);
x_14 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 3);
x_15 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 4);
x_16 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 5);
lean_inc(x_10);
lean_dec(x_5);
x_17 = 2;
x_18 = lean_alloc_ctor(0, 1, 7);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_11);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 1, x_12);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 2, x_13);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 3, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 4, x_15);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 5, x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*1 + 6, x_17);
lean_ctor_set(x_2, 0, x_18);
x_19 = l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___closed__1;
x_20 = l_Lean_Meta_forallTelescopeReducing___rarg(x_1, x_19, x_2, x_3);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_ctor_get(x_2, 1);
x_23 = lean_ctor_get(x_2, 2);
x_24 = lean_ctor_get(x_2, 3);
x_25 = lean_ctor_get(x_2, 4);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_2);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_21, sizeof(void*)*1);
x_28 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 1);
x_29 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 2);
x_30 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 3);
x_31 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 4);
x_32 = lean_ctor_get_uint8(x_21, sizeof(void*)*1 + 5);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_33 = x_21;
} else {
 lean_dec_ref(x_21);
 x_33 = lean_box(0);
}
x_34 = 2;
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 1, 7);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_27);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 1, x_28);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 2, x_29);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 3, x_30);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 4, x_31);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 5, x_32);
lean_ctor_set_uint8(x_35, sizeof(void*)*1 + 6, x_34);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_36, 2, x_23);
lean_ctor_set(x_36, 3, x_24);
lean_ctor_set(x_36, 4, x_25);
x_37 = l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___closed__1;
x_38 = l_Lean_Meta_forallTelescopeReducing___rarg(x_1, x_37, x_36, x_3);
return x_38;
}
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_4);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("apply");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to unify");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("with");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_6, 0, x_2);
x_7 = l_Lean_indentExpr(x_6);
x_8 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__5;
x_9 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
x_10 = l_Lean_MessageData_ofList___closed__3;
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__8;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = l_Lean_indentExpr(x_14);
x_16 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2;
x_18 = l_Lean_Meta_throwTacticEx___rarg(x_17, x_1, x_16, x_4, x_5);
return x_18;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___boxed), 5, 0);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* _init_l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("failed to assign synthesized instance");
return x_1;
}
}
lean_object* _init_l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_5, x_10);
lean_dec(x_5);
x_12 = lean_nat_sub(x_4, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = l_Lean_BinderInfo_inhabited;
x_15 = lean_box(x_14);
x_16 = lean_array_get(x_15, x_3, x_13);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
x_18 = l_Lean_BinderInfo_isInstImplicit(x_17);
x_19 = l_coeDecidableEq(x_18);
if (x_19 == 0)
{
lean_dec(x_13);
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_Expr_Inhabited;
x_22 = lean_array_get(x_21, x_2, x_13);
lean_dec(x_13);
lean_inc(x_6);
lean_inc(x_22);
x_23 = l_Lean_Meta_inferType(x_22, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_6);
x_26 = l_Lean_Meta_synthInstance(x_24, x_6, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_6);
x_29 = l_Lean_Meta_isExprDefEq(x_22, x_27, x_6, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_11);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2;
x_34 = l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__3;
x_35 = l_Lean_Meta_throwTacticEx___rarg(x_33, x_1, x_34, x_6, x_32);
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_dec(x_29);
x_5 = x_11;
x_7 = x_40;
goto _start;
}
}
else
{
uint8_t x_42; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_29);
if (x_42 == 0)
{
return x_29;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_29, 0);
x_44 = lean_ctor_get(x_29, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_29);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_26);
if (x_46 == 0)
{
return x_26;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_26, 0);
x_48 = lean_ctor_get(x_26, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_26);
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
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_23);
if (x_50 == 0)
{
return x_23;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_23, 0);
x_52 = lean_ctor_get(x_23, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_23);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_7);
return x_55;
}
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_array_get_size(x_2);
lean_inc(x_6);
x_7 = l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1(x_1, x_2, x_3, x_6, x_6, x_4, x_5);
lean_dec(x_6);
return x_7;
}
}
lean_object* l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_5, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_5, x_10);
lean_dec(x_5);
x_12 = lean_nat_sub(x_4, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = l_Lean_Expr_Inhabited;
x_15 = lean_array_get(x_14, x_1, x_13);
x_16 = l_Lean_Expr_mvarId_x21(x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_inc(x_16);
x_18 = lean_metavar_ctx_is_expr_assigned(x_17, x_16);
if (x_18 == 0)
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; 
x_19 = l_Lean_BinderInfo_inhabited;
x_20 = lean_box(x_19);
x_21 = lean_array_get(x_20, x_2, x_13);
lean_dec(x_13);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
x_23 = l_Lean_BinderInfo_isInstImplicit(x_22);
x_24 = l_coeDecidableEq(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_inc(x_16);
x_25 = l_Lean_Meta_getMVarTag(x_16, x_6, x_7);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Name_eraseMacroScopes(x_26);
lean_dec(x_26);
x_29 = l_Lean_Name_append___main(x_3, x_28);
x_30 = l_Lean_Meta_renameMVar(x_16, x_29, x_6, x_27);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_5 = x_11;
x_7 = x_31;
goto _start;
}
else
{
uint8_t x_33; 
lean_dec(x_16);
lean_dec(x_11);
x_33 = !lean_is_exclusive(x_25);
if (x_33 == 0)
{
return x_25;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_25, 0);
x_35 = lean_ctor_get(x_25, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_25);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_dec(x_16);
x_5 = x_11;
goto _start;
}
}
else
{
lean_dec(x_16);
lean_dec(x_13);
x_5 = x_11;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_5);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_7);
return x_40;
}
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_getMVarTag(x_1, x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_Name_isAnonymous(x_8);
x_11 = l_coeDecidableEq(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_free_object(x_6);
x_12 = lean_array_get_size(x_2);
lean_inc(x_12);
x_13 = l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag___spec__1(x_2, x_3, x_8, x_12, x_12, x_4, x_9);
lean_dec(x_12);
lean_dec(x_8);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_8);
x_14 = lean_box(0);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_6);
x_17 = l_Lean_Name_isAnonymous(x_15);
x_18 = l_coeDecidableEq(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_array_get_size(x_2);
lean_inc(x_19);
x_20 = l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag___spec__1(x_2, x_3, x_15, x_19, x_19, x_4, x_16);
lean_dec(x_19);
lean_dec(x_15);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_15);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_6);
if (x_23 == 0)
{
return x_6;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_6);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
lean_object* l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Expr_mvarId_x21(x_1);
x_6 = lean_name_eq(x_4, x_5);
lean_dec(x_5);
x_7 = l_coeDecidableEq(x_6);
if (x_7 == 0)
{
return x_3;
}
else
{
lean_object* x_8; 
lean_inc(x_4);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_4);
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = l_String_posOfAux___main___closed__1;
if (x_10 == 0)
{
return x_3;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
lean_inc(x_9);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_13; 
lean_dec(x_3);
lean_inc(x_9);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_9);
return x_13;
}
}
}
}
case 5:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_23; 
x_23 = l_Lean_Expr_hasMVar(x_14);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_String_posOfAux___main___closed__2;
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_14, x_3);
if (lean_obj_tag(x_25) == 0)
{
x_16 = x_25;
goto block_22;
}
else
{
x_2 = x_15;
x_3 = x_25;
goto _start;
}
}
else
{
x_16 = x_3;
goto block_22;
}
}
else
{
uint8_t x_27; 
x_27 = l_String_posOfAux___main___closed__1;
if (x_27 == 0)
{
lean_object* x_28; 
x_28 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_14, x_3);
if (lean_obj_tag(x_28) == 0)
{
x_16 = x_28;
goto block_22;
}
else
{
uint8_t x_29; 
x_29 = l_String_posOfAux___main___closed__2;
if (x_29 == 0)
{
x_2 = x_15;
x_3 = x_28;
goto _start;
}
else
{
return x_28;
}
}
}
else
{
x_16 = x_3;
goto block_22;
}
}
}
else
{
uint8_t x_31; 
x_31 = l_String_posOfAux___main___closed__2;
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_14, x_3);
if (lean_obj_tag(x_32) == 0)
{
x_16 = x_32;
goto block_22;
}
else
{
x_2 = x_15;
x_3 = x_32;
goto _start;
}
}
else
{
return x_3;
}
}
block_22:
{
uint8_t x_17; 
x_17 = l_Lean_Expr_hasMVar(x_15);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_String_posOfAux___main___closed__2;
if (x_18 == 0)
{
x_2 = x_15;
x_3 = x_16;
goto _start;
}
else
{
return x_16;
}
}
else
{
uint8_t x_20; 
x_20 = l_String_posOfAux___main___closed__1;
if (x_20 == 0)
{
x_2 = x_15;
x_3 = x_16;
goto _start;
}
else
{
return x_16;
}
}
}
}
case 6:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_2, 1);
x_35 = lean_ctor_get(x_2, 2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Expr_hasMVar(x_34);
if (x_43 == 0)
{
uint8_t x_44; 
x_44 = l_String_posOfAux___main___closed__2;
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_34, x_3);
if (lean_obj_tag(x_45) == 0)
{
x_36 = x_45;
goto block_42;
}
else
{
x_2 = x_35;
x_3 = x_45;
goto _start;
}
}
else
{
x_36 = x_3;
goto block_42;
}
}
else
{
uint8_t x_47; 
x_47 = l_String_posOfAux___main___closed__1;
if (x_47 == 0)
{
lean_object* x_48; 
x_48 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_34, x_3);
if (lean_obj_tag(x_48) == 0)
{
x_36 = x_48;
goto block_42;
}
else
{
uint8_t x_49; 
x_49 = l_String_posOfAux___main___closed__2;
if (x_49 == 0)
{
x_2 = x_35;
x_3 = x_48;
goto _start;
}
else
{
return x_48;
}
}
}
else
{
x_36 = x_3;
goto block_42;
}
}
}
else
{
uint8_t x_51; 
x_51 = l_String_posOfAux___main___closed__2;
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_34, x_3);
if (lean_obj_tag(x_52) == 0)
{
x_36 = x_52;
goto block_42;
}
else
{
x_2 = x_35;
x_3 = x_52;
goto _start;
}
}
else
{
return x_3;
}
}
block_42:
{
uint8_t x_37; 
x_37 = l_Lean_Expr_hasMVar(x_35);
if (x_37 == 0)
{
uint8_t x_38; 
x_38 = l_String_posOfAux___main___closed__2;
if (x_38 == 0)
{
x_2 = x_35;
x_3 = x_36;
goto _start;
}
else
{
return x_36;
}
}
else
{
uint8_t x_40; 
x_40 = l_String_posOfAux___main___closed__1;
if (x_40 == 0)
{
x_2 = x_35;
x_3 = x_36;
goto _start;
}
else
{
return x_36;
}
}
}
}
case 7:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_2, 1);
x_55 = lean_ctor_get(x_2, 2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_63; 
x_63 = l_Lean_Expr_hasMVar(x_54);
if (x_63 == 0)
{
uint8_t x_64; 
x_64 = l_String_posOfAux___main___closed__2;
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_54, x_3);
if (lean_obj_tag(x_65) == 0)
{
x_56 = x_65;
goto block_62;
}
else
{
x_2 = x_55;
x_3 = x_65;
goto _start;
}
}
else
{
x_56 = x_3;
goto block_62;
}
}
else
{
uint8_t x_67; 
x_67 = l_String_posOfAux___main___closed__1;
if (x_67 == 0)
{
lean_object* x_68; 
x_68 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_54, x_3);
if (lean_obj_tag(x_68) == 0)
{
x_56 = x_68;
goto block_62;
}
else
{
uint8_t x_69; 
x_69 = l_String_posOfAux___main___closed__2;
if (x_69 == 0)
{
x_2 = x_55;
x_3 = x_68;
goto _start;
}
else
{
return x_68;
}
}
}
else
{
x_56 = x_3;
goto block_62;
}
}
}
else
{
uint8_t x_71; 
x_71 = l_String_posOfAux___main___closed__2;
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_54, x_3);
if (lean_obj_tag(x_72) == 0)
{
x_56 = x_72;
goto block_62;
}
else
{
x_2 = x_55;
x_3 = x_72;
goto _start;
}
}
else
{
return x_3;
}
}
block_62:
{
uint8_t x_57; 
x_57 = l_Lean_Expr_hasMVar(x_55);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = l_String_posOfAux___main___closed__2;
if (x_58 == 0)
{
x_2 = x_55;
x_3 = x_56;
goto _start;
}
else
{
return x_56;
}
}
else
{
uint8_t x_60; 
x_60 = l_String_posOfAux___main___closed__1;
if (x_60 == 0)
{
x_2 = x_55;
x_3 = x_56;
goto _start;
}
else
{
return x_56;
}
}
}
}
case 8:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_84; lean_object* x_96; 
x_74 = lean_ctor_get(x_2, 1);
x_75 = lean_ctor_get(x_2, 2);
x_76 = lean_ctor_get(x_2, 3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_101; 
x_101 = l_Lean_Expr_hasMVar(x_74);
if (x_101 == 0)
{
uint8_t x_102; 
x_102 = l_String_posOfAux___main___closed__2;
if (x_102 == 0)
{
lean_object* x_103; 
x_103 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_74, x_3);
if (lean_obj_tag(x_103) == 0)
{
x_84 = x_103;
goto block_95;
}
else
{
x_96 = x_103;
goto block_100;
}
}
else
{
x_84 = x_3;
goto block_95;
}
}
else
{
uint8_t x_104; 
x_104 = l_String_posOfAux___main___closed__1;
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_74, x_3);
if (lean_obj_tag(x_105) == 0)
{
x_84 = x_105;
goto block_95;
}
else
{
x_96 = x_105;
goto block_100;
}
}
else
{
x_84 = x_3;
goto block_95;
}
}
}
else
{
uint8_t x_106; 
x_106 = l_String_posOfAux___main___closed__2;
if (x_106 == 0)
{
lean_object* x_107; 
x_107 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_74, x_3);
if (lean_obj_tag(x_107) == 0)
{
x_84 = x_107;
goto block_95;
}
else
{
x_96 = x_107;
goto block_100;
}
}
else
{
x_96 = x_3;
goto block_100;
}
}
block_83:
{
uint8_t x_78; 
x_78 = l_Lean_Expr_hasMVar(x_76);
if (x_78 == 0)
{
uint8_t x_79; 
x_79 = l_String_posOfAux___main___closed__2;
if (x_79 == 0)
{
x_2 = x_76;
x_3 = x_77;
goto _start;
}
else
{
return x_77;
}
}
else
{
uint8_t x_81; 
x_81 = l_String_posOfAux___main___closed__1;
if (x_81 == 0)
{
x_2 = x_76;
x_3 = x_77;
goto _start;
}
else
{
return x_77;
}
}
}
block_95:
{
uint8_t x_85; 
x_85 = l_Lean_Expr_hasMVar(x_75);
if (x_85 == 0)
{
uint8_t x_86; 
x_86 = l_String_posOfAux___main___closed__2;
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_75, x_84);
if (lean_obj_tag(x_87) == 0)
{
x_77 = x_87;
goto block_83;
}
else
{
x_2 = x_76;
x_3 = x_87;
goto _start;
}
}
else
{
if (lean_obj_tag(x_84) == 0)
{
x_77 = x_84;
goto block_83;
}
else
{
return x_84;
}
}
}
else
{
uint8_t x_89; 
x_89 = l_String_posOfAux___main___closed__1;
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_75, x_84);
if (lean_obj_tag(x_90) == 0)
{
x_77 = x_90;
goto block_83;
}
else
{
uint8_t x_91; 
x_91 = l_String_posOfAux___main___closed__2;
if (x_91 == 0)
{
x_2 = x_76;
x_3 = x_90;
goto _start;
}
else
{
return x_90;
}
}
}
else
{
if (lean_obj_tag(x_84) == 0)
{
x_77 = x_84;
goto block_83;
}
else
{
uint8_t x_93; 
x_93 = l_String_posOfAux___main___closed__2;
if (x_93 == 0)
{
x_2 = x_76;
x_3 = x_84;
goto _start;
}
else
{
return x_84;
}
}
}
}
}
block_100:
{
uint8_t x_97; 
x_97 = l_String_posOfAux___main___closed__2;
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_75, x_96);
if (lean_obj_tag(x_98) == 0)
{
x_77 = x_98;
goto block_83;
}
else
{
x_2 = x_76;
x_3 = x_98;
goto _start;
}
}
else
{
if (lean_obj_tag(x_96) == 0)
{
x_77 = x_96;
goto block_83;
}
else
{
return x_96;
}
}
}
}
case 10:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_2, 1);
x_109 = l_Lean_Expr_hasMVar(x_108);
if (x_109 == 0)
{
uint8_t x_110; 
x_110 = l_String_posOfAux___main___closed__2;
if (x_110 == 0)
{
x_2 = x_108;
goto _start;
}
else
{
return x_3;
}
}
else
{
uint8_t x_112; 
x_112 = l_String_posOfAux___main___closed__1;
if (x_112 == 0)
{
x_2 = x_108;
goto _start;
}
else
{
return x_3;
}
}
}
else
{
lean_object* x_114; uint8_t x_115; 
x_114 = lean_ctor_get(x_2, 1);
x_115 = l_String_posOfAux___main___closed__2;
if (x_115 == 0)
{
x_2 = x_114;
goto _start;
}
else
{
return x_3;
}
}
}
case 11:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_2, 2);
x_118 = l_Lean_Expr_hasMVar(x_117);
if (x_118 == 0)
{
uint8_t x_119; 
x_119 = l_String_posOfAux___main___closed__2;
if (x_119 == 0)
{
x_2 = x_117;
goto _start;
}
else
{
return x_3;
}
}
else
{
uint8_t x_121; 
x_121 = l_String_posOfAux___main___closed__1;
if (x_121 == 0)
{
x_2 = x_117;
goto _start;
}
else
{
return x_3;
}
}
}
else
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_ctor_get(x_2, 2);
x_124 = l_String_posOfAux___main___closed__2;
if (x_124 == 0)
{
x_2 = x_123;
goto _start;
}
else
{
return x_3;
}
}
}
default: 
{
return x_3;
}
}
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_5, x_4);
if (x_8 == 0)
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = 0;
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_12 = lean_array_fget(x_3, x_5);
x_13 = lean_expr_eqv(x_1, x_12);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_inc(x_6);
x_15 = l_Lean_Meta_inferType(x_12, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_box(0);
x_20 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_17, x_19);
lean_dec(x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_free_object(x_15);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_5, x_21);
lean_dec(x_5);
x_5 = x_22;
x_7 = x_18;
goto _start;
}
else
{
uint8_t x_24; lean_object* x_25; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
x_24 = 1;
x_25 = lean_box(x_24);
lean_ctor_set(x_15, 0, x_25);
return x_15;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_box(0);
x_29 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_26, x_28);
lean_dec(x_26);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_5, x_30);
lean_dec(x_5);
x_5 = x_31;
x_7 = x_27;
goto _start;
}
else
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
x_33 = 1;
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_27);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_15);
if (x_36 == 0)
{
return x_15;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_15, 0);
x_38 = lean_ctor_get(x_15, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_15);
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
lean_dec(x_12);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_5, x_40);
lean_dec(x_5);
x_5 = x_41;
goto _start;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_array_get_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__2(x_1, x_2, x_2, x_5, x_6, x_3, x_4);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_anyRangeMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_2);
x_8 = lean_nat_dec_lt(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_array_fget(x_2, x_3);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_13 = !lean_is_exclusive(x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_4, 0);
x_15 = lean_ctor_get(x_4, 1);
x_16 = l_Lean_Expr_mvarId_x21(x_10);
lean_inc(x_5);
x_17 = l___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers(x_10, x_1, x_5, x_6);
lean_dec(x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_array_push(x_14, x_16);
lean_ctor_set(x_4, 0, x_21);
x_3 = x_12;
x_6 = x_20;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_array_push(x_15, x_16);
lean_ctor_set(x_4, 1, x_24);
x_3 = x_12;
x_6 = x_23;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_16);
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_5);
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
return x_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_17, 0);
x_28 = lean_ctor_get(x_17, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_17);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_4, 0);
x_31 = lean_ctor_get(x_4, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_4);
x_32 = l_Lean_Expr_mvarId_x21(x_10);
lean_inc(x_5);
x_33 = l___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers(x_10, x_1, x_5, x_6);
lean_dec(x_10);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_array_push(x_30, x_32);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_31);
x_3 = x_12;
x_4 = x_38;
x_6 = x_36;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_dec(x_33);
x_41 = lean_array_push(x_31, x_32);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_30);
lean_ctor_set(x_42, 1, x_41);
x_3 = x_12;
x_4 = x_42;
x_6 = x_40;
goto _start;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_5);
x_44 = lean_ctor_get(x_33, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_33, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_46 = x_33;
} else {
 lean_dec_ref(x_33);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Array_empty___closed__1;
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst___closed__1;
x_6 = l_Array_iterateMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst___spec__1(x_1, x_1, x_4, x_5, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Array_toList___rarg(x_9);
lean_dec(x_9);
x_12 = l_Array_toList___rarg(x_10);
lean_dec(x_10);
x_13 = l_List_append___rarg(x_11, x_12);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l_Array_toList___rarg(x_16);
lean_dec(x_16);
x_19 = l_Array_toList___rarg(x_17);
lean_dec(x_17);
x_20 = l_List_append___rarg(x_18, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_15);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_6);
if (x_22 == 0)
{
return x_6;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Array_iterateMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_iterateMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_1);
x_7 = lean_nat_dec_lt(x_2, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
x_8 = l_Array_shrink___main___rarg(x_1, x_3);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_5);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_array_fget(x_1, x_2);
x_11 = l_Lean_Expr_mvarId_x21(x_10);
lean_dec(x_10);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_13 = lean_metavar_ctx_is_expr_assigned(x_12, x_11);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_3, x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_17 = lean_nat_add(x_3, x_15);
lean_dec(x_3);
x_2 = x_16;
x_3 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_array_fswap(x_1, x_2, x_3);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
lean_dec(x_2);
x_22 = lean_nat_add(x_3, x_20);
lean_dec(x_3);
x_1 = x_19;
x_2 = x_21;
x_3 = x_22;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
lean_dec(x_2);
x_2 = x_25;
goto _start;
}
}
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_apply___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_LocalInstance_beq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
lean_object* l_Lean_Meta_apply(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_1);
x_5 = l_Lean_Meta_getMVarDecl(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 2);
x_11 = lean_ctor_get(x_3, 3);
x_12 = lean_ctor_get(x_3, 4);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_6, 4);
lean_inc(x_14);
x_15 = lean_array_get_size(x_10);
x_16 = lean_array_get_size(x_14);
x_17 = lean_nat_dec_eq(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_14);
lean_inc(x_9);
x_18 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_14);
lean_ctor_set(x_18, 3, x_11);
lean_ctor_set(x_18, 4, x_12);
if (x_17 == 0)
{
uint8_t x_1213; 
lean_dec(x_14);
lean_dec(x_6);
x_1213 = 0;
x_19 = x_1213;
goto block_1212;
}
else
{
lean_object* x_1214; uint8_t x_1215; 
x_1214 = lean_unsigned_to_nat(0u);
x_1215 = l_Array_isEqvAux___main___at_Lean_Meta_apply___spec__2(x_3, x_6, lean_box(0), x_10, x_14, x_1214);
lean_dec(x_14);
lean_dec(x_6);
x_19 = x_1215;
goto block_1212;
}
block_1212:
{
uint8_t x_20; 
x_20 = l_coeDecidableEq(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_7, 2);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_49; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_24 = lean_ctor_get(x_22, 2);
x_87 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_22, 2, x_87);
x_88 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2;
lean_inc(x_1);
x_89 = l_Lean_Meta_checkNotAssigned(x_1, x_88, x_18, x_7);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
lean_inc(x_1);
x_91 = l_Lean_Meta_getMVarType(x_1, x_18, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
lean_inc(x_18);
lean_inc(x_2);
x_94 = l_Lean_Meta_inferType(x_2, x_18, x_93);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
lean_inc(x_18);
lean_inc(x_95);
x_97 = l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux(x_95, x_18, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
x_100 = lean_unbox(x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
lean_dec(x_97);
x_102 = lean_ctor_get(x_98, 0);
lean_inc(x_102);
lean_dec(x_98);
x_103 = l_String_posOfAux___main___closed__2;
if (x_103 == 0)
{
lean_object* x_104; 
lean_inc(x_18);
lean_inc(x_92);
x_104 = l___private_Init_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(x_92, x_18, x_101);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_nat_sub(x_102, x_105);
lean_dec(x_105);
lean_dec(x_102);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = 0;
lean_inc(x_18);
x_110 = l_Lean_Meta_forallMetaTelescopeReducing(x_95, x_108, x_109, x_18, x_106);
lean_dec(x_108);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_143; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
lean_dec(x_110);
x_114 = lean_ctor_get(x_111, 0);
lean_inc(x_114);
lean_dec(x_111);
x_115 = lean_ctor_get(x_112, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_112, 1);
lean_inc(x_116);
lean_dec(x_112);
lean_inc(x_18);
lean_inc(x_92);
lean_inc(x_116);
x_143 = l_Lean_Meta_isExprDefEq(x_116, x_92, x_18, x_113);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_unbox(x_144);
lean_dec(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_2);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_dec(x_143);
x_147 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_116, x_92, x_18, x_146);
lean_dec(x_18);
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
x_49 = x_147;
goto block_86;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_147, 0);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_147);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_49 = x_151;
goto block_86;
}
}
else
{
lean_object* x_152; 
lean_dec(x_116);
lean_dec(x_92);
x_152 = lean_ctor_get(x_143, 1);
lean_inc(x_152);
lean_dec(x_143);
x_117 = x_152;
goto block_142;
}
}
else
{
uint8_t x_153; 
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_92);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_143);
if (x_153 == 0)
{
x_49 = x_143;
goto block_86;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_143, 0);
x_155 = lean_ctor_get(x_143, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_143);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_49 = x_156;
goto block_86;
}
}
block_142:
{
lean_object* x_118; 
lean_inc(x_18);
lean_inc(x_1);
x_118 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_114, x_115, x_18, x_117);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_unsigned_to_nat(0u);
x_121 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_114, x_114, x_120, x_2);
lean_inc(x_1);
x_122 = l_Lean_Meta_assignExprMVar(x_1, x_121, x_18, x_119);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_124 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_114, x_115, x_18, x_123);
lean_dec(x_115);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_124, 1);
lean_inc(x_125);
lean_dec(x_124);
x_126 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_114, x_120, x_120, x_18, x_125);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_127, x_18, x_128);
lean_dec(x_127);
x_49 = x_129;
goto block_86;
}
else
{
uint8_t x_130; 
lean_dec(x_114);
lean_dec(x_18);
x_130 = !lean_is_exclusive(x_124);
if (x_130 == 0)
{
x_49 = x_124;
goto block_86;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_124, 0);
x_132 = lean_ctor_get(x_124, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_124);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_49 = x_133;
goto block_86;
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_18);
lean_dec(x_1);
x_134 = !lean_is_exclusive(x_122);
if (x_134 == 0)
{
x_49 = x_122;
goto block_86;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_122, 0);
x_136 = lean_ctor_get(x_122, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_122);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_49 = x_137;
goto block_86;
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_118);
if (x_138 == 0)
{
x_49 = x_118;
goto block_86;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_118, 0);
x_140 = lean_ctor_get(x_118, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_118);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
x_49 = x_141;
goto block_86;
}
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_92);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_110);
if (x_157 == 0)
{
x_49 = x_110;
goto block_86;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_110, 0);
x_159 = lean_ctor_get(x_110, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_110);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_49 = x_160;
goto block_86;
}
}
}
else
{
uint8_t x_161; 
lean_dec(x_102);
lean_dec(x_95);
lean_dec(x_92);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_161 = !lean_is_exclusive(x_104);
if (x_161 == 0)
{
x_49 = x_104;
goto block_86;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_104, 0);
x_163 = lean_ctor_get(x_104, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_104);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_49 = x_164;
goto block_86;
}
}
}
else
{
lean_object* x_165; uint8_t x_166; lean_object* x_167; 
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_102);
x_166 = 0;
lean_inc(x_18);
x_167 = l_Lean_Meta_forallMetaTelescopeReducing(x_95, x_165, x_166, x_18, x_101);
lean_dec(x_165);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_200; 
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
lean_dec(x_167);
x_171 = lean_ctor_get(x_168, 0);
lean_inc(x_171);
lean_dec(x_168);
x_172 = lean_ctor_get(x_169, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_169, 1);
lean_inc(x_173);
lean_dec(x_169);
lean_inc(x_18);
lean_inc(x_92);
lean_inc(x_173);
x_200 = l_Lean_Meta_isExprDefEq(x_173, x_92, x_18, x_170);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; uint8_t x_202; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_unbox(x_201);
lean_dec(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; uint8_t x_205; 
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_2);
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
lean_dec(x_200);
x_204 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_173, x_92, x_18, x_203);
lean_dec(x_18);
x_205 = !lean_is_exclusive(x_204);
if (x_205 == 0)
{
x_49 = x_204;
goto block_86;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_204, 0);
x_207 = lean_ctor_get(x_204, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_204);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
x_49 = x_208;
goto block_86;
}
}
else
{
lean_object* x_209; 
lean_dec(x_173);
lean_dec(x_92);
x_209 = lean_ctor_get(x_200, 1);
lean_inc(x_209);
lean_dec(x_200);
x_174 = x_209;
goto block_199;
}
}
else
{
uint8_t x_210; 
lean_dec(x_173);
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_92);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_210 = !lean_is_exclusive(x_200);
if (x_210 == 0)
{
x_49 = x_200;
goto block_86;
}
else
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_200, 0);
x_212 = lean_ctor_get(x_200, 1);
lean_inc(x_212);
lean_inc(x_211);
lean_dec(x_200);
x_213 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_213, 0, x_211);
lean_ctor_set(x_213, 1, x_212);
x_49 = x_213;
goto block_86;
}
}
block_199:
{
lean_object* x_175; 
lean_inc(x_18);
lean_inc(x_1);
x_175 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_171, x_172, x_18, x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_177 = lean_unsigned_to_nat(0u);
x_178 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_171, x_171, x_177, x_2);
lean_inc(x_1);
x_179 = l_Lean_Meta_assignExprMVar(x_1, x_178, x_18, x_176);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_181 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_171, x_172, x_18, x_180);
lean_dec(x_172);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_183 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_171, x_177, x_177, x_18, x_182);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_184, x_18, x_185);
lean_dec(x_184);
x_49 = x_186;
goto block_86;
}
else
{
uint8_t x_187; 
lean_dec(x_171);
lean_dec(x_18);
x_187 = !lean_is_exclusive(x_181);
if (x_187 == 0)
{
x_49 = x_181;
goto block_86;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_181, 0);
x_189 = lean_ctor_get(x_181, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_181);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_49 = x_190;
goto block_86;
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_18);
lean_dec(x_1);
x_191 = !lean_is_exclusive(x_179);
if (x_191 == 0)
{
x_49 = x_179;
goto block_86;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_179, 0);
x_193 = lean_ctor_get(x_179, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_179);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_49 = x_194;
goto block_86;
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_172);
lean_dec(x_171);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_195 = !lean_is_exclusive(x_175);
if (x_195 == 0)
{
x_49 = x_175;
goto block_86;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_175, 0);
x_197 = lean_ctor_get(x_175, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_175);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
x_49 = x_198;
goto block_86;
}
}
}
}
else
{
uint8_t x_214; 
lean_dec(x_92);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_214 = !lean_is_exclusive(x_167);
if (x_214 == 0)
{
x_49 = x_167;
goto block_86;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_167, 0);
x_216 = lean_ctor_get(x_167, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_167);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
x_49 = x_217;
goto block_86;
}
}
}
}
else
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; 
x_218 = lean_ctor_get(x_97, 1);
lean_inc(x_218);
lean_dec(x_97);
x_219 = lean_ctor_get(x_98, 0);
lean_inc(x_219);
lean_dec(x_98);
x_220 = l_String_posOfAux___main___closed__1;
if (x_220 == 0)
{
lean_object* x_221; 
lean_inc(x_18);
lean_inc(x_92);
x_221 = l___private_Init_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(x_92, x_18, x_218);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_224 = lean_nat_sub(x_219, x_222);
lean_dec(x_222);
lean_dec(x_219);
x_225 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_225, 0, x_224);
x_226 = 0;
lean_inc(x_18);
x_227 = l_Lean_Meta_forallMetaTelescopeReducing(x_95, x_225, x_226, x_18, x_223);
lean_dec(x_225);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_260; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
lean_dec(x_227);
x_231 = lean_ctor_get(x_228, 0);
lean_inc(x_231);
lean_dec(x_228);
x_232 = lean_ctor_get(x_229, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_229, 1);
lean_inc(x_233);
lean_dec(x_229);
lean_inc(x_18);
lean_inc(x_92);
lean_inc(x_233);
x_260 = l_Lean_Meta_isExprDefEq(x_233, x_92, x_18, x_230);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; uint8_t x_262; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_unbox(x_261);
lean_dec(x_261);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; uint8_t x_265; 
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_2);
x_263 = lean_ctor_get(x_260, 1);
lean_inc(x_263);
lean_dec(x_260);
x_264 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_233, x_92, x_18, x_263);
lean_dec(x_18);
x_265 = !lean_is_exclusive(x_264);
if (x_265 == 0)
{
x_49 = x_264;
goto block_86;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_264, 0);
x_267 = lean_ctor_get(x_264, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_264);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
x_49 = x_268;
goto block_86;
}
}
else
{
lean_object* x_269; 
lean_dec(x_233);
lean_dec(x_92);
x_269 = lean_ctor_get(x_260, 1);
lean_inc(x_269);
lean_dec(x_260);
x_234 = x_269;
goto block_259;
}
}
else
{
uint8_t x_270; 
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_92);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_270 = !lean_is_exclusive(x_260);
if (x_270 == 0)
{
x_49 = x_260;
goto block_86;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_260, 0);
x_272 = lean_ctor_get(x_260, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_260);
x_273 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
x_49 = x_273;
goto block_86;
}
}
block_259:
{
lean_object* x_235; 
lean_inc(x_18);
lean_inc(x_1);
x_235 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_231, x_232, x_18, x_234);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
lean_dec(x_235);
x_237 = lean_unsigned_to_nat(0u);
x_238 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_231, x_231, x_237, x_2);
lean_inc(x_1);
x_239 = l_Lean_Meta_assignExprMVar(x_1, x_238, x_18, x_236);
if (lean_obj_tag(x_239) == 0)
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
lean_dec(x_239);
x_241 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_231, x_232, x_18, x_240);
lean_dec(x_232);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
lean_dec(x_241);
x_243 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_231, x_237, x_237, x_18, x_242);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_243, 1);
lean_inc(x_245);
lean_dec(x_243);
x_246 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_244, x_18, x_245);
lean_dec(x_244);
x_49 = x_246;
goto block_86;
}
else
{
uint8_t x_247; 
lean_dec(x_231);
lean_dec(x_18);
x_247 = !lean_is_exclusive(x_241);
if (x_247 == 0)
{
x_49 = x_241;
goto block_86;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_241, 0);
x_249 = lean_ctor_get(x_241, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_241);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
x_49 = x_250;
goto block_86;
}
}
}
else
{
uint8_t x_251; 
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_18);
lean_dec(x_1);
x_251 = !lean_is_exclusive(x_239);
if (x_251 == 0)
{
x_49 = x_239;
goto block_86;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_239, 0);
x_253 = lean_ctor_get(x_239, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_239);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
x_49 = x_254;
goto block_86;
}
}
}
else
{
uint8_t x_255; 
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_255 = !lean_is_exclusive(x_235);
if (x_255 == 0)
{
x_49 = x_235;
goto block_86;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_235, 0);
x_257 = lean_ctor_get(x_235, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_235);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
x_49 = x_258;
goto block_86;
}
}
}
}
else
{
uint8_t x_274; 
lean_dec(x_92);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_274 = !lean_is_exclusive(x_227);
if (x_274 == 0)
{
x_49 = x_227;
goto block_86;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_227, 0);
x_276 = lean_ctor_get(x_227, 1);
lean_inc(x_276);
lean_inc(x_275);
lean_dec(x_227);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
x_49 = x_277;
goto block_86;
}
}
}
else
{
uint8_t x_278; 
lean_dec(x_219);
lean_dec(x_95);
lean_dec(x_92);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_278 = !lean_is_exclusive(x_221);
if (x_278 == 0)
{
x_49 = x_221;
goto block_86;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_221, 0);
x_280 = lean_ctor_get(x_221, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_221);
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
x_49 = x_281;
goto block_86;
}
}
}
else
{
lean_object* x_282; uint8_t x_283; lean_object* x_284; 
x_282 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_282, 0, x_219);
x_283 = 0;
lean_inc(x_18);
x_284 = l_Lean_Meta_forallMetaTelescopeReducing(x_95, x_282, x_283, x_18, x_218);
lean_dec(x_282);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_317; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_284, 1);
lean_inc(x_287);
lean_dec(x_284);
x_288 = lean_ctor_get(x_285, 0);
lean_inc(x_288);
lean_dec(x_285);
x_289 = lean_ctor_get(x_286, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_286, 1);
lean_inc(x_290);
lean_dec(x_286);
lean_inc(x_18);
lean_inc(x_92);
lean_inc(x_290);
x_317 = l_Lean_Meta_isExprDefEq(x_290, x_92, x_18, x_287);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; uint8_t x_319; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_unbox(x_318);
lean_dec(x_318);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; uint8_t x_322; 
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_2);
x_320 = lean_ctor_get(x_317, 1);
lean_inc(x_320);
lean_dec(x_317);
x_321 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_290, x_92, x_18, x_320);
lean_dec(x_18);
x_322 = !lean_is_exclusive(x_321);
if (x_322 == 0)
{
x_49 = x_321;
goto block_86;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_323 = lean_ctor_get(x_321, 0);
x_324 = lean_ctor_get(x_321, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_321);
x_325 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
x_49 = x_325;
goto block_86;
}
}
else
{
lean_object* x_326; 
lean_dec(x_290);
lean_dec(x_92);
x_326 = lean_ctor_get(x_317, 1);
lean_inc(x_326);
lean_dec(x_317);
x_291 = x_326;
goto block_316;
}
}
else
{
uint8_t x_327; 
lean_dec(x_290);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_92);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_327 = !lean_is_exclusive(x_317);
if (x_327 == 0)
{
x_49 = x_317;
goto block_86;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_317, 0);
x_329 = lean_ctor_get(x_317, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_317);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
x_49 = x_330;
goto block_86;
}
}
block_316:
{
lean_object* x_292; 
lean_inc(x_18);
lean_inc(x_1);
x_292 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_288, x_289, x_18, x_291);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
lean_dec(x_292);
x_294 = lean_unsigned_to_nat(0u);
x_295 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_288, x_288, x_294, x_2);
lean_inc(x_1);
x_296 = l_Lean_Meta_assignExprMVar(x_1, x_295, x_18, x_293);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
lean_dec(x_296);
x_298 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_288, x_289, x_18, x_297);
lean_dec(x_289);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_299 = lean_ctor_get(x_298, 1);
lean_inc(x_299);
lean_dec(x_298);
x_300 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_288, x_294, x_294, x_18, x_299);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_301, x_18, x_302);
lean_dec(x_301);
x_49 = x_303;
goto block_86;
}
else
{
uint8_t x_304; 
lean_dec(x_288);
lean_dec(x_18);
x_304 = !lean_is_exclusive(x_298);
if (x_304 == 0)
{
x_49 = x_298;
goto block_86;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_298, 0);
x_306 = lean_ctor_get(x_298, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_298);
x_307 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_307, 0, x_305);
lean_ctor_set(x_307, 1, x_306);
x_49 = x_307;
goto block_86;
}
}
}
else
{
uint8_t x_308; 
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_18);
lean_dec(x_1);
x_308 = !lean_is_exclusive(x_296);
if (x_308 == 0)
{
x_49 = x_296;
goto block_86;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_296, 0);
x_310 = lean_ctor_get(x_296, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_296);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
x_49 = x_311;
goto block_86;
}
}
}
else
{
uint8_t x_312; 
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_312 = !lean_is_exclusive(x_292);
if (x_312 == 0)
{
x_49 = x_292;
goto block_86;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_292, 0);
x_314 = lean_ctor_get(x_292, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_292);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
x_49 = x_315;
goto block_86;
}
}
}
}
else
{
uint8_t x_331; 
lean_dec(x_92);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_331 = !lean_is_exclusive(x_284);
if (x_331 == 0)
{
x_49 = x_284;
goto block_86;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_284, 0);
x_333 = lean_ctor_get(x_284, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_284);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
x_49 = x_334;
goto block_86;
}
}
}
}
}
else
{
uint8_t x_335; 
lean_dec(x_95);
lean_dec(x_92);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_335 = !lean_is_exclusive(x_97);
if (x_335 == 0)
{
x_49 = x_97;
goto block_86;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_97, 0);
x_337 = lean_ctor_get(x_97, 1);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_97);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
x_49 = x_338;
goto block_86;
}
}
}
else
{
lean_object* x_339; lean_object* x_340; 
lean_dec(x_92);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_339 = lean_ctor_get(x_94, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_94, 1);
lean_inc(x_340);
lean_dec(x_94);
x_25 = x_339;
x_26 = x_340;
goto block_48;
}
}
else
{
lean_object* x_341; lean_object* x_342; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_341 = lean_ctor_get(x_91, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_91, 1);
lean_inc(x_342);
lean_dec(x_91);
x_25 = x_341;
x_26 = x_342;
goto block_48;
}
}
else
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_343 = lean_ctor_get(x_89, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_89, 1);
lean_inc(x_344);
lean_dec(x_89);
x_25 = x_343;
x_26 = x_344;
goto block_48;
}
block_48:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 2);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 2);
lean_dec(x_30);
lean_ctor_set(x_28, 2, x_24);
if (lean_is_scalar(x_8)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_8;
 lean_ctor_set_tag(x_31, 1);
}
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_28, 0);
x_33 = lean_ctor_get(x_28, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_28);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_24);
lean_ctor_set(x_26, 2, x_34);
if (lean_is_scalar(x_8)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_8;
 lean_ctor_set_tag(x_35, 1);
}
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_26);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_36 = lean_ctor_get(x_26, 2);
x_37 = lean_ctor_get(x_26, 0);
x_38 = lean_ctor_get(x_26, 1);
x_39 = lean_ctor_get(x_26, 3);
x_40 = lean_ctor_get(x_26, 4);
x_41 = lean_ctor_get(x_26, 5);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_36);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_26);
x_42 = lean_ctor_get(x_36, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_36, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 lean_ctor_release(x_36, 2);
 x_44 = x_36;
} else {
 lean_dec_ref(x_36);
 x_44 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_45 = lean_alloc_ctor(0, 3, 0);
} else {
 x_45 = x_44;
}
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_24);
x_46 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_38);
lean_ctor_set(x_46, 2, x_45);
lean_ctor_set(x_46, 3, x_39);
lean_ctor_set(x_46, 4, x_40);
lean_ctor_set(x_46, 5, x_41);
if (lean_is_scalar(x_8)) {
 x_47 = lean_alloc_ctor(1, 2, 0);
} else {
 x_47 = x_8;
 lean_ctor_set_tag(x_47, 1);
}
lean_ctor_set(x_47, 0, x_25);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
block_86:
{
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_8);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_50, 2);
lean_inc(x_51);
x_52 = !lean_is_exclusive(x_49);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_49, 1);
lean_dec(x_53);
x_54 = !lean_is_exclusive(x_50);
if (x_54 == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_50, 2);
lean_dec(x_55);
x_56 = !lean_is_exclusive(x_51);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_51, 2);
lean_dec(x_57);
lean_ctor_set(x_51, 2, x_24);
return x_49;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_51, 0);
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_51);
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_60, 2, x_24);
lean_ctor_set(x_50, 2, x_60);
return x_49;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_50, 0);
x_62 = lean_ctor_get(x_50, 1);
x_63 = lean_ctor_get(x_50, 3);
x_64 = lean_ctor_get(x_50, 4);
x_65 = lean_ctor_get(x_50, 5);
lean_inc(x_65);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_50);
x_66 = lean_ctor_get(x_51, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_51, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 x_68 = x_51;
} else {
 lean_dec_ref(x_51);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(0, 3, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_69, 2, x_24);
x_70 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_70, 0, x_61);
lean_ctor_set(x_70, 1, x_62);
lean_ctor_set(x_70, 2, x_69);
lean_ctor_set(x_70, 3, x_63);
lean_ctor_set(x_70, 4, x_64);
lean_ctor_set(x_70, 5, x_65);
lean_ctor_set(x_49, 1, x_70);
return x_49;
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_71 = lean_ctor_get(x_49, 0);
lean_inc(x_71);
lean_dec(x_49);
x_72 = lean_ctor_get(x_50, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_50, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_50, 3);
lean_inc(x_74);
x_75 = lean_ctor_get(x_50, 4);
lean_inc(x_75);
x_76 = lean_ctor_get(x_50, 5);
lean_inc(x_76);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 lean_ctor_release(x_50, 2);
 lean_ctor_release(x_50, 3);
 lean_ctor_release(x_50, 4);
 lean_ctor_release(x_50, 5);
 x_77 = x_50;
} else {
 lean_dec_ref(x_50);
 x_77 = lean_box(0);
}
x_78 = lean_ctor_get(x_51, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_51, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 lean_ctor_release(x_51, 2);
 x_80 = x_51;
} else {
 lean_dec_ref(x_51);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 3, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
lean_ctor_set(x_81, 2, x_24);
if (lean_is_scalar(x_77)) {
 x_82 = lean_alloc_ctor(0, 6, 0);
} else {
 x_82 = x_77;
}
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_73);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_74);
lean_ctor_set(x_82, 4, x_75);
lean_ctor_set(x_82, 5, x_76);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_71);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_49, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_49, 1);
lean_inc(x_85);
lean_dec(x_49);
x_25 = x_84;
x_26 = x_85;
goto block_48;
}
}
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_364; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_345 = lean_ctor_get(x_22, 0);
x_346 = lean_ctor_get(x_22, 1);
x_347 = lean_ctor_get(x_22, 2);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_22);
x_384 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_385 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_385, 0, x_345);
lean_ctor_set(x_385, 1, x_346);
lean_ctor_set(x_385, 2, x_384);
lean_ctor_set(x_7, 2, x_385);
x_386 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2;
lean_inc(x_1);
x_387 = l_Lean_Meta_checkNotAssigned(x_1, x_386, x_18, x_7);
if (lean_obj_tag(x_387) == 0)
{
lean_object* x_388; lean_object* x_389; 
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
lean_dec(x_387);
lean_inc(x_1);
x_389 = l_Lean_Meta_getMVarType(x_1, x_18, x_388);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
lean_dec(x_389);
lean_inc(x_18);
lean_inc(x_2);
x_392 = l_Lean_Meta_inferType(x_2, x_18, x_391);
if (lean_obj_tag(x_392) == 0)
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; 
x_393 = lean_ctor_get(x_392, 0);
lean_inc(x_393);
x_394 = lean_ctor_get(x_392, 1);
lean_inc(x_394);
lean_dec(x_392);
lean_inc(x_18);
lean_inc(x_393);
x_395 = l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux(x_393, x_18, x_394);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; lean_object* x_397; uint8_t x_398; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_396, 1);
lean_inc(x_397);
x_398 = lean_unbox(x_397);
lean_dec(x_397);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; uint8_t x_401; 
x_399 = lean_ctor_get(x_395, 1);
lean_inc(x_399);
lean_dec(x_395);
x_400 = lean_ctor_get(x_396, 0);
lean_inc(x_400);
lean_dec(x_396);
x_401 = l_String_posOfAux___main___closed__2;
if (x_401 == 0)
{
lean_object* x_402; 
lean_inc(x_18);
lean_inc(x_390);
x_402 = l___private_Init_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(x_390, x_18, x_399);
if (lean_obj_tag(x_402) == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; uint8_t x_407; lean_object* x_408; 
x_403 = lean_ctor_get(x_402, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_402, 1);
lean_inc(x_404);
lean_dec(x_402);
x_405 = lean_nat_sub(x_400, x_403);
lean_dec(x_403);
lean_dec(x_400);
x_406 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_406, 0, x_405);
x_407 = 0;
lean_inc(x_18);
x_408 = l_Lean_Meta_forallMetaTelescopeReducing(x_393, x_406, x_407, x_18, x_404);
lean_dec(x_406);
if (lean_obj_tag(x_408) == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_441; 
x_409 = lean_ctor_get(x_408, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_409, 1);
lean_inc(x_410);
x_411 = lean_ctor_get(x_408, 1);
lean_inc(x_411);
lean_dec(x_408);
x_412 = lean_ctor_get(x_409, 0);
lean_inc(x_412);
lean_dec(x_409);
x_413 = lean_ctor_get(x_410, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_410, 1);
lean_inc(x_414);
lean_dec(x_410);
lean_inc(x_18);
lean_inc(x_390);
lean_inc(x_414);
x_441 = l_Lean_Meta_isExprDefEq(x_414, x_390, x_18, x_411);
if (lean_obj_tag(x_441) == 0)
{
lean_object* x_442; uint8_t x_443; 
x_442 = lean_ctor_get(x_441, 0);
lean_inc(x_442);
x_443 = lean_unbox(x_442);
lean_dec(x_442);
if (x_443 == 0)
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_413);
lean_dec(x_412);
lean_dec(x_2);
x_444 = lean_ctor_get(x_441, 1);
lean_inc(x_444);
lean_dec(x_441);
x_445 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_414, x_390, x_18, x_444);
lean_dec(x_18);
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_448 = x_445;
} else {
 lean_dec_ref(x_445);
 x_448 = lean_box(0);
}
if (lean_is_scalar(x_448)) {
 x_449 = lean_alloc_ctor(1, 2, 0);
} else {
 x_449 = x_448;
}
lean_ctor_set(x_449, 0, x_446);
lean_ctor_set(x_449, 1, x_447);
x_364 = x_449;
goto block_383;
}
else
{
lean_object* x_450; 
lean_dec(x_414);
lean_dec(x_390);
x_450 = lean_ctor_get(x_441, 1);
lean_inc(x_450);
lean_dec(x_441);
x_415 = x_450;
goto block_440;
}
}
else
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_414);
lean_dec(x_413);
lean_dec(x_412);
lean_dec(x_390);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_451 = lean_ctor_get(x_441, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_441, 1);
lean_inc(x_452);
if (lean_is_exclusive(x_441)) {
 lean_ctor_release(x_441, 0);
 lean_ctor_release(x_441, 1);
 x_453 = x_441;
} else {
 lean_dec_ref(x_441);
 x_453 = lean_box(0);
}
if (lean_is_scalar(x_453)) {
 x_454 = lean_alloc_ctor(1, 2, 0);
} else {
 x_454 = x_453;
}
lean_ctor_set(x_454, 0, x_451);
lean_ctor_set(x_454, 1, x_452);
x_364 = x_454;
goto block_383;
}
block_440:
{
lean_object* x_416; 
lean_inc(x_18);
lean_inc(x_1);
x_416 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_412, x_413, x_18, x_415);
if (lean_obj_tag(x_416) == 0)
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_417 = lean_ctor_get(x_416, 1);
lean_inc(x_417);
lean_dec(x_416);
x_418 = lean_unsigned_to_nat(0u);
x_419 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_412, x_412, x_418, x_2);
lean_inc(x_1);
x_420 = l_Lean_Meta_assignExprMVar(x_1, x_419, x_18, x_417);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; 
x_421 = lean_ctor_get(x_420, 1);
lean_inc(x_421);
lean_dec(x_420);
x_422 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_412, x_413, x_18, x_421);
lean_dec(x_413);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_423 = lean_ctor_get(x_422, 1);
lean_inc(x_423);
lean_dec(x_422);
x_424 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_412, x_418, x_418, x_18, x_423);
x_425 = lean_ctor_get(x_424, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_424, 1);
lean_inc(x_426);
lean_dec(x_424);
x_427 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_425, x_18, x_426);
lean_dec(x_425);
x_364 = x_427;
goto block_383;
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_412);
lean_dec(x_18);
x_428 = lean_ctor_get(x_422, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_422, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_422)) {
 lean_ctor_release(x_422, 0);
 lean_ctor_release(x_422, 1);
 x_430 = x_422;
} else {
 lean_dec_ref(x_422);
 x_430 = lean_box(0);
}
if (lean_is_scalar(x_430)) {
 x_431 = lean_alloc_ctor(1, 2, 0);
} else {
 x_431 = x_430;
}
lean_ctor_set(x_431, 0, x_428);
lean_ctor_set(x_431, 1, x_429);
x_364 = x_431;
goto block_383;
}
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; 
lean_dec(x_413);
lean_dec(x_412);
lean_dec(x_18);
lean_dec(x_1);
x_432 = lean_ctor_get(x_420, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_420, 1);
lean_inc(x_433);
if (lean_is_exclusive(x_420)) {
 lean_ctor_release(x_420, 0);
 lean_ctor_release(x_420, 1);
 x_434 = x_420;
} else {
 lean_dec_ref(x_420);
 x_434 = lean_box(0);
}
if (lean_is_scalar(x_434)) {
 x_435 = lean_alloc_ctor(1, 2, 0);
} else {
 x_435 = x_434;
}
lean_ctor_set(x_435, 0, x_432);
lean_ctor_set(x_435, 1, x_433);
x_364 = x_435;
goto block_383;
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_413);
lean_dec(x_412);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_436 = lean_ctor_get(x_416, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_416, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_416)) {
 lean_ctor_release(x_416, 0);
 lean_ctor_release(x_416, 1);
 x_438 = x_416;
} else {
 lean_dec_ref(x_416);
 x_438 = lean_box(0);
}
if (lean_is_scalar(x_438)) {
 x_439 = lean_alloc_ctor(1, 2, 0);
} else {
 x_439 = x_438;
}
lean_ctor_set(x_439, 0, x_436);
lean_ctor_set(x_439, 1, x_437);
x_364 = x_439;
goto block_383;
}
}
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_390);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_455 = lean_ctor_get(x_408, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_408, 1);
lean_inc(x_456);
if (lean_is_exclusive(x_408)) {
 lean_ctor_release(x_408, 0);
 lean_ctor_release(x_408, 1);
 x_457 = x_408;
} else {
 lean_dec_ref(x_408);
 x_457 = lean_box(0);
}
if (lean_is_scalar(x_457)) {
 x_458 = lean_alloc_ctor(1, 2, 0);
} else {
 x_458 = x_457;
}
lean_ctor_set(x_458, 0, x_455);
lean_ctor_set(x_458, 1, x_456);
x_364 = x_458;
goto block_383;
}
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_400);
lean_dec(x_393);
lean_dec(x_390);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_459 = lean_ctor_get(x_402, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_402, 1);
lean_inc(x_460);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 x_461 = x_402;
} else {
 lean_dec_ref(x_402);
 x_461 = lean_box(0);
}
if (lean_is_scalar(x_461)) {
 x_462 = lean_alloc_ctor(1, 2, 0);
} else {
 x_462 = x_461;
}
lean_ctor_set(x_462, 0, x_459);
lean_ctor_set(x_462, 1, x_460);
x_364 = x_462;
goto block_383;
}
}
else
{
lean_object* x_463; uint8_t x_464; lean_object* x_465; 
x_463 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_463, 0, x_400);
x_464 = 0;
lean_inc(x_18);
x_465 = l_Lean_Meta_forallMetaTelescopeReducing(x_393, x_463, x_464, x_18, x_399);
lean_dec(x_463);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_498; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_466, 1);
lean_inc(x_467);
x_468 = lean_ctor_get(x_465, 1);
lean_inc(x_468);
lean_dec(x_465);
x_469 = lean_ctor_get(x_466, 0);
lean_inc(x_469);
lean_dec(x_466);
x_470 = lean_ctor_get(x_467, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_467, 1);
lean_inc(x_471);
lean_dec(x_467);
lean_inc(x_18);
lean_inc(x_390);
lean_inc(x_471);
x_498 = l_Lean_Meta_isExprDefEq(x_471, x_390, x_18, x_468);
if (lean_obj_tag(x_498) == 0)
{
lean_object* x_499; uint8_t x_500; 
x_499 = lean_ctor_get(x_498, 0);
lean_inc(x_499);
x_500 = lean_unbox(x_499);
lean_dec(x_499);
if (x_500 == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_2);
x_501 = lean_ctor_get(x_498, 1);
lean_inc(x_501);
lean_dec(x_498);
x_502 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_471, x_390, x_18, x_501);
lean_dec(x_18);
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_502, 1);
lean_inc(x_504);
if (lean_is_exclusive(x_502)) {
 lean_ctor_release(x_502, 0);
 lean_ctor_release(x_502, 1);
 x_505 = x_502;
} else {
 lean_dec_ref(x_502);
 x_505 = lean_box(0);
}
if (lean_is_scalar(x_505)) {
 x_506 = lean_alloc_ctor(1, 2, 0);
} else {
 x_506 = x_505;
}
lean_ctor_set(x_506, 0, x_503);
lean_ctor_set(x_506, 1, x_504);
x_364 = x_506;
goto block_383;
}
else
{
lean_object* x_507; 
lean_dec(x_471);
lean_dec(x_390);
x_507 = lean_ctor_get(x_498, 1);
lean_inc(x_507);
lean_dec(x_498);
x_472 = x_507;
goto block_497;
}
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_390);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_508 = lean_ctor_get(x_498, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_498, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_498)) {
 lean_ctor_release(x_498, 0);
 lean_ctor_release(x_498, 1);
 x_510 = x_498;
} else {
 lean_dec_ref(x_498);
 x_510 = lean_box(0);
}
if (lean_is_scalar(x_510)) {
 x_511 = lean_alloc_ctor(1, 2, 0);
} else {
 x_511 = x_510;
}
lean_ctor_set(x_511, 0, x_508);
lean_ctor_set(x_511, 1, x_509);
x_364 = x_511;
goto block_383;
}
block_497:
{
lean_object* x_473; 
lean_inc(x_18);
lean_inc(x_1);
x_473 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_469, x_470, x_18, x_472);
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_474 = lean_ctor_get(x_473, 1);
lean_inc(x_474);
lean_dec(x_473);
x_475 = lean_unsigned_to_nat(0u);
x_476 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_469, x_469, x_475, x_2);
lean_inc(x_1);
x_477 = l_Lean_Meta_assignExprMVar(x_1, x_476, x_18, x_474);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; lean_object* x_479; 
x_478 = lean_ctor_get(x_477, 1);
lean_inc(x_478);
lean_dec(x_477);
x_479 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_469, x_470, x_18, x_478);
lean_dec(x_470);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_480 = lean_ctor_get(x_479, 1);
lean_inc(x_480);
lean_dec(x_479);
x_481 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_469, x_475, x_475, x_18, x_480);
x_482 = lean_ctor_get(x_481, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_481, 1);
lean_inc(x_483);
lean_dec(x_481);
x_484 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_482, x_18, x_483);
lean_dec(x_482);
x_364 = x_484;
goto block_383;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_469);
lean_dec(x_18);
x_485 = lean_ctor_get(x_479, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_479, 1);
lean_inc(x_486);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 lean_ctor_release(x_479, 1);
 x_487 = x_479;
} else {
 lean_dec_ref(x_479);
 x_487 = lean_box(0);
}
if (lean_is_scalar(x_487)) {
 x_488 = lean_alloc_ctor(1, 2, 0);
} else {
 x_488 = x_487;
}
lean_ctor_set(x_488, 0, x_485);
lean_ctor_set(x_488, 1, x_486);
x_364 = x_488;
goto block_383;
}
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_18);
lean_dec(x_1);
x_489 = lean_ctor_get(x_477, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_477, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 x_491 = x_477;
} else {
 lean_dec_ref(x_477);
 x_491 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_492 = lean_alloc_ctor(1, 2, 0);
} else {
 x_492 = x_491;
}
lean_ctor_set(x_492, 0, x_489);
lean_ctor_set(x_492, 1, x_490);
x_364 = x_492;
goto block_383;
}
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_493 = lean_ctor_get(x_473, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_473, 1);
lean_inc(x_494);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 x_495 = x_473;
} else {
 lean_dec_ref(x_473);
 x_495 = lean_box(0);
}
if (lean_is_scalar(x_495)) {
 x_496 = lean_alloc_ctor(1, 2, 0);
} else {
 x_496 = x_495;
}
lean_ctor_set(x_496, 0, x_493);
lean_ctor_set(x_496, 1, x_494);
x_364 = x_496;
goto block_383;
}
}
}
else
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
lean_dec(x_390);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_512 = lean_ctor_get(x_465, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_465, 1);
lean_inc(x_513);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_514 = x_465;
} else {
 lean_dec_ref(x_465);
 x_514 = lean_box(0);
}
if (lean_is_scalar(x_514)) {
 x_515 = lean_alloc_ctor(1, 2, 0);
} else {
 x_515 = x_514;
}
lean_ctor_set(x_515, 0, x_512);
lean_ctor_set(x_515, 1, x_513);
x_364 = x_515;
goto block_383;
}
}
}
else
{
lean_object* x_516; lean_object* x_517; uint8_t x_518; 
x_516 = lean_ctor_get(x_395, 1);
lean_inc(x_516);
lean_dec(x_395);
x_517 = lean_ctor_get(x_396, 0);
lean_inc(x_517);
lean_dec(x_396);
x_518 = l_String_posOfAux___main___closed__1;
if (x_518 == 0)
{
lean_object* x_519; 
lean_inc(x_18);
lean_inc(x_390);
x_519 = l___private_Init_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(x_390, x_18, x_516);
if (lean_obj_tag(x_519) == 0)
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; uint8_t x_524; lean_object* x_525; 
x_520 = lean_ctor_get(x_519, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_519, 1);
lean_inc(x_521);
lean_dec(x_519);
x_522 = lean_nat_sub(x_517, x_520);
lean_dec(x_520);
lean_dec(x_517);
x_523 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_523, 0, x_522);
x_524 = 0;
lean_inc(x_18);
x_525 = l_Lean_Meta_forallMetaTelescopeReducing(x_393, x_523, x_524, x_18, x_521);
lean_dec(x_523);
if (lean_obj_tag(x_525) == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_558; 
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_526, 1);
lean_inc(x_527);
x_528 = lean_ctor_get(x_525, 1);
lean_inc(x_528);
lean_dec(x_525);
x_529 = lean_ctor_get(x_526, 0);
lean_inc(x_529);
lean_dec(x_526);
x_530 = lean_ctor_get(x_527, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_527, 1);
lean_inc(x_531);
lean_dec(x_527);
lean_inc(x_18);
lean_inc(x_390);
lean_inc(x_531);
x_558 = l_Lean_Meta_isExprDefEq(x_531, x_390, x_18, x_528);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; uint8_t x_560; 
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
x_560 = lean_unbox(x_559);
lean_dec(x_559);
if (x_560 == 0)
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
lean_dec(x_530);
lean_dec(x_529);
lean_dec(x_2);
x_561 = lean_ctor_get(x_558, 1);
lean_inc(x_561);
lean_dec(x_558);
x_562 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_531, x_390, x_18, x_561);
lean_dec(x_18);
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_562, 1);
lean_inc(x_564);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 lean_ctor_release(x_562, 1);
 x_565 = x_562;
} else {
 lean_dec_ref(x_562);
 x_565 = lean_box(0);
}
if (lean_is_scalar(x_565)) {
 x_566 = lean_alloc_ctor(1, 2, 0);
} else {
 x_566 = x_565;
}
lean_ctor_set(x_566, 0, x_563);
lean_ctor_set(x_566, 1, x_564);
x_364 = x_566;
goto block_383;
}
else
{
lean_object* x_567; 
lean_dec(x_531);
lean_dec(x_390);
x_567 = lean_ctor_get(x_558, 1);
lean_inc(x_567);
lean_dec(x_558);
x_532 = x_567;
goto block_557;
}
}
else
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; 
lean_dec(x_531);
lean_dec(x_530);
lean_dec(x_529);
lean_dec(x_390);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_568 = lean_ctor_get(x_558, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_558, 1);
lean_inc(x_569);
if (lean_is_exclusive(x_558)) {
 lean_ctor_release(x_558, 0);
 lean_ctor_release(x_558, 1);
 x_570 = x_558;
} else {
 lean_dec_ref(x_558);
 x_570 = lean_box(0);
}
if (lean_is_scalar(x_570)) {
 x_571 = lean_alloc_ctor(1, 2, 0);
} else {
 x_571 = x_570;
}
lean_ctor_set(x_571, 0, x_568);
lean_ctor_set(x_571, 1, x_569);
x_364 = x_571;
goto block_383;
}
block_557:
{
lean_object* x_533; 
lean_inc(x_18);
lean_inc(x_1);
x_533 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_529, x_530, x_18, x_532);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
x_534 = lean_ctor_get(x_533, 1);
lean_inc(x_534);
lean_dec(x_533);
x_535 = lean_unsigned_to_nat(0u);
x_536 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_529, x_529, x_535, x_2);
lean_inc(x_1);
x_537 = l_Lean_Meta_assignExprMVar(x_1, x_536, x_18, x_534);
if (lean_obj_tag(x_537) == 0)
{
lean_object* x_538; lean_object* x_539; 
x_538 = lean_ctor_get(x_537, 1);
lean_inc(x_538);
lean_dec(x_537);
x_539 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_529, x_530, x_18, x_538);
lean_dec(x_530);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_540 = lean_ctor_get(x_539, 1);
lean_inc(x_540);
lean_dec(x_539);
x_541 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_529, x_535, x_535, x_18, x_540);
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_541, 1);
lean_inc(x_543);
lean_dec(x_541);
x_544 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_542, x_18, x_543);
lean_dec(x_542);
x_364 = x_544;
goto block_383;
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_dec(x_529);
lean_dec(x_18);
x_545 = lean_ctor_get(x_539, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_539, 1);
lean_inc(x_546);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 lean_ctor_release(x_539, 1);
 x_547 = x_539;
} else {
 lean_dec_ref(x_539);
 x_547 = lean_box(0);
}
if (lean_is_scalar(x_547)) {
 x_548 = lean_alloc_ctor(1, 2, 0);
} else {
 x_548 = x_547;
}
lean_ctor_set(x_548, 0, x_545);
lean_ctor_set(x_548, 1, x_546);
x_364 = x_548;
goto block_383;
}
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_530);
lean_dec(x_529);
lean_dec(x_18);
lean_dec(x_1);
x_549 = lean_ctor_get(x_537, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_537, 1);
lean_inc(x_550);
if (lean_is_exclusive(x_537)) {
 lean_ctor_release(x_537, 0);
 lean_ctor_release(x_537, 1);
 x_551 = x_537;
} else {
 lean_dec_ref(x_537);
 x_551 = lean_box(0);
}
if (lean_is_scalar(x_551)) {
 x_552 = lean_alloc_ctor(1, 2, 0);
} else {
 x_552 = x_551;
}
lean_ctor_set(x_552, 0, x_549);
lean_ctor_set(x_552, 1, x_550);
x_364 = x_552;
goto block_383;
}
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
lean_dec(x_530);
lean_dec(x_529);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_553 = lean_ctor_get(x_533, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_533, 1);
lean_inc(x_554);
if (lean_is_exclusive(x_533)) {
 lean_ctor_release(x_533, 0);
 lean_ctor_release(x_533, 1);
 x_555 = x_533;
} else {
 lean_dec_ref(x_533);
 x_555 = lean_box(0);
}
if (lean_is_scalar(x_555)) {
 x_556 = lean_alloc_ctor(1, 2, 0);
} else {
 x_556 = x_555;
}
lean_ctor_set(x_556, 0, x_553);
lean_ctor_set(x_556, 1, x_554);
x_364 = x_556;
goto block_383;
}
}
}
else
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
lean_dec(x_390);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_572 = lean_ctor_get(x_525, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_525, 1);
lean_inc(x_573);
if (lean_is_exclusive(x_525)) {
 lean_ctor_release(x_525, 0);
 lean_ctor_release(x_525, 1);
 x_574 = x_525;
} else {
 lean_dec_ref(x_525);
 x_574 = lean_box(0);
}
if (lean_is_scalar(x_574)) {
 x_575 = lean_alloc_ctor(1, 2, 0);
} else {
 x_575 = x_574;
}
lean_ctor_set(x_575, 0, x_572);
lean_ctor_set(x_575, 1, x_573);
x_364 = x_575;
goto block_383;
}
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
lean_dec(x_517);
lean_dec(x_393);
lean_dec(x_390);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_576 = lean_ctor_get(x_519, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_519, 1);
lean_inc(x_577);
if (lean_is_exclusive(x_519)) {
 lean_ctor_release(x_519, 0);
 lean_ctor_release(x_519, 1);
 x_578 = x_519;
} else {
 lean_dec_ref(x_519);
 x_578 = lean_box(0);
}
if (lean_is_scalar(x_578)) {
 x_579 = lean_alloc_ctor(1, 2, 0);
} else {
 x_579 = x_578;
}
lean_ctor_set(x_579, 0, x_576);
lean_ctor_set(x_579, 1, x_577);
x_364 = x_579;
goto block_383;
}
}
else
{
lean_object* x_580; uint8_t x_581; lean_object* x_582; 
x_580 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_580, 0, x_517);
x_581 = 0;
lean_inc(x_18);
x_582 = l_Lean_Meta_forallMetaTelescopeReducing(x_393, x_580, x_581, x_18, x_516);
lean_dec(x_580);
if (lean_obj_tag(x_582) == 0)
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_615; 
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_583, 1);
lean_inc(x_584);
x_585 = lean_ctor_get(x_582, 1);
lean_inc(x_585);
lean_dec(x_582);
x_586 = lean_ctor_get(x_583, 0);
lean_inc(x_586);
lean_dec(x_583);
x_587 = lean_ctor_get(x_584, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_584, 1);
lean_inc(x_588);
lean_dec(x_584);
lean_inc(x_18);
lean_inc(x_390);
lean_inc(x_588);
x_615 = l_Lean_Meta_isExprDefEq(x_588, x_390, x_18, x_585);
if (lean_obj_tag(x_615) == 0)
{
lean_object* x_616; uint8_t x_617; 
x_616 = lean_ctor_get(x_615, 0);
lean_inc(x_616);
x_617 = lean_unbox(x_616);
lean_dec(x_616);
if (x_617 == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; 
lean_dec(x_587);
lean_dec(x_586);
lean_dec(x_2);
x_618 = lean_ctor_get(x_615, 1);
lean_inc(x_618);
lean_dec(x_615);
x_619 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_588, x_390, x_18, x_618);
lean_dec(x_18);
x_620 = lean_ctor_get(x_619, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_619, 1);
lean_inc(x_621);
if (lean_is_exclusive(x_619)) {
 lean_ctor_release(x_619, 0);
 lean_ctor_release(x_619, 1);
 x_622 = x_619;
} else {
 lean_dec_ref(x_619);
 x_622 = lean_box(0);
}
if (lean_is_scalar(x_622)) {
 x_623 = lean_alloc_ctor(1, 2, 0);
} else {
 x_623 = x_622;
}
lean_ctor_set(x_623, 0, x_620);
lean_ctor_set(x_623, 1, x_621);
x_364 = x_623;
goto block_383;
}
else
{
lean_object* x_624; 
lean_dec(x_588);
lean_dec(x_390);
x_624 = lean_ctor_get(x_615, 1);
lean_inc(x_624);
lean_dec(x_615);
x_589 = x_624;
goto block_614;
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
lean_dec(x_588);
lean_dec(x_587);
lean_dec(x_586);
lean_dec(x_390);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_625 = lean_ctor_get(x_615, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_615, 1);
lean_inc(x_626);
if (lean_is_exclusive(x_615)) {
 lean_ctor_release(x_615, 0);
 lean_ctor_release(x_615, 1);
 x_627 = x_615;
} else {
 lean_dec_ref(x_615);
 x_627 = lean_box(0);
}
if (lean_is_scalar(x_627)) {
 x_628 = lean_alloc_ctor(1, 2, 0);
} else {
 x_628 = x_627;
}
lean_ctor_set(x_628, 0, x_625);
lean_ctor_set(x_628, 1, x_626);
x_364 = x_628;
goto block_383;
}
block_614:
{
lean_object* x_590; 
lean_inc(x_18);
lean_inc(x_1);
x_590 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_586, x_587, x_18, x_589);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_591 = lean_ctor_get(x_590, 1);
lean_inc(x_591);
lean_dec(x_590);
x_592 = lean_unsigned_to_nat(0u);
x_593 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_586, x_586, x_592, x_2);
lean_inc(x_1);
x_594 = l_Lean_Meta_assignExprMVar(x_1, x_593, x_18, x_591);
if (lean_obj_tag(x_594) == 0)
{
lean_object* x_595; lean_object* x_596; 
x_595 = lean_ctor_get(x_594, 1);
lean_inc(x_595);
lean_dec(x_594);
x_596 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_586, x_587, x_18, x_595);
lean_dec(x_587);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_597 = lean_ctor_get(x_596, 1);
lean_inc(x_597);
lean_dec(x_596);
x_598 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_586, x_592, x_592, x_18, x_597);
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_598, 1);
lean_inc(x_600);
lean_dec(x_598);
x_601 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_599, x_18, x_600);
lean_dec(x_599);
x_364 = x_601;
goto block_383;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
lean_dec(x_586);
lean_dec(x_18);
x_602 = lean_ctor_get(x_596, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_596, 1);
lean_inc(x_603);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_604 = x_596;
} else {
 lean_dec_ref(x_596);
 x_604 = lean_box(0);
}
if (lean_is_scalar(x_604)) {
 x_605 = lean_alloc_ctor(1, 2, 0);
} else {
 x_605 = x_604;
}
lean_ctor_set(x_605, 0, x_602);
lean_ctor_set(x_605, 1, x_603);
x_364 = x_605;
goto block_383;
}
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
lean_dec(x_587);
lean_dec(x_586);
lean_dec(x_18);
lean_dec(x_1);
x_606 = lean_ctor_get(x_594, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_594, 1);
lean_inc(x_607);
if (lean_is_exclusive(x_594)) {
 lean_ctor_release(x_594, 0);
 lean_ctor_release(x_594, 1);
 x_608 = x_594;
} else {
 lean_dec_ref(x_594);
 x_608 = lean_box(0);
}
if (lean_is_scalar(x_608)) {
 x_609 = lean_alloc_ctor(1, 2, 0);
} else {
 x_609 = x_608;
}
lean_ctor_set(x_609, 0, x_606);
lean_ctor_set(x_609, 1, x_607);
x_364 = x_609;
goto block_383;
}
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_587);
lean_dec(x_586);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_610 = lean_ctor_get(x_590, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_590, 1);
lean_inc(x_611);
if (lean_is_exclusive(x_590)) {
 lean_ctor_release(x_590, 0);
 lean_ctor_release(x_590, 1);
 x_612 = x_590;
} else {
 lean_dec_ref(x_590);
 x_612 = lean_box(0);
}
if (lean_is_scalar(x_612)) {
 x_613 = lean_alloc_ctor(1, 2, 0);
} else {
 x_613 = x_612;
}
lean_ctor_set(x_613, 0, x_610);
lean_ctor_set(x_613, 1, x_611);
x_364 = x_613;
goto block_383;
}
}
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
lean_dec(x_390);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_629 = lean_ctor_get(x_582, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_582, 1);
lean_inc(x_630);
if (lean_is_exclusive(x_582)) {
 lean_ctor_release(x_582, 0);
 lean_ctor_release(x_582, 1);
 x_631 = x_582;
} else {
 lean_dec_ref(x_582);
 x_631 = lean_box(0);
}
if (lean_is_scalar(x_631)) {
 x_632 = lean_alloc_ctor(1, 2, 0);
} else {
 x_632 = x_631;
}
lean_ctor_set(x_632, 0, x_629);
lean_ctor_set(x_632, 1, x_630);
x_364 = x_632;
goto block_383;
}
}
}
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
lean_dec(x_393);
lean_dec(x_390);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_633 = lean_ctor_get(x_395, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_395, 1);
lean_inc(x_634);
if (lean_is_exclusive(x_395)) {
 lean_ctor_release(x_395, 0);
 lean_ctor_release(x_395, 1);
 x_635 = x_395;
} else {
 lean_dec_ref(x_395);
 x_635 = lean_box(0);
}
if (lean_is_scalar(x_635)) {
 x_636 = lean_alloc_ctor(1, 2, 0);
} else {
 x_636 = x_635;
}
lean_ctor_set(x_636, 0, x_633);
lean_ctor_set(x_636, 1, x_634);
x_364 = x_636;
goto block_383;
}
}
else
{
lean_object* x_637; lean_object* x_638; 
lean_dec(x_390);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_637 = lean_ctor_get(x_392, 0);
lean_inc(x_637);
x_638 = lean_ctor_get(x_392, 1);
lean_inc(x_638);
lean_dec(x_392);
x_348 = x_637;
x_349 = x_638;
goto block_363;
}
}
else
{
lean_object* x_639; lean_object* x_640; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_639 = lean_ctor_get(x_389, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_389, 1);
lean_inc(x_640);
lean_dec(x_389);
x_348 = x_639;
x_349 = x_640;
goto block_363;
}
}
else
{
lean_object* x_641; lean_object* x_642; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_641 = lean_ctor_get(x_387, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_387, 1);
lean_inc(x_642);
lean_dec(x_387);
x_348 = x_641;
x_349 = x_642;
goto block_363;
}
block_363:
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_350 = lean_ctor_get(x_349, 2);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_349, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_349, 3);
lean_inc(x_353);
x_354 = lean_ctor_get(x_349, 4);
lean_inc(x_354);
x_355 = lean_ctor_get(x_349, 5);
lean_inc(x_355);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 lean_ctor_release(x_349, 2);
 lean_ctor_release(x_349, 3);
 lean_ctor_release(x_349, 4);
 lean_ctor_release(x_349, 5);
 x_356 = x_349;
} else {
 lean_dec_ref(x_349);
 x_356 = lean_box(0);
}
x_357 = lean_ctor_get(x_350, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_350, 1);
lean_inc(x_358);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 lean_ctor_release(x_350, 2);
 x_359 = x_350;
} else {
 lean_dec_ref(x_350);
 x_359 = lean_box(0);
}
if (lean_is_scalar(x_359)) {
 x_360 = lean_alloc_ctor(0, 3, 0);
} else {
 x_360 = x_359;
}
lean_ctor_set(x_360, 0, x_357);
lean_ctor_set(x_360, 1, x_358);
lean_ctor_set(x_360, 2, x_347);
if (lean_is_scalar(x_356)) {
 x_361 = lean_alloc_ctor(0, 6, 0);
} else {
 x_361 = x_356;
}
lean_ctor_set(x_361, 0, x_351);
lean_ctor_set(x_361, 1, x_352);
lean_ctor_set(x_361, 2, x_360);
lean_ctor_set(x_361, 3, x_353);
lean_ctor_set(x_361, 4, x_354);
lean_ctor_set(x_361, 5, x_355);
if (lean_is_scalar(x_8)) {
 x_362 = lean_alloc_ctor(1, 2, 0);
} else {
 x_362 = x_8;
 lean_ctor_set_tag(x_362, 1);
}
lean_ctor_set(x_362, 0, x_348);
lean_ctor_set(x_362, 1, x_361);
return x_362;
}
block_383:
{
if (lean_obj_tag(x_364) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_8);
x_365 = lean_ctor_get(x_364, 1);
lean_inc(x_365);
x_366 = lean_ctor_get(x_365, 2);
lean_inc(x_366);
x_367 = lean_ctor_get(x_364, 0);
lean_inc(x_367);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 x_368 = x_364;
} else {
 lean_dec_ref(x_364);
 x_368 = lean_box(0);
}
x_369 = lean_ctor_get(x_365, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_365, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_365, 3);
lean_inc(x_371);
x_372 = lean_ctor_get(x_365, 4);
lean_inc(x_372);
x_373 = lean_ctor_get(x_365, 5);
lean_inc(x_373);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 lean_ctor_release(x_365, 2);
 lean_ctor_release(x_365, 3);
 lean_ctor_release(x_365, 4);
 lean_ctor_release(x_365, 5);
 x_374 = x_365;
} else {
 lean_dec_ref(x_365);
 x_374 = lean_box(0);
}
x_375 = lean_ctor_get(x_366, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_366, 1);
lean_inc(x_376);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 lean_ctor_release(x_366, 2);
 x_377 = x_366;
} else {
 lean_dec_ref(x_366);
 x_377 = lean_box(0);
}
if (lean_is_scalar(x_377)) {
 x_378 = lean_alloc_ctor(0, 3, 0);
} else {
 x_378 = x_377;
}
lean_ctor_set(x_378, 0, x_375);
lean_ctor_set(x_378, 1, x_376);
lean_ctor_set(x_378, 2, x_347);
if (lean_is_scalar(x_374)) {
 x_379 = lean_alloc_ctor(0, 6, 0);
} else {
 x_379 = x_374;
}
lean_ctor_set(x_379, 0, x_369);
lean_ctor_set(x_379, 1, x_370);
lean_ctor_set(x_379, 2, x_378);
lean_ctor_set(x_379, 3, x_371);
lean_ctor_set(x_379, 4, x_372);
lean_ctor_set(x_379, 5, x_373);
if (lean_is_scalar(x_368)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_368;
}
lean_ctor_set(x_380, 0, x_367);
lean_ctor_set(x_380, 1, x_379);
return x_380;
}
else
{
lean_object* x_381; lean_object* x_382; 
x_381 = lean_ctor_get(x_364, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_364, 1);
lean_inc(x_382);
lean_dec(x_364);
x_348 = x_381;
x_349 = x_382;
goto block_363;
}
}
}
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_669; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_643 = lean_ctor_get(x_7, 2);
x_644 = lean_ctor_get(x_7, 0);
x_645 = lean_ctor_get(x_7, 1);
x_646 = lean_ctor_get(x_7, 3);
x_647 = lean_ctor_get(x_7, 4);
x_648 = lean_ctor_get(x_7, 5);
lean_inc(x_648);
lean_inc(x_647);
lean_inc(x_646);
lean_inc(x_643);
lean_inc(x_645);
lean_inc(x_644);
lean_dec(x_7);
x_649 = lean_ctor_get(x_643, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_643, 1);
lean_inc(x_650);
x_651 = lean_ctor_get(x_643, 2);
lean_inc(x_651);
if (lean_is_exclusive(x_643)) {
 lean_ctor_release(x_643, 0);
 lean_ctor_release(x_643, 1);
 lean_ctor_release(x_643, 2);
 x_652 = x_643;
} else {
 lean_dec_ref(x_643);
 x_652 = lean_box(0);
}
x_689 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_652)) {
 x_690 = lean_alloc_ctor(0, 3, 0);
} else {
 x_690 = x_652;
}
lean_ctor_set(x_690, 0, x_649);
lean_ctor_set(x_690, 1, x_650);
lean_ctor_set(x_690, 2, x_689);
x_691 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_691, 0, x_644);
lean_ctor_set(x_691, 1, x_645);
lean_ctor_set(x_691, 2, x_690);
lean_ctor_set(x_691, 3, x_646);
lean_ctor_set(x_691, 4, x_647);
lean_ctor_set(x_691, 5, x_648);
x_692 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2;
lean_inc(x_1);
x_693 = l_Lean_Meta_checkNotAssigned(x_1, x_692, x_18, x_691);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_694; lean_object* x_695; 
x_694 = lean_ctor_get(x_693, 1);
lean_inc(x_694);
lean_dec(x_693);
lean_inc(x_1);
x_695 = l_Lean_Meta_getMVarType(x_1, x_18, x_694);
if (lean_obj_tag(x_695) == 0)
{
lean_object* x_696; lean_object* x_697; lean_object* x_698; 
x_696 = lean_ctor_get(x_695, 0);
lean_inc(x_696);
x_697 = lean_ctor_get(x_695, 1);
lean_inc(x_697);
lean_dec(x_695);
lean_inc(x_18);
lean_inc(x_2);
x_698 = l_Lean_Meta_inferType(x_2, x_18, x_697);
if (lean_obj_tag(x_698) == 0)
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; 
x_699 = lean_ctor_get(x_698, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_698, 1);
lean_inc(x_700);
lean_dec(x_698);
lean_inc(x_18);
lean_inc(x_699);
x_701 = l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux(x_699, x_18, x_700);
if (lean_obj_tag(x_701) == 0)
{
lean_object* x_702; lean_object* x_703; uint8_t x_704; 
x_702 = lean_ctor_get(x_701, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_702, 1);
lean_inc(x_703);
x_704 = lean_unbox(x_703);
lean_dec(x_703);
if (x_704 == 0)
{
lean_object* x_705; lean_object* x_706; uint8_t x_707; 
x_705 = lean_ctor_get(x_701, 1);
lean_inc(x_705);
lean_dec(x_701);
x_706 = lean_ctor_get(x_702, 0);
lean_inc(x_706);
lean_dec(x_702);
x_707 = l_String_posOfAux___main___closed__2;
if (x_707 == 0)
{
lean_object* x_708; 
lean_inc(x_18);
lean_inc(x_696);
x_708 = l___private_Init_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(x_696, x_18, x_705);
if (lean_obj_tag(x_708) == 0)
{
lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; uint8_t x_713; lean_object* x_714; 
x_709 = lean_ctor_get(x_708, 0);
lean_inc(x_709);
x_710 = lean_ctor_get(x_708, 1);
lean_inc(x_710);
lean_dec(x_708);
x_711 = lean_nat_sub(x_706, x_709);
lean_dec(x_709);
lean_dec(x_706);
x_712 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_712, 0, x_711);
x_713 = 0;
lean_inc(x_18);
x_714 = l_Lean_Meta_forallMetaTelescopeReducing(x_699, x_712, x_713, x_18, x_710);
lean_dec(x_712);
if (lean_obj_tag(x_714) == 0)
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_747; 
x_715 = lean_ctor_get(x_714, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_715, 1);
lean_inc(x_716);
x_717 = lean_ctor_get(x_714, 1);
lean_inc(x_717);
lean_dec(x_714);
x_718 = lean_ctor_get(x_715, 0);
lean_inc(x_718);
lean_dec(x_715);
x_719 = lean_ctor_get(x_716, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_716, 1);
lean_inc(x_720);
lean_dec(x_716);
lean_inc(x_18);
lean_inc(x_696);
lean_inc(x_720);
x_747 = l_Lean_Meta_isExprDefEq(x_720, x_696, x_18, x_717);
if (lean_obj_tag(x_747) == 0)
{
lean_object* x_748; uint8_t x_749; 
x_748 = lean_ctor_get(x_747, 0);
lean_inc(x_748);
x_749 = lean_unbox(x_748);
lean_dec(x_748);
if (x_749 == 0)
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; 
lean_dec(x_719);
lean_dec(x_718);
lean_dec(x_2);
x_750 = lean_ctor_get(x_747, 1);
lean_inc(x_750);
lean_dec(x_747);
x_751 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_720, x_696, x_18, x_750);
lean_dec(x_18);
x_752 = lean_ctor_get(x_751, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_751, 1);
lean_inc(x_753);
if (lean_is_exclusive(x_751)) {
 lean_ctor_release(x_751, 0);
 lean_ctor_release(x_751, 1);
 x_754 = x_751;
} else {
 lean_dec_ref(x_751);
 x_754 = lean_box(0);
}
if (lean_is_scalar(x_754)) {
 x_755 = lean_alloc_ctor(1, 2, 0);
} else {
 x_755 = x_754;
}
lean_ctor_set(x_755, 0, x_752);
lean_ctor_set(x_755, 1, x_753);
x_669 = x_755;
goto block_688;
}
else
{
lean_object* x_756; 
lean_dec(x_720);
lean_dec(x_696);
x_756 = lean_ctor_get(x_747, 1);
lean_inc(x_756);
lean_dec(x_747);
x_721 = x_756;
goto block_746;
}
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; 
lean_dec(x_720);
lean_dec(x_719);
lean_dec(x_718);
lean_dec(x_696);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_757 = lean_ctor_get(x_747, 0);
lean_inc(x_757);
x_758 = lean_ctor_get(x_747, 1);
lean_inc(x_758);
if (lean_is_exclusive(x_747)) {
 lean_ctor_release(x_747, 0);
 lean_ctor_release(x_747, 1);
 x_759 = x_747;
} else {
 lean_dec_ref(x_747);
 x_759 = lean_box(0);
}
if (lean_is_scalar(x_759)) {
 x_760 = lean_alloc_ctor(1, 2, 0);
} else {
 x_760 = x_759;
}
lean_ctor_set(x_760, 0, x_757);
lean_ctor_set(x_760, 1, x_758);
x_669 = x_760;
goto block_688;
}
block_746:
{
lean_object* x_722; 
lean_inc(x_18);
lean_inc(x_1);
x_722 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_718, x_719, x_18, x_721);
if (lean_obj_tag(x_722) == 0)
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; 
x_723 = lean_ctor_get(x_722, 1);
lean_inc(x_723);
lean_dec(x_722);
x_724 = lean_unsigned_to_nat(0u);
x_725 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_718, x_718, x_724, x_2);
lean_inc(x_1);
x_726 = l_Lean_Meta_assignExprMVar(x_1, x_725, x_18, x_723);
if (lean_obj_tag(x_726) == 0)
{
lean_object* x_727; lean_object* x_728; 
x_727 = lean_ctor_get(x_726, 1);
lean_inc(x_727);
lean_dec(x_726);
x_728 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_718, x_719, x_18, x_727);
lean_dec(x_719);
if (lean_obj_tag(x_728) == 0)
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; 
x_729 = lean_ctor_get(x_728, 1);
lean_inc(x_729);
lean_dec(x_728);
x_730 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_718, x_724, x_724, x_18, x_729);
x_731 = lean_ctor_get(x_730, 0);
lean_inc(x_731);
x_732 = lean_ctor_get(x_730, 1);
lean_inc(x_732);
lean_dec(x_730);
x_733 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_731, x_18, x_732);
lean_dec(x_731);
x_669 = x_733;
goto block_688;
}
else
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; 
lean_dec(x_718);
lean_dec(x_18);
x_734 = lean_ctor_get(x_728, 0);
lean_inc(x_734);
x_735 = lean_ctor_get(x_728, 1);
lean_inc(x_735);
if (lean_is_exclusive(x_728)) {
 lean_ctor_release(x_728, 0);
 lean_ctor_release(x_728, 1);
 x_736 = x_728;
} else {
 lean_dec_ref(x_728);
 x_736 = lean_box(0);
}
if (lean_is_scalar(x_736)) {
 x_737 = lean_alloc_ctor(1, 2, 0);
} else {
 x_737 = x_736;
}
lean_ctor_set(x_737, 0, x_734);
lean_ctor_set(x_737, 1, x_735);
x_669 = x_737;
goto block_688;
}
}
else
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; 
lean_dec(x_719);
lean_dec(x_718);
lean_dec(x_18);
lean_dec(x_1);
x_738 = lean_ctor_get(x_726, 0);
lean_inc(x_738);
x_739 = lean_ctor_get(x_726, 1);
lean_inc(x_739);
if (lean_is_exclusive(x_726)) {
 lean_ctor_release(x_726, 0);
 lean_ctor_release(x_726, 1);
 x_740 = x_726;
} else {
 lean_dec_ref(x_726);
 x_740 = lean_box(0);
}
if (lean_is_scalar(x_740)) {
 x_741 = lean_alloc_ctor(1, 2, 0);
} else {
 x_741 = x_740;
}
lean_ctor_set(x_741, 0, x_738);
lean_ctor_set(x_741, 1, x_739);
x_669 = x_741;
goto block_688;
}
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
lean_dec(x_719);
lean_dec(x_718);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_742 = lean_ctor_get(x_722, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_722, 1);
lean_inc(x_743);
if (lean_is_exclusive(x_722)) {
 lean_ctor_release(x_722, 0);
 lean_ctor_release(x_722, 1);
 x_744 = x_722;
} else {
 lean_dec_ref(x_722);
 x_744 = lean_box(0);
}
if (lean_is_scalar(x_744)) {
 x_745 = lean_alloc_ctor(1, 2, 0);
} else {
 x_745 = x_744;
}
lean_ctor_set(x_745, 0, x_742);
lean_ctor_set(x_745, 1, x_743);
x_669 = x_745;
goto block_688;
}
}
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; 
lean_dec(x_696);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_761 = lean_ctor_get(x_714, 0);
lean_inc(x_761);
x_762 = lean_ctor_get(x_714, 1);
lean_inc(x_762);
if (lean_is_exclusive(x_714)) {
 lean_ctor_release(x_714, 0);
 lean_ctor_release(x_714, 1);
 x_763 = x_714;
} else {
 lean_dec_ref(x_714);
 x_763 = lean_box(0);
}
if (lean_is_scalar(x_763)) {
 x_764 = lean_alloc_ctor(1, 2, 0);
} else {
 x_764 = x_763;
}
lean_ctor_set(x_764, 0, x_761);
lean_ctor_set(x_764, 1, x_762);
x_669 = x_764;
goto block_688;
}
}
else
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
lean_dec(x_706);
lean_dec(x_699);
lean_dec(x_696);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_765 = lean_ctor_get(x_708, 0);
lean_inc(x_765);
x_766 = lean_ctor_get(x_708, 1);
lean_inc(x_766);
if (lean_is_exclusive(x_708)) {
 lean_ctor_release(x_708, 0);
 lean_ctor_release(x_708, 1);
 x_767 = x_708;
} else {
 lean_dec_ref(x_708);
 x_767 = lean_box(0);
}
if (lean_is_scalar(x_767)) {
 x_768 = lean_alloc_ctor(1, 2, 0);
} else {
 x_768 = x_767;
}
lean_ctor_set(x_768, 0, x_765);
lean_ctor_set(x_768, 1, x_766);
x_669 = x_768;
goto block_688;
}
}
else
{
lean_object* x_769; uint8_t x_770; lean_object* x_771; 
x_769 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_769, 0, x_706);
x_770 = 0;
lean_inc(x_18);
x_771 = l_Lean_Meta_forallMetaTelescopeReducing(x_699, x_769, x_770, x_18, x_705);
lean_dec(x_769);
if (lean_obj_tag(x_771) == 0)
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_804; 
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_772, 1);
lean_inc(x_773);
x_774 = lean_ctor_get(x_771, 1);
lean_inc(x_774);
lean_dec(x_771);
x_775 = lean_ctor_get(x_772, 0);
lean_inc(x_775);
lean_dec(x_772);
x_776 = lean_ctor_get(x_773, 0);
lean_inc(x_776);
x_777 = lean_ctor_get(x_773, 1);
lean_inc(x_777);
lean_dec(x_773);
lean_inc(x_18);
lean_inc(x_696);
lean_inc(x_777);
x_804 = l_Lean_Meta_isExprDefEq(x_777, x_696, x_18, x_774);
if (lean_obj_tag(x_804) == 0)
{
lean_object* x_805; uint8_t x_806; 
x_805 = lean_ctor_get(x_804, 0);
lean_inc(x_805);
x_806 = lean_unbox(x_805);
lean_dec(x_805);
if (x_806 == 0)
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; 
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_2);
x_807 = lean_ctor_get(x_804, 1);
lean_inc(x_807);
lean_dec(x_804);
x_808 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_777, x_696, x_18, x_807);
lean_dec(x_18);
x_809 = lean_ctor_get(x_808, 0);
lean_inc(x_809);
x_810 = lean_ctor_get(x_808, 1);
lean_inc(x_810);
if (lean_is_exclusive(x_808)) {
 lean_ctor_release(x_808, 0);
 lean_ctor_release(x_808, 1);
 x_811 = x_808;
} else {
 lean_dec_ref(x_808);
 x_811 = lean_box(0);
}
if (lean_is_scalar(x_811)) {
 x_812 = lean_alloc_ctor(1, 2, 0);
} else {
 x_812 = x_811;
}
lean_ctor_set(x_812, 0, x_809);
lean_ctor_set(x_812, 1, x_810);
x_669 = x_812;
goto block_688;
}
else
{
lean_object* x_813; 
lean_dec(x_777);
lean_dec(x_696);
x_813 = lean_ctor_get(x_804, 1);
lean_inc(x_813);
lean_dec(x_804);
x_778 = x_813;
goto block_803;
}
}
else
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; 
lean_dec(x_777);
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_696);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_814 = lean_ctor_get(x_804, 0);
lean_inc(x_814);
x_815 = lean_ctor_get(x_804, 1);
lean_inc(x_815);
if (lean_is_exclusive(x_804)) {
 lean_ctor_release(x_804, 0);
 lean_ctor_release(x_804, 1);
 x_816 = x_804;
} else {
 lean_dec_ref(x_804);
 x_816 = lean_box(0);
}
if (lean_is_scalar(x_816)) {
 x_817 = lean_alloc_ctor(1, 2, 0);
} else {
 x_817 = x_816;
}
lean_ctor_set(x_817, 0, x_814);
lean_ctor_set(x_817, 1, x_815);
x_669 = x_817;
goto block_688;
}
block_803:
{
lean_object* x_779; 
lean_inc(x_18);
lean_inc(x_1);
x_779 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_775, x_776, x_18, x_778);
if (lean_obj_tag(x_779) == 0)
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
x_780 = lean_ctor_get(x_779, 1);
lean_inc(x_780);
lean_dec(x_779);
x_781 = lean_unsigned_to_nat(0u);
x_782 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_775, x_775, x_781, x_2);
lean_inc(x_1);
x_783 = l_Lean_Meta_assignExprMVar(x_1, x_782, x_18, x_780);
if (lean_obj_tag(x_783) == 0)
{
lean_object* x_784; lean_object* x_785; 
x_784 = lean_ctor_get(x_783, 1);
lean_inc(x_784);
lean_dec(x_783);
x_785 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_775, x_776, x_18, x_784);
lean_dec(x_776);
if (lean_obj_tag(x_785) == 0)
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_786 = lean_ctor_get(x_785, 1);
lean_inc(x_786);
lean_dec(x_785);
x_787 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_775, x_781, x_781, x_18, x_786);
x_788 = lean_ctor_get(x_787, 0);
lean_inc(x_788);
x_789 = lean_ctor_get(x_787, 1);
lean_inc(x_789);
lean_dec(x_787);
x_790 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_788, x_18, x_789);
lean_dec(x_788);
x_669 = x_790;
goto block_688;
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; 
lean_dec(x_775);
lean_dec(x_18);
x_791 = lean_ctor_get(x_785, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_785, 1);
lean_inc(x_792);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 lean_ctor_release(x_785, 1);
 x_793 = x_785;
} else {
 lean_dec_ref(x_785);
 x_793 = lean_box(0);
}
if (lean_is_scalar(x_793)) {
 x_794 = lean_alloc_ctor(1, 2, 0);
} else {
 x_794 = x_793;
}
lean_ctor_set(x_794, 0, x_791);
lean_ctor_set(x_794, 1, x_792);
x_669 = x_794;
goto block_688;
}
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_18);
lean_dec(x_1);
x_795 = lean_ctor_get(x_783, 0);
lean_inc(x_795);
x_796 = lean_ctor_get(x_783, 1);
lean_inc(x_796);
if (lean_is_exclusive(x_783)) {
 lean_ctor_release(x_783, 0);
 lean_ctor_release(x_783, 1);
 x_797 = x_783;
} else {
 lean_dec_ref(x_783);
 x_797 = lean_box(0);
}
if (lean_is_scalar(x_797)) {
 x_798 = lean_alloc_ctor(1, 2, 0);
} else {
 x_798 = x_797;
}
lean_ctor_set(x_798, 0, x_795);
lean_ctor_set(x_798, 1, x_796);
x_669 = x_798;
goto block_688;
}
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; 
lean_dec(x_776);
lean_dec(x_775);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_799 = lean_ctor_get(x_779, 0);
lean_inc(x_799);
x_800 = lean_ctor_get(x_779, 1);
lean_inc(x_800);
if (lean_is_exclusive(x_779)) {
 lean_ctor_release(x_779, 0);
 lean_ctor_release(x_779, 1);
 x_801 = x_779;
} else {
 lean_dec_ref(x_779);
 x_801 = lean_box(0);
}
if (lean_is_scalar(x_801)) {
 x_802 = lean_alloc_ctor(1, 2, 0);
} else {
 x_802 = x_801;
}
lean_ctor_set(x_802, 0, x_799);
lean_ctor_set(x_802, 1, x_800);
x_669 = x_802;
goto block_688;
}
}
}
else
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; 
lean_dec(x_696);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_818 = lean_ctor_get(x_771, 0);
lean_inc(x_818);
x_819 = lean_ctor_get(x_771, 1);
lean_inc(x_819);
if (lean_is_exclusive(x_771)) {
 lean_ctor_release(x_771, 0);
 lean_ctor_release(x_771, 1);
 x_820 = x_771;
} else {
 lean_dec_ref(x_771);
 x_820 = lean_box(0);
}
if (lean_is_scalar(x_820)) {
 x_821 = lean_alloc_ctor(1, 2, 0);
} else {
 x_821 = x_820;
}
lean_ctor_set(x_821, 0, x_818);
lean_ctor_set(x_821, 1, x_819);
x_669 = x_821;
goto block_688;
}
}
}
else
{
lean_object* x_822; lean_object* x_823; uint8_t x_824; 
x_822 = lean_ctor_get(x_701, 1);
lean_inc(x_822);
lean_dec(x_701);
x_823 = lean_ctor_get(x_702, 0);
lean_inc(x_823);
lean_dec(x_702);
x_824 = l_String_posOfAux___main___closed__1;
if (x_824 == 0)
{
lean_object* x_825; 
lean_inc(x_18);
lean_inc(x_696);
x_825 = l___private_Init_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(x_696, x_18, x_822);
if (lean_obj_tag(x_825) == 0)
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; uint8_t x_830; lean_object* x_831; 
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_825, 1);
lean_inc(x_827);
lean_dec(x_825);
x_828 = lean_nat_sub(x_823, x_826);
lean_dec(x_826);
lean_dec(x_823);
x_829 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_829, 0, x_828);
x_830 = 0;
lean_inc(x_18);
x_831 = l_Lean_Meta_forallMetaTelescopeReducing(x_699, x_829, x_830, x_18, x_827);
lean_dec(x_829);
if (lean_obj_tag(x_831) == 0)
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_864; 
x_832 = lean_ctor_get(x_831, 0);
lean_inc(x_832);
x_833 = lean_ctor_get(x_832, 1);
lean_inc(x_833);
x_834 = lean_ctor_get(x_831, 1);
lean_inc(x_834);
lean_dec(x_831);
x_835 = lean_ctor_get(x_832, 0);
lean_inc(x_835);
lean_dec(x_832);
x_836 = lean_ctor_get(x_833, 0);
lean_inc(x_836);
x_837 = lean_ctor_get(x_833, 1);
lean_inc(x_837);
lean_dec(x_833);
lean_inc(x_18);
lean_inc(x_696);
lean_inc(x_837);
x_864 = l_Lean_Meta_isExprDefEq(x_837, x_696, x_18, x_834);
if (lean_obj_tag(x_864) == 0)
{
lean_object* x_865; uint8_t x_866; 
x_865 = lean_ctor_get(x_864, 0);
lean_inc(x_865);
x_866 = lean_unbox(x_865);
lean_dec(x_865);
if (x_866 == 0)
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
lean_dec(x_836);
lean_dec(x_835);
lean_dec(x_2);
x_867 = lean_ctor_get(x_864, 1);
lean_inc(x_867);
lean_dec(x_864);
x_868 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_837, x_696, x_18, x_867);
lean_dec(x_18);
x_869 = lean_ctor_get(x_868, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_868, 1);
lean_inc(x_870);
if (lean_is_exclusive(x_868)) {
 lean_ctor_release(x_868, 0);
 lean_ctor_release(x_868, 1);
 x_871 = x_868;
} else {
 lean_dec_ref(x_868);
 x_871 = lean_box(0);
}
if (lean_is_scalar(x_871)) {
 x_872 = lean_alloc_ctor(1, 2, 0);
} else {
 x_872 = x_871;
}
lean_ctor_set(x_872, 0, x_869);
lean_ctor_set(x_872, 1, x_870);
x_669 = x_872;
goto block_688;
}
else
{
lean_object* x_873; 
lean_dec(x_837);
lean_dec(x_696);
x_873 = lean_ctor_get(x_864, 1);
lean_inc(x_873);
lean_dec(x_864);
x_838 = x_873;
goto block_863;
}
}
else
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; 
lean_dec(x_837);
lean_dec(x_836);
lean_dec(x_835);
lean_dec(x_696);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_874 = lean_ctor_get(x_864, 0);
lean_inc(x_874);
x_875 = lean_ctor_get(x_864, 1);
lean_inc(x_875);
if (lean_is_exclusive(x_864)) {
 lean_ctor_release(x_864, 0);
 lean_ctor_release(x_864, 1);
 x_876 = x_864;
} else {
 lean_dec_ref(x_864);
 x_876 = lean_box(0);
}
if (lean_is_scalar(x_876)) {
 x_877 = lean_alloc_ctor(1, 2, 0);
} else {
 x_877 = x_876;
}
lean_ctor_set(x_877, 0, x_874);
lean_ctor_set(x_877, 1, x_875);
x_669 = x_877;
goto block_688;
}
block_863:
{
lean_object* x_839; 
lean_inc(x_18);
lean_inc(x_1);
x_839 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_835, x_836, x_18, x_838);
if (lean_obj_tag(x_839) == 0)
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; 
x_840 = lean_ctor_get(x_839, 1);
lean_inc(x_840);
lean_dec(x_839);
x_841 = lean_unsigned_to_nat(0u);
x_842 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_835, x_835, x_841, x_2);
lean_inc(x_1);
x_843 = l_Lean_Meta_assignExprMVar(x_1, x_842, x_18, x_840);
if (lean_obj_tag(x_843) == 0)
{
lean_object* x_844; lean_object* x_845; 
x_844 = lean_ctor_get(x_843, 1);
lean_inc(x_844);
lean_dec(x_843);
x_845 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_835, x_836, x_18, x_844);
lean_dec(x_836);
if (lean_obj_tag(x_845) == 0)
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; 
x_846 = lean_ctor_get(x_845, 1);
lean_inc(x_846);
lean_dec(x_845);
x_847 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_835, x_841, x_841, x_18, x_846);
x_848 = lean_ctor_get(x_847, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_847, 1);
lean_inc(x_849);
lean_dec(x_847);
x_850 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_848, x_18, x_849);
lean_dec(x_848);
x_669 = x_850;
goto block_688;
}
else
{
lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; 
lean_dec(x_835);
lean_dec(x_18);
x_851 = lean_ctor_get(x_845, 0);
lean_inc(x_851);
x_852 = lean_ctor_get(x_845, 1);
lean_inc(x_852);
if (lean_is_exclusive(x_845)) {
 lean_ctor_release(x_845, 0);
 lean_ctor_release(x_845, 1);
 x_853 = x_845;
} else {
 lean_dec_ref(x_845);
 x_853 = lean_box(0);
}
if (lean_is_scalar(x_853)) {
 x_854 = lean_alloc_ctor(1, 2, 0);
} else {
 x_854 = x_853;
}
lean_ctor_set(x_854, 0, x_851);
lean_ctor_set(x_854, 1, x_852);
x_669 = x_854;
goto block_688;
}
}
else
{
lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; 
lean_dec(x_836);
lean_dec(x_835);
lean_dec(x_18);
lean_dec(x_1);
x_855 = lean_ctor_get(x_843, 0);
lean_inc(x_855);
x_856 = lean_ctor_get(x_843, 1);
lean_inc(x_856);
if (lean_is_exclusive(x_843)) {
 lean_ctor_release(x_843, 0);
 lean_ctor_release(x_843, 1);
 x_857 = x_843;
} else {
 lean_dec_ref(x_843);
 x_857 = lean_box(0);
}
if (lean_is_scalar(x_857)) {
 x_858 = lean_alloc_ctor(1, 2, 0);
} else {
 x_858 = x_857;
}
lean_ctor_set(x_858, 0, x_855);
lean_ctor_set(x_858, 1, x_856);
x_669 = x_858;
goto block_688;
}
}
else
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; 
lean_dec(x_836);
lean_dec(x_835);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_859 = lean_ctor_get(x_839, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_839, 1);
lean_inc(x_860);
if (lean_is_exclusive(x_839)) {
 lean_ctor_release(x_839, 0);
 lean_ctor_release(x_839, 1);
 x_861 = x_839;
} else {
 lean_dec_ref(x_839);
 x_861 = lean_box(0);
}
if (lean_is_scalar(x_861)) {
 x_862 = lean_alloc_ctor(1, 2, 0);
} else {
 x_862 = x_861;
}
lean_ctor_set(x_862, 0, x_859);
lean_ctor_set(x_862, 1, x_860);
x_669 = x_862;
goto block_688;
}
}
}
else
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; 
lean_dec(x_696);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_878 = lean_ctor_get(x_831, 0);
lean_inc(x_878);
x_879 = lean_ctor_get(x_831, 1);
lean_inc(x_879);
if (lean_is_exclusive(x_831)) {
 lean_ctor_release(x_831, 0);
 lean_ctor_release(x_831, 1);
 x_880 = x_831;
} else {
 lean_dec_ref(x_831);
 x_880 = lean_box(0);
}
if (lean_is_scalar(x_880)) {
 x_881 = lean_alloc_ctor(1, 2, 0);
} else {
 x_881 = x_880;
}
lean_ctor_set(x_881, 0, x_878);
lean_ctor_set(x_881, 1, x_879);
x_669 = x_881;
goto block_688;
}
}
else
{
lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; 
lean_dec(x_823);
lean_dec(x_699);
lean_dec(x_696);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_882 = lean_ctor_get(x_825, 0);
lean_inc(x_882);
x_883 = lean_ctor_get(x_825, 1);
lean_inc(x_883);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 lean_ctor_release(x_825, 1);
 x_884 = x_825;
} else {
 lean_dec_ref(x_825);
 x_884 = lean_box(0);
}
if (lean_is_scalar(x_884)) {
 x_885 = lean_alloc_ctor(1, 2, 0);
} else {
 x_885 = x_884;
}
lean_ctor_set(x_885, 0, x_882);
lean_ctor_set(x_885, 1, x_883);
x_669 = x_885;
goto block_688;
}
}
else
{
lean_object* x_886; uint8_t x_887; lean_object* x_888; 
x_886 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_886, 0, x_823);
x_887 = 0;
lean_inc(x_18);
x_888 = l_Lean_Meta_forallMetaTelescopeReducing(x_699, x_886, x_887, x_18, x_822);
lean_dec(x_886);
if (lean_obj_tag(x_888) == 0)
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; lean_object* x_921; 
x_889 = lean_ctor_get(x_888, 0);
lean_inc(x_889);
x_890 = lean_ctor_get(x_889, 1);
lean_inc(x_890);
x_891 = lean_ctor_get(x_888, 1);
lean_inc(x_891);
lean_dec(x_888);
x_892 = lean_ctor_get(x_889, 0);
lean_inc(x_892);
lean_dec(x_889);
x_893 = lean_ctor_get(x_890, 0);
lean_inc(x_893);
x_894 = lean_ctor_get(x_890, 1);
lean_inc(x_894);
lean_dec(x_890);
lean_inc(x_18);
lean_inc(x_696);
lean_inc(x_894);
x_921 = l_Lean_Meta_isExprDefEq(x_894, x_696, x_18, x_891);
if (lean_obj_tag(x_921) == 0)
{
lean_object* x_922; uint8_t x_923; 
x_922 = lean_ctor_get(x_921, 0);
lean_inc(x_922);
x_923 = lean_unbox(x_922);
lean_dec(x_922);
if (x_923 == 0)
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; 
lean_dec(x_893);
lean_dec(x_892);
lean_dec(x_2);
x_924 = lean_ctor_get(x_921, 1);
lean_inc(x_924);
lean_dec(x_921);
x_925 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_894, x_696, x_18, x_924);
lean_dec(x_18);
x_926 = lean_ctor_get(x_925, 0);
lean_inc(x_926);
x_927 = lean_ctor_get(x_925, 1);
lean_inc(x_927);
if (lean_is_exclusive(x_925)) {
 lean_ctor_release(x_925, 0);
 lean_ctor_release(x_925, 1);
 x_928 = x_925;
} else {
 lean_dec_ref(x_925);
 x_928 = lean_box(0);
}
if (lean_is_scalar(x_928)) {
 x_929 = lean_alloc_ctor(1, 2, 0);
} else {
 x_929 = x_928;
}
lean_ctor_set(x_929, 0, x_926);
lean_ctor_set(x_929, 1, x_927);
x_669 = x_929;
goto block_688;
}
else
{
lean_object* x_930; 
lean_dec(x_894);
lean_dec(x_696);
x_930 = lean_ctor_get(x_921, 1);
lean_inc(x_930);
lean_dec(x_921);
x_895 = x_930;
goto block_920;
}
}
else
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
lean_dec(x_894);
lean_dec(x_893);
lean_dec(x_892);
lean_dec(x_696);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_931 = lean_ctor_get(x_921, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_921, 1);
lean_inc(x_932);
if (lean_is_exclusive(x_921)) {
 lean_ctor_release(x_921, 0);
 lean_ctor_release(x_921, 1);
 x_933 = x_921;
} else {
 lean_dec_ref(x_921);
 x_933 = lean_box(0);
}
if (lean_is_scalar(x_933)) {
 x_934 = lean_alloc_ctor(1, 2, 0);
} else {
 x_934 = x_933;
}
lean_ctor_set(x_934, 0, x_931);
lean_ctor_set(x_934, 1, x_932);
x_669 = x_934;
goto block_688;
}
block_920:
{
lean_object* x_896; 
lean_inc(x_18);
lean_inc(x_1);
x_896 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_892, x_893, x_18, x_895);
if (lean_obj_tag(x_896) == 0)
{
lean_object* x_897; lean_object* x_898; lean_object* x_899; lean_object* x_900; 
x_897 = lean_ctor_get(x_896, 1);
lean_inc(x_897);
lean_dec(x_896);
x_898 = lean_unsigned_to_nat(0u);
x_899 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_892, x_892, x_898, x_2);
lean_inc(x_1);
x_900 = l_Lean_Meta_assignExprMVar(x_1, x_899, x_18, x_897);
if (lean_obj_tag(x_900) == 0)
{
lean_object* x_901; lean_object* x_902; 
x_901 = lean_ctor_get(x_900, 1);
lean_inc(x_901);
lean_dec(x_900);
x_902 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_892, x_893, x_18, x_901);
lean_dec(x_893);
if (lean_obj_tag(x_902) == 0)
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; 
x_903 = lean_ctor_get(x_902, 1);
lean_inc(x_903);
lean_dec(x_902);
x_904 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_892, x_898, x_898, x_18, x_903);
x_905 = lean_ctor_get(x_904, 0);
lean_inc(x_905);
x_906 = lean_ctor_get(x_904, 1);
lean_inc(x_906);
lean_dec(x_904);
x_907 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_905, x_18, x_906);
lean_dec(x_905);
x_669 = x_907;
goto block_688;
}
else
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; 
lean_dec(x_892);
lean_dec(x_18);
x_908 = lean_ctor_get(x_902, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_902, 1);
lean_inc(x_909);
if (lean_is_exclusive(x_902)) {
 lean_ctor_release(x_902, 0);
 lean_ctor_release(x_902, 1);
 x_910 = x_902;
} else {
 lean_dec_ref(x_902);
 x_910 = lean_box(0);
}
if (lean_is_scalar(x_910)) {
 x_911 = lean_alloc_ctor(1, 2, 0);
} else {
 x_911 = x_910;
}
lean_ctor_set(x_911, 0, x_908);
lean_ctor_set(x_911, 1, x_909);
x_669 = x_911;
goto block_688;
}
}
else
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; 
lean_dec(x_893);
lean_dec(x_892);
lean_dec(x_18);
lean_dec(x_1);
x_912 = lean_ctor_get(x_900, 0);
lean_inc(x_912);
x_913 = lean_ctor_get(x_900, 1);
lean_inc(x_913);
if (lean_is_exclusive(x_900)) {
 lean_ctor_release(x_900, 0);
 lean_ctor_release(x_900, 1);
 x_914 = x_900;
} else {
 lean_dec_ref(x_900);
 x_914 = lean_box(0);
}
if (lean_is_scalar(x_914)) {
 x_915 = lean_alloc_ctor(1, 2, 0);
} else {
 x_915 = x_914;
}
lean_ctor_set(x_915, 0, x_912);
lean_ctor_set(x_915, 1, x_913);
x_669 = x_915;
goto block_688;
}
}
else
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; lean_object* x_919; 
lean_dec(x_893);
lean_dec(x_892);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_916 = lean_ctor_get(x_896, 0);
lean_inc(x_916);
x_917 = lean_ctor_get(x_896, 1);
lean_inc(x_917);
if (lean_is_exclusive(x_896)) {
 lean_ctor_release(x_896, 0);
 lean_ctor_release(x_896, 1);
 x_918 = x_896;
} else {
 lean_dec_ref(x_896);
 x_918 = lean_box(0);
}
if (lean_is_scalar(x_918)) {
 x_919 = lean_alloc_ctor(1, 2, 0);
} else {
 x_919 = x_918;
}
lean_ctor_set(x_919, 0, x_916);
lean_ctor_set(x_919, 1, x_917);
x_669 = x_919;
goto block_688;
}
}
}
else
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
lean_dec(x_696);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_935 = lean_ctor_get(x_888, 0);
lean_inc(x_935);
x_936 = lean_ctor_get(x_888, 1);
lean_inc(x_936);
if (lean_is_exclusive(x_888)) {
 lean_ctor_release(x_888, 0);
 lean_ctor_release(x_888, 1);
 x_937 = x_888;
} else {
 lean_dec_ref(x_888);
 x_937 = lean_box(0);
}
if (lean_is_scalar(x_937)) {
 x_938 = lean_alloc_ctor(1, 2, 0);
} else {
 x_938 = x_937;
}
lean_ctor_set(x_938, 0, x_935);
lean_ctor_set(x_938, 1, x_936);
x_669 = x_938;
goto block_688;
}
}
}
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; 
lean_dec(x_699);
lean_dec(x_696);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_939 = lean_ctor_get(x_701, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_701, 1);
lean_inc(x_940);
if (lean_is_exclusive(x_701)) {
 lean_ctor_release(x_701, 0);
 lean_ctor_release(x_701, 1);
 x_941 = x_701;
} else {
 lean_dec_ref(x_701);
 x_941 = lean_box(0);
}
if (lean_is_scalar(x_941)) {
 x_942 = lean_alloc_ctor(1, 2, 0);
} else {
 x_942 = x_941;
}
lean_ctor_set(x_942, 0, x_939);
lean_ctor_set(x_942, 1, x_940);
x_669 = x_942;
goto block_688;
}
}
else
{
lean_object* x_943; lean_object* x_944; 
lean_dec(x_696);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_943 = lean_ctor_get(x_698, 0);
lean_inc(x_943);
x_944 = lean_ctor_get(x_698, 1);
lean_inc(x_944);
lean_dec(x_698);
x_653 = x_943;
x_654 = x_944;
goto block_668;
}
}
else
{
lean_object* x_945; lean_object* x_946; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_945 = lean_ctor_get(x_695, 0);
lean_inc(x_945);
x_946 = lean_ctor_get(x_695, 1);
lean_inc(x_946);
lean_dec(x_695);
x_653 = x_945;
x_654 = x_946;
goto block_668;
}
}
else
{
lean_object* x_947; lean_object* x_948; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_947 = lean_ctor_get(x_693, 0);
lean_inc(x_947);
x_948 = lean_ctor_get(x_693, 1);
lean_inc(x_948);
lean_dec(x_693);
x_653 = x_947;
x_654 = x_948;
goto block_668;
}
block_668:
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_655 = lean_ctor_get(x_654, 2);
lean_inc(x_655);
x_656 = lean_ctor_get(x_654, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_654, 1);
lean_inc(x_657);
x_658 = lean_ctor_get(x_654, 3);
lean_inc(x_658);
x_659 = lean_ctor_get(x_654, 4);
lean_inc(x_659);
x_660 = lean_ctor_get(x_654, 5);
lean_inc(x_660);
if (lean_is_exclusive(x_654)) {
 lean_ctor_release(x_654, 0);
 lean_ctor_release(x_654, 1);
 lean_ctor_release(x_654, 2);
 lean_ctor_release(x_654, 3);
 lean_ctor_release(x_654, 4);
 lean_ctor_release(x_654, 5);
 x_661 = x_654;
} else {
 lean_dec_ref(x_654);
 x_661 = lean_box(0);
}
x_662 = lean_ctor_get(x_655, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_655, 1);
lean_inc(x_663);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 lean_ctor_release(x_655, 1);
 lean_ctor_release(x_655, 2);
 x_664 = x_655;
} else {
 lean_dec_ref(x_655);
 x_664 = lean_box(0);
}
if (lean_is_scalar(x_664)) {
 x_665 = lean_alloc_ctor(0, 3, 0);
} else {
 x_665 = x_664;
}
lean_ctor_set(x_665, 0, x_662);
lean_ctor_set(x_665, 1, x_663);
lean_ctor_set(x_665, 2, x_651);
if (lean_is_scalar(x_661)) {
 x_666 = lean_alloc_ctor(0, 6, 0);
} else {
 x_666 = x_661;
}
lean_ctor_set(x_666, 0, x_656);
lean_ctor_set(x_666, 1, x_657);
lean_ctor_set(x_666, 2, x_665);
lean_ctor_set(x_666, 3, x_658);
lean_ctor_set(x_666, 4, x_659);
lean_ctor_set(x_666, 5, x_660);
if (lean_is_scalar(x_8)) {
 x_667 = lean_alloc_ctor(1, 2, 0);
} else {
 x_667 = x_8;
 lean_ctor_set_tag(x_667, 1);
}
lean_ctor_set(x_667, 0, x_653);
lean_ctor_set(x_667, 1, x_666);
return x_667;
}
block_688:
{
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; 
lean_dec(x_8);
x_670 = lean_ctor_get(x_669, 1);
lean_inc(x_670);
x_671 = lean_ctor_get(x_670, 2);
lean_inc(x_671);
x_672 = lean_ctor_get(x_669, 0);
lean_inc(x_672);
if (lean_is_exclusive(x_669)) {
 lean_ctor_release(x_669, 0);
 lean_ctor_release(x_669, 1);
 x_673 = x_669;
} else {
 lean_dec_ref(x_669);
 x_673 = lean_box(0);
}
x_674 = lean_ctor_get(x_670, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_670, 1);
lean_inc(x_675);
x_676 = lean_ctor_get(x_670, 3);
lean_inc(x_676);
x_677 = lean_ctor_get(x_670, 4);
lean_inc(x_677);
x_678 = lean_ctor_get(x_670, 5);
lean_inc(x_678);
if (lean_is_exclusive(x_670)) {
 lean_ctor_release(x_670, 0);
 lean_ctor_release(x_670, 1);
 lean_ctor_release(x_670, 2);
 lean_ctor_release(x_670, 3);
 lean_ctor_release(x_670, 4);
 lean_ctor_release(x_670, 5);
 x_679 = x_670;
} else {
 lean_dec_ref(x_670);
 x_679 = lean_box(0);
}
x_680 = lean_ctor_get(x_671, 0);
lean_inc(x_680);
x_681 = lean_ctor_get(x_671, 1);
lean_inc(x_681);
if (lean_is_exclusive(x_671)) {
 lean_ctor_release(x_671, 0);
 lean_ctor_release(x_671, 1);
 lean_ctor_release(x_671, 2);
 x_682 = x_671;
} else {
 lean_dec_ref(x_671);
 x_682 = lean_box(0);
}
if (lean_is_scalar(x_682)) {
 x_683 = lean_alloc_ctor(0, 3, 0);
} else {
 x_683 = x_682;
}
lean_ctor_set(x_683, 0, x_680);
lean_ctor_set(x_683, 1, x_681);
lean_ctor_set(x_683, 2, x_651);
if (lean_is_scalar(x_679)) {
 x_684 = lean_alloc_ctor(0, 6, 0);
} else {
 x_684 = x_679;
}
lean_ctor_set(x_684, 0, x_674);
lean_ctor_set(x_684, 1, x_675);
lean_ctor_set(x_684, 2, x_683);
lean_ctor_set(x_684, 3, x_676);
lean_ctor_set(x_684, 4, x_677);
lean_ctor_set(x_684, 5, x_678);
if (lean_is_scalar(x_673)) {
 x_685 = lean_alloc_ctor(0, 2, 0);
} else {
 x_685 = x_673;
}
lean_ctor_set(x_685, 0, x_672);
lean_ctor_set(x_685, 1, x_684);
return x_685;
}
else
{
lean_object* x_686; lean_object* x_687; 
x_686 = lean_ctor_get(x_669, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_669, 1);
lean_inc(x_687);
lean_dec(x_669);
x_653 = x_686;
x_654 = x_687;
goto block_668;
}
}
}
}
else
{
lean_object* x_949; lean_object* x_950; 
lean_dec(x_8);
x_949 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2;
lean_inc(x_1);
x_950 = l_Lean_Meta_checkNotAssigned(x_1, x_949, x_18, x_7);
if (lean_obj_tag(x_950) == 0)
{
lean_object* x_951; lean_object* x_952; 
x_951 = lean_ctor_get(x_950, 1);
lean_inc(x_951);
lean_dec(x_950);
lean_inc(x_1);
x_952 = l_Lean_Meta_getMVarType(x_1, x_18, x_951);
if (lean_obj_tag(x_952) == 0)
{
lean_object* x_953; lean_object* x_954; lean_object* x_955; 
x_953 = lean_ctor_get(x_952, 0);
lean_inc(x_953);
x_954 = lean_ctor_get(x_952, 1);
lean_inc(x_954);
lean_dec(x_952);
lean_inc(x_18);
lean_inc(x_2);
x_955 = l_Lean_Meta_inferType(x_2, x_18, x_954);
if (lean_obj_tag(x_955) == 0)
{
lean_object* x_956; lean_object* x_957; lean_object* x_958; 
x_956 = lean_ctor_get(x_955, 0);
lean_inc(x_956);
x_957 = lean_ctor_get(x_955, 1);
lean_inc(x_957);
lean_dec(x_955);
lean_inc(x_18);
lean_inc(x_956);
x_958 = l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux(x_956, x_18, x_957);
if (lean_obj_tag(x_958) == 0)
{
lean_object* x_959; lean_object* x_960; uint8_t x_961; 
x_959 = lean_ctor_get(x_958, 0);
lean_inc(x_959);
x_960 = lean_ctor_get(x_959, 1);
lean_inc(x_960);
x_961 = lean_unbox(x_960);
lean_dec(x_960);
if (x_961 == 0)
{
lean_object* x_962; lean_object* x_963; uint8_t x_964; 
x_962 = lean_ctor_get(x_958, 1);
lean_inc(x_962);
lean_dec(x_958);
x_963 = lean_ctor_get(x_959, 0);
lean_inc(x_963);
lean_dec(x_959);
x_964 = l_String_posOfAux___main___closed__2;
if (x_964 == 0)
{
lean_object* x_965; 
lean_inc(x_18);
lean_inc(x_953);
x_965 = l___private_Init_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(x_953, x_18, x_962);
if (lean_obj_tag(x_965) == 0)
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; uint8_t x_970; lean_object* x_971; 
x_966 = lean_ctor_get(x_965, 0);
lean_inc(x_966);
x_967 = lean_ctor_get(x_965, 1);
lean_inc(x_967);
lean_dec(x_965);
x_968 = lean_nat_sub(x_963, x_966);
lean_dec(x_966);
lean_dec(x_963);
x_969 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_969, 0, x_968);
x_970 = 0;
lean_inc(x_18);
x_971 = l_Lean_Meta_forallMetaTelescopeReducing(x_956, x_969, x_970, x_18, x_967);
lean_dec(x_969);
if (lean_obj_tag(x_971) == 0)
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_1004; 
x_972 = lean_ctor_get(x_971, 0);
lean_inc(x_972);
x_973 = lean_ctor_get(x_972, 1);
lean_inc(x_973);
x_974 = lean_ctor_get(x_971, 1);
lean_inc(x_974);
lean_dec(x_971);
x_975 = lean_ctor_get(x_972, 0);
lean_inc(x_975);
lean_dec(x_972);
x_976 = lean_ctor_get(x_973, 0);
lean_inc(x_976);
x_977 = lean_ctor_get(x_973, 1);
lean_inc(x_977);
lean_dec(x_973);
lean_inc(x_18);
lean_inc(x_953);
lean_inc(x_977);
x_1004 = l_Lean_Meta_isExprDefEq(x_977, x_953, x_18, x_974);
if (lean_obj_tag(x_1004) == 0)
{
lean_object* x_1005; uint8_t x_1006; 
x_1005 = lean_ctor_get(x_1004, 0);
lean_inc(x_1005);
x_1006 = lean_unbox(x_1005);
lean_dec(x_1005);
if (x_1006 == 0)
{
lean_object* x_1007; lean_object* x_1008; uint8_t x_1009; 
lean_dec(x_976);
lean_dec(x_975);
lean_dec(x_2);
x_1007 = lean_ctor_get(x_1004, 1);
lean_inc(x_1007);
lean_dec(x_1004);
x_1008 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_977, x_953, x_18, x_1007);
lean_dec(x_18);
x_1009 = !lean_is_exclusive(x_1008);
if (x_1009 == 0)
{
return x_1008;
}
else
{
lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
x_1010 = lean_ctor_get(x_1008, 0);
x_1011 = lean_ctor_get(x_1008, 1);
lean_inc(x_1011);
lean_inc(x_1010);
lean_dec(x_1008);
x_1012 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1012, 0, x_1010);
lean_ctor_set(x_1012, 1, x_1011);
return x_1012;
}
}
else
{
lean_object* x_1013; 
lean_dec(x_977);
lean_dec(x_953);
x_1013 = lean_ctor_get(x_1004, 1);
lean_inc(x_1013);
lean_dec(x_1004);
x_978 = x_1013;
goto block_1003;
}
}
else
{
uint8_t x_1014; 
lean_dec(x_977);
lean_dec(x_976);
lean_dec(x_975);
lean_dec(x_953);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_1014 = !lean_is_exclusive(x_1004);
if (x_1014 == 0)
{
return x_1004;
}
else
{
lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; 
x_1015 = lean_ctor_get(x_1004, 0);
x_1016 = lean_ctor_get(x_1004, 1);
lean_inc(x_1016);
lean_inc(x_1015);
lean_dec(x_1004);
x_1017 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1017, 0, x_1015);
lean_ctor_set(x_1017, 1, x_1016);
return x_1017;
}
}
block_1003:
{
lean_object* x_979; 
lean_inc(x_18);
lean_inc(x_1);
x_979 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_975, x_976, x_18, x_978);
if (lean_obj_tag(x_979) == 0)
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; 
x_980 = lean_ctor_get(x_979, 1);
lean_inc(x_980);
lean_dec(x_979);
x_981 = lean_unsigned_to_nat(0u);
x_982 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_975, x_975, x_981, x_2);
lean_inc(x_1);
x_983 = l_Lean_Meta_assignExprMVar(x_1, x_982, x_18, x_980);
if (lean_obj_tag(x_983) == 0)
{
lean_object* x_984; lean_object* x_985; 
x_984 = lean_ctor_get(x_983, 1);
lean_inc(x_984);
lean_dec(x_983);
x_985 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_975, x_976, x_18, x_984);
lean_dec(x_976);
if (lean_obj_tag(x_985) == 0)
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; 
x_986 = lean_ctor_get(x_985, 1);
lean_inc(x_986);
lean_dec(x_985);
x_987 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_975, x_981, x_981, x_18, x_986);
x_988 = lean_ctor_get(x_987, 0);
lean_inc(x_988);
x_989 = lean_ctor_get(x_987, 1);
lean_inc(x_989);
lean_dec(x_987);
x_990 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_988, x_18, x_989);
lean_dec(x_988);
return x_990;
}
else
{
uint8_t x_991; 
lean_dec(x_975);
lean_dec(x_18);
x_991 = !lean_is_exclusive(x_985);
if (x_991 == 0)
{
return x_985;
}
else
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; 
x_992 = lean_ctor_get(x_985, 0);
x_993 = lean_ctor_get(x_985, 1);
lean_inc(x_993);
lean_inc(x_992);
lean_dec(x_985);
x_994 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_994, 0, x_992);
lean_ctor_set(x_994, 1, x_993);
return x_994;
}
}
}
else
{
uint8_t x_995; 
lean_dec(x_976);
lean_dec(x_975);
lean_dec(x_18);
lean_dec(x_1);
x_995 = !lean_is_exclusive(x_983);
if (x_995 == 0)
{
return x_983;
}
else
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; 
x_996 = lean_ctor_get(x_983, 0);
x_997 = lean_ctor_get(x_983, 1);
lean_inc(x_997);
lean_inc(x_996);
lean_dec(x_983);
x_998 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_998, 0, x_996);
lean_ctor_set(x_998, 1, x_997);
return x_998;
}
}
}
else
{
uint8_t x_999; 
lean_dec(x_976);
lean_dec(x_975);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_999 = !lean_is_exclusive(x_979);
if (x_999 == 0)
{
return x_979;
}
else
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; 
x_1000 = lean_ctor_get(x_979, 0);
x_1001 = lean_ctor_get(x_979, 1);
lean_inc(x_1001);
lean_inc(x_1000);
lean_dec(x_979);
x_1002 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1002, 0, x_1000);
lean_ctor_set(x_1002, 1, x_1001);
return x_1002;
}
}
}
}
else
{
uint8_t x_1018; 
lean_dec(x_953);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_1018 = !lean_is_exclusive(x_971);
if (x_1018 == 0)
{
return x_971;
}
else
{
lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; 
x_1019 = lean_ctor_get(x_971, 0);
x_1020 = lean_ctor_get(x_971, 1);
lean_inc(x_1020);
lean_inc(x_1019);
lean_dec(x_971);
x_1021 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1021, 0, x_1019);
lean_ctor_set(x_1021, 1, x_1020);
return x_1021;
}
}
}
else
{
uint8_t x_1022; 
lean_dec(x_963);
lean_dec(x_956);
lean_dec(x_953);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_1022 = !lean_is_exclusive(x_965);
if (x_1022 == 0)
{
return x_965;
}
else
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; 
x_1023 = lean_ctor_get(x_965, 0);
x_1024 = lean_ctor_get(x_965, 1);
lean_inc(x_1024);
lean_inc(x_1023);
lean_dec(x_965);
x_1025 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1025, 0, x_1023);
lean_ctor_set(x_1025, 1, x_1024);
return x_1025;
}
}
}
else
{
lean_object* x_1026; uint8_t x_1027; lean_object* x_1028; 
x_1026 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1026, 0, x_963);
x_1027 = 0;
lean_inc(x_18);
x_1028 = l_Lean_Meta_forallMetaTelescopeReducing(x_956, x_1026, x_1027, x_18, x_962);
lean_dec(x_1026);
if (lean_obj_tag(x_1028) == 0)
{
lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1061; 
x_1029 = lean_ctor_get(x_1028, 0);
lean_inc(x_1029);
x_1030 = lean_ctor_get(x_1029, 1);
lean_inc(x_1030);
x_1031 = lean_ctor_get(x_1028, 1);
lean_inc(x_1031);
lean_dec(x_1028);
x_1032 = lean_ctor_get(x_1029, 0);
lean_inc(x_1032);
lean_dec(x_1029);
x_1033 = lean_ctor_get(x_1030, 0);
lean_inc(x_1033);
x_1034 = lean_ctor_get(x_1030, 1);
lean_inc(x_1034);
lean_dec(x_1030);
lean_inc(x_18);
lean_inc(x_953);
lean_inc(x_1034);
x_1061 = l_Lean_Meta_isExprDefEq(x_1034, x_953, x_18, x_1031);
if (lean_obj_tag(x_1061) == 0)
{
lean_object* x_1062; uint8_t x_1063; 
x_1062 = lean_ctor_get(x_1061, 0);
lean_inc(x_1062);
x_1063 = lean_unbox(x_1062);
lean_dec(x_1062);
if (x_1063 == 0)
{
lean_object* x_1064; lean_object* x_1065; uint8_t x_1066; 
lean_dec(x_1033);
lean_dec(x_1032);
lean_dec(x_2);
x_1064 = lean_ctor_get(x_1061, 1);
lean_inc(x_1064);
lean_dec(x_1061);
x_1065 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_1034, x_953, x_18, x_1064);
lean_dec(x_18);
x_1066 = !lean_is_exclusive(x_1065);
if (x_1066 == 0)
{
return x_1065;
}
else
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; 
x_1067 = lean_ctor_get(x_1065, 0);
x_1068 = lean_ctor_get(x_1065, 1);
lean_inc(x_1068);
lean_inc(x_1067);
lean_dec(x_1065);
x_1069 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1069, 0, x_1067);
lean_ctor_set(x_1069, 1, x_1068);
return x_1069;
}
}
else
{
lean_object* x_1070; 
lean_dec(x_1034);
lean_dec(x_953);
x_1070 = lean_ctor_get(x_1061, 1);
lean_inc(x_1070);
lean_dec(x_1061);
x_1035 = x_1070;
goto block_1060;
}
}
else
{
uint8_t x_1071; 
lean_dec(x_1034);
lean_dec(x_1033);
lean_dec(x_1032);
lean_dec(x_953);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_1071 = !lean_is_exclusive(x_1061);
if (x_1071 == 0)
{
return x_1061;
}
else
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; 
x_1072 = lean_ctor_get(x_1061, 0);
x_1073 = lean_ctor_get(x_1061, 1);
lean_inc(x_1073);
lean_inc(x_1072);
lean_dec(x_1061);
x_1074 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1074, 0, x_1072);
lean_ctor_set(x_1074, 1, x_1073);
return x_1074;
}
}
block_1060:
{
lean_object* x_1036; 
lean_inc(x_18);
lean_inc(x_1);
x_1036 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_1032, x_1033, x_18, x_1035);
if (lean_obj_tag(x_1036) == 0)
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; 
x_1037 = lean_ctor_get(x_1036, 1);
lean_inc(x_1037);
lean_dec(x_1036);
x_1038 = lean_unsigned_to_nat(0u);
x_1039 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_1032, x_1032, x_1038, x_2);
lean_inc(x_1);
x_1040 = l_Lean_Meta_assignExprMVar(x_1, x_1039, x_18, x_1037);
if (lean_obj_tag(x_1040) == 0)
{
lean_object* x_1041; lean_object* x_1042; 
x_1041 = lean_ctor_get(x_1040, 1);
lean_inc(x_1041);
lean_dec(x_1040);
x_1042 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_1032, x_1033, x_18, x_1041);
lean_dec(x_1033);
if (lean_obj_tag(x_1042) == 0)
{
lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
x_1043 = lean_ctor_get(x_1042, 1);
lean_inc(x_1043);
lean_dec(x_1042);
x_1044 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_1032, x_1038, x_1038, x_18, x_1043);
x_1045 = lean_ctor_get(x_1044, 0);
lean_inc(x_1045);
x_1046 = lean_ctor_get(x_1044, 1);
lean_inc(x_1046);
lean_dec(x_1044);
x_1047 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_1045, x_18, x_1046);
lean_dec(x_1045);
return x_1047;
}
else
{
uint8_t x_1048; 
lean_dec(x_1032);
lean_dec(x_18);
x_1048 = !lean_is_exclusive(x_1042);
if (x_1048 == 0)
{
return x_1042;
}
else
{
lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
x_1049 = lean_ctor_get(x_1042, 0);
x_1050 = lean_ctor_get(x_1042, 1);
lean_inc(x_1050);
lean_inc(x_1049);
lean_dec(x_1042);
x_1051 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1051, 0, x_1049);
lean_ctor_set(x_1051, 1, x_1050);
return x_1051;
}
}
}
else
{
uint8_t x_1052; 
lean_dec(x_1033);
lean_dec(x_1032);
lean_dec(x_18);
lean_dec(x_1);
x_1052 = !lean_is_exclusive(x_1040);
if (x_1052 == 0)
{
return x_1040;
}
else
{
lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
x_1053 = lean_ctor_get(x_1040, 0);
x_1054 = lean_ctor_get(x_1040, 1);
lean_inc(x_1054);
lean_inc(x_1053);
lean_dec(x_1040);
x_1055 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1055, 0, x_1053);
lean_ctor_set(x_1055, 1, x_1054);
return x_1055;
}
}
}
else
{
uint8_t x_1056; 
lean_dec(x_1033);
lean_dec(x_1032);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_1056 = !lean_is_exclusive(x_1036);
if (x_1056 == 0)
{
return x_1036;
}
else
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; 
x_1057 = lean_ctor_get(x_1036, 0);
x_1058 = lean_ctor_get(x_1036, 1);
lean_inc(x_1058);
lean_inc(x_1057);
lean_dec(x_1036);
x_1059 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1059, 0, x_1057);
lean_ctor_set(x_1059, 1, x_1058);
return x_1059;
}
}
}
}
else
{
uint8_t x_1075; 
lean_dec(x_953);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_1075 = !lean_is_exclusive(x_1028);
if (x_1075 == 0)
{
return x_1028;
}
else
{
lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; 
x_1076 = lean_ctor_get(x_1028, 0);
x_1077 = lean_ctor_get(x_1028, 1);
lean_inc(x_1077);
lean_inc(x_1076);
lean_dec(x_1028);
x_1078 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1078, 0, x_1076);
lean_ctor_set(x_1078, 1, x_1077);
return x_1078;
}
}
}
}
else
{
lean_object* x_1079; lean_object* x_1080; uint8_t x_1081; 
x_1079 = lean_ctor_get(x_958, 1);
lean_inc(x_1079);
lean_dec(x_958);
x_1080 = lean_ctor_get(x_959, 0);
lean_inc(x_1080);
lean_dec(x_959);
x_1081 = l_String_posOfAux___main___closed__1;
if (x_1081 == 0)
{
lean_object* x_1082; 
lean_inc(x_18);
lean_inc(x_953);
x_1082 = l___private_Init_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(x_953, x_18, x_1079);
if (lean_obj_tag(x_1082) == 0)
{
lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; uint8_t x_1087; lean_object* x_1088; 
x_1083 = lean_ctor_get(x_1082, 0);
lean_inc(x_1083);
x_1084 = lean_ctor_get(x_1082, 1);
lean_inc(x_1084);
lean_dec(x_1082);
x_1085 = lean_nat_sub(x_1080, x_1083);
lean_dec(x_1083);
lean_dec(x_1080);
x_1086 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1086, 0, x_1085);
x_1087 = 0;
lean_inc(x_18);
x_1088 = l_Lean_Meta_forallMetaTelescopeReducing(x_956, x_1086, x_1087, x_18, x_1084);
lean_dec(x_1086);
if (lean_obj_tag(x_1088) == 0)
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1121; 
x_1089 = lean_ctor_get(x_1088, 0);
lean_inc(x_1089);
x_1090 = lean_ctor_get(x_1089, 1);
lean_inc(x_1090);
x_1091 = lean_ctor_get(x_1088, 1);
lean_inc(x_1091);
lean_dec(x_1088);
x_1092 = lean_ctor_get(x_1089, 0);
lean_inc(x_1092);
lean_dec(x_1089);
x_1093 = lean_ctor_get(x_1090, 0);
lean_inc(x_1093);
x_1094 = lean_ctor_get(x_1090, 1);
lean_inc(x_1094);
lean_dec(x_1090);
lean_inc(x_18);
lean_inc(x_953);
lean_inc(x_1094);
x_1121 = l_Lean_Meta_isExprDefEq(x_1094, x_953, x_18, x_1091);
if (lean_obj_tag(x_1121) == 0)
{
lean_object* x_1122; uint8_t x_1123; 
x_1122 = lean_ctor_get(x_1121, 0);
lean_inc(x_1122);
x_1123 = lean_unbox(x_1122);
lean_dec(x_1122);
if (x_1123 == 0)
{
lean_object* x_1124; lean_object* x_1125; uint8_t x_1126; 
lean_dec(x_1093);
lean_dec(x_1092);
lean_dec(x_2);
x_1124 = lean_ctor_get(x_1121, 1);
lean_inc(x_1124);
lean_dec(x_1121);
x_1125 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_1094, x_953, x_18, x_1124);
lean_dec(x_18);
x_1126 = !lean_is_exclusive(x_1125);
if (x_1126 == 0)
{
return x_1125;
}
else
{
lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; 
x_1127 = lean_ctor_get(x_1125, 0);
x_1128 = lean_ctor_get(x_1125, 1);
lean_inc(x_1128);
lean_inc(x_1127);
lean_dec(x_1125);
x_1129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1129, 0, x_1127);
lean_ctor_set(x_1129, 1, x_1128);
return x_1129;
}
}
else
{
lean_object* x_1130; 
lean_dec(x_1094);
lean_dec(x_953);
x_1130 = lean_ctor_get(x_1121, 1);
lean_inc(x_1130);
lean_dec(x_1121);
x_1095 = x_1130;
goto block_1120;
}
}
else
{
uint8_t x_1131; 
lean_dec(x_1094);
lean_dec(x_1093);
lean_dec(x_1092);
lean_dec(x_953);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_1131 = !lean_is_exclusive(x_1121);
if (x_1131 == 0)
{
return x_1121;
}
else
{
lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; 
x_1132 = lean_ctor_get(x_1121, 0);
x_1133 = lean_ctor_get(x_1121, 1);
lean_inc(x_1133);
lean_inc(x_1132);
lean_dec(x_1121);
x_1134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1134, 0, x_1132);
lean_ctor_set(x_1134, 1, x_1133);
return x_1134;
}
}
block_1120:
{
lean_object* x_1096; 
lean_inc(x_18);
lean_inc(x_1);
x_1096 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_1092, x_1093, x_18, x_1095);
if (lean_obj_tag(x_1096) == 0)
{
lean_object* x_1097; lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; 
x_1097 = lean_ctor_get(x_1096, 1);
lean_inc(x_1097);
lean_dec(x_1096);
x_1098 = lean_unsigned_to_nat(0u);
x_1099 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_1092, x_1092, x_1098, x_2);
lean_inc(x_1);
x_1100 = l_Lean_Meta_assignExprMVar(x_1, x_1099, x_18, x_1097);
if (lean_obj_tag(x_1100) == 0)
{
lean_object* x_1101; lean_object* x_1102; 
x_1101 = lean_ctor_get(x_1100, 1);
lean_inc(x_1101);
lean_dec(x_1100);
x_1102 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_1092, x_1093, x_18, x_1101);
lean_dec(x_1093);
if (lean_obj_tag(x_1102) == 0)
{
lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; 
x_1103 = lean_ctor_get(x_1102, 1);
lean_inc(x_1103);
lean_dec(x_1102);
x_1104 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_1092, x_1098, x_1098, x_18, x_1103);
x_1105 = lean_ctor_get(x_1104, 0);
lean_inc(x_1105);
x_1106 = lean_ctor_get(x_1104, 1);
lean_inc(x_1106);
lean_dec(x_1104);
x_1107 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_1105, x_18, x_1106);
lean_dec(x_1105);
return x_1107;
}
else
{
uint8_t x_1108; 
lean_dec(x_1092);
lean_dec(x_18);
x_1108 = !lean_is_exclusive(x_1102);
if (x_1108 == 0)
{
return x_1102;
}
else
{
lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; 
x_1109 = lean_ctor_get(x_1102, 0);
x_1110 = lean_ctor_get(x_1102, 1);
lean_inc(x_1110);
lean_inc(x_1109);
lean_dec(x_1102);
x_1111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1111, 0, x_1109);
lean_ctor_set(x_1111, 1, x_1110);
return x_1111;
}
}
}
else
{
uint8_t x_1112; 
lean_dec(x_1093);
lean_dec(x_1092);
lean_dec(x_18);
lean_dec(x_1);
x_1112 = !lean_is_exclusive(x_1100);
if (x_1112 == 0)
{
return x_1100;
}
else
{
lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; 
x_1113 = lean_ctor_get(x_1100, 0);
x_1114 = lean_ctor_get(x_1100, 1);
lean_inc(x_1114);
lean_inc(x_1113);
lean_dec(x_1100);
x_1115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1115, 0, x_1113);
lean_ctor_set(x_1115, 1, x_1114);
return x_1115;
}
}
}
else
{
uint8_t x_1116; 
lean_dec(x_1093);
lean_dec(x_1092);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_1116 = !lean_is_exclusive(x_1096);
if (x_1116 == 0)
{
return x_1096;
}
else
{
lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; 
x_1117 = lean_ctor_get(x_1096, 0);
x_1118 = lean_ctor_get(x_1096, 1);
lean_inc(x_1118);
lean_inc(x_1117);
lean_dec(x_1096);
x_1119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1119, 0, x_1117);
lean_ctor_set(x_1119, 1, x_1118);
return x_1119;
}
}
}
}
else
{
uint8_t x_1135; 
lean_dec(x_953);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_1135 = !lean_is_exclusive(x_1088);
if (x_1135 == 0)
{
return x_1088;
}
else
{
lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; 
x_1136 = lean_ctor_get(x_1088, 0);
x_1137 = lean_ctor_get(x_1088, 1);
lean_inc(x_1137);
lean_inc(x_1136);
lean_dec(x_1088);
x_1138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1138, 0, x_1136);
lean_ctor_set(x_1138, 1, x_1137);
return x_1138;
}
}
}
else
{
uint8_t x_1139; 
lean_dec(x_1080);
lean_dec(x_956);
lean_dec(x_953);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_1139 = !lean_is_exclusive(x_1082);
if (x_1139 == 0)
{
return x_1082;
}
else
{
lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; 
x_1140 = lean_ctor_get(x_1082, 0);
x_1141 = lean_ctor_get(x_1082, 1);
lean_inc(x_1141);
lean_inc(x_1140);
lean_dec(x_1082);
x_1142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1142, 0, x_1140);
lean_ctor_set(x_1142, 1, x_1141);
return x_1142;
}
}
}
else
{
lean_object* x_1143; uint8_t x_1144; lean_object* x_1145; 
x_1143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1143, 0, x_1080);
x_1144 = 0;
lean_inc(x_18);
x_1145 = l_Lean_Meta_forallMetaTelescopeReducing(x_956, x_1143, x_1144, x_18, x_1079);
lean_dec(x_1143);
if (lean_obj_tag(x_1145) == 0)
{
lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1178; 
x_1146 = lean_ctor_get(x_1145, 0);
lean_inc(x_1146);
x_1147 = lean_ctor_get(x_1146, 1);
lean_inc(x_1147);
x_1148 = lean_ctor_get(x_1145, 1);
lean_inc(x_1148);
lean_dec(x_1145);
x_1149 = lean_ctor_get(x_1146, 0);
lean_inc(x_1149);
lean_dec(x_1146);
x_1150 = lean_ctor_get(x_1147, 0);
lean_inc(x_1150);
x_1151 = lean_ctor_get(x_1147, 1);
lean_inc(x_1151);
lean_dec(x_1147);
lean_inc(x_18);
lean_inc(x_953);
lean_inc(x_1151);
x_1178 = l_Lean_Meta_isExprDefEq(x_1151, x_953, x_18, x_1148);
if (lean_obj_tag(x_1178) == 0)
{
lean_object* x_1179; uint8_t x_1180; 
x_1179 = lean_ctor_get(x_1178, 0);
lean_inc(x_1179);
x_1180 = lean_unbox(x_1179);
lean_dec(x_1179);
if (x_1180 == 0)
{
lean_object* x_1181; lean_object* x_1182; uint8_t x_1183; 
lean_dec(x_1150);
lean_dec(x_1149);
lean_dec(x_2);
x_1181 = lean_ctor_get(x_1178, 1);
lean_inc(x_1181);
lean_dec(x_1178);
x_1182 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_1151, x_953, x_18, x_1181);
lean_dec(x_18);
x_1183 = !lean_is_exclusive(x_1182);
if (x_1183 == 0)
{
return x_1182;
}
else
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
x_1184 = lean_ctor_get(x_1182, 0);
x_1185 = lean_ctor_get(x_1182, 1);
lean_inc(x_1185);
lean_inc(x_1184);
lean_dec(x_1182);
x_1186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1186, 0, x_1184);
lean_ctor_set(x_1186, 1, x_1185);
return x_1186;
}
}
else
{
lean_object* x_1187; 
lean_dec(x_1151);
lean_dec(x_953);
x_1187 = lean_ctor_get(x_1178, 1);
lean_inc(x_1187);
lean_dec(x_1178);
x_1152 = x_1187;
goto block_1177;
}
}
else
{
uint8_t x_1188; 
lean_dec(x_1151);
lean_dec(x_1150);
lean_dec(x_1149);
lean_dec(x_953);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_1188 = !lean_is_exclusive(x_1178);
if (x_1188 == 0)
{
return x_1178;
}
else
{
lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; 
x_1189 = lean_ctor_get(x_1178, 0);
x_1190 = lean_ctor_get(x_1178, 1);
lean_inc(x_1190);
lean_inc(x_1189);
lean_dec(x_1178);
x_1191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1191, 0, x_1189);
lean_ctor_set(x_1191, 1, x_1190);
return x_1191;
}
}
block_1177:
{
lean_object* x_1153; 
lean_inc(x_18);
lean_inc(x_1);
x_1153 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_1149, x_1150, x_18, x_1152);
if (lean_obj_tag(x_1153) == 0)
{
lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; 
x_1154 = lean_ctor_get(x_1153, 1);
lean_inc(x_1154);
lean_dec(x_1153);
x_1155 = lean_unsigned_to_nat(0u);
x_1156 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_1149, x_1149, x_1155, x_2);
lean_inc(x_1);
x_1157 = l_Lean_Meta_assignExprMVar(x_1, x_1156, x_18, x_1154);
if (lean_obj_tag(x_1157) == 0)
{
lean_object* x_1158; lean_object* x_1159; 
x_1158 = lean_ctor_get(x_1157, 1);
lean_inc(x_1158);
lean_dec(x_1157);
x_1159 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_1149, x_1150, x_18, x_1158);
lean_dec(x_1150);
if (lean_obj_tag(x_1159) == 0)
{
lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; 
x_1160 = lean_ctor_get(x_1159, 1);
lean_inc(x_1160);
lean_dec(x_1159);
x_1161 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_1149, x_1155, x_1155, x_18, x_1160);
x_1162 = lean_ctor_get(x_1161, 0);
lean_inc(x_1162);
x_1163 = lean_ctor_get(x_1161, 1);
lean_inc(x_1163);
lean_dec(x_1161);
x_1164 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_1162, x_18, x_1163);
lean_dec(x_1162);
return x_1164;
}
else
{
uint8_t x_1165; 
lean_dec(x_1149);
lean_dec(x_18);
x_1165 = !lean_is_exclusive(x_1159);
if (x_1165 == 0)
{
return x_1159;
}
else
{
lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; 
x_1166 = lean_ctor_get(x_1159, 0);
x_1167 = lean_ctor_get(x_1159, 1);
lean_inc(x_1167);
lean_inc(x_1166);
lean_dec(x_1159);
x_1168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1168, 0, x_1166);
lean_ctor_set(x_1168, 1, x_1167);
return x_1168;
}
}
}
else
{
uint8_t x_1169; 
lean_dec(x_1150);
lean_dec(x_1149);
lean_dec(x_18);
lean_dec(x_1);
x_1169 = !lean_is_exclusive(x_1157);
if (x_1169 == 0)
{
return x_1157;
}
else
{
lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; 
x_1170 = lean_ctor_get(x_1157, 0);
x_1171 = lean_ctor_get(x_1157, 1);
lean_inc(x_1171);
lean_inc(x_1170);
lean_dec(x_1157);
x_1172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1172, 0, x_1170);
lean_ctor_set(x_1172, 1, x_1171);
return x_1172;
}
}
}
else
{
uint8_t x_1173; 
lean_dec(x_1150);
lean_dec(x_1149);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_1173 = !lean_is_exclusive(x_1153);
if (x_1173 == 0)
{
return x_1153;
}
else
{
lean_object* x_1174; lean_object* x_1175; lean_object* x_1176; 
x_1174 = lean_ctor_get(x_1153, 0);
x_1175 = lean_ctor_get(x_1153, 1);
lean_inc(x_1175);
lean_inc(x_1174);
lean_dec(x_1153);
x_1176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1176, 0, x_1174);
lean_ctor_set(x_1176, 1, x_1175);
return x_1176;
}
}
}
}
else
{
uint8_t x_1192; 
lean_dec(x_953);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_1192 = !lean_is_exclusive(x_1145);
if (x_1192 == 0)
{
return x_1145;
}
else
{
lean_object* x_1193; lean_object* x_1194; lean_object* x_1195; 
x_1193 = lean_ctor_get(x_1145, 0);
x_1194 = lean_ctor_get(x_1145, 1);
lean_inc(x_1194);
lean_inc(x_1193);
lean_dec(x_1145);
x_1195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1195, 0, x_1193);
lean_ctor_set(x_1195, 1, x_1194);
return x_1195;
}
}
}
}
}
else
{
uint8_t x_1196; 
lean_dec(x_956);
lean_dec(x_953);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_1196 = !lean_is_exclusive(x_958);
if (x_1196 == 0)
{
return x_958;
}
else
{
lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; 
x_1197 = lean_ctor_get(x_958, 0);
x_1198 = lean_ctor_get(x_958, 1);
lean_inc(x_1198);
lean_inc(x_1197);
lean_dec(x_958);
x_1199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1199, 0, x_1197);
lean_ctor_set(x_1199, 1, x_1198);
return x_1199;
}
}
}
else
{
uint8_t x_1200; 
lean_dec(x_953);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_1200 = !lean_is_exclusive(x_955);
if (x_1200 == 0)
{
return x_955;
}
else
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; 
x_1201 = lean_ctor_get(x_955, 0);
x_1202 = lean_ctor_get(x_955, 1);
lean_inc(x_1202);
lean_inc(x_1201);
lean_dec(x_955);
x_1203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1203, 0, x_1201);
lean_ctor_set(x_1203, 1, x_1202);
return x_1203;
}
}
}
else
{
uint8_t x_1204; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_1204 = !lean_is_exclusive(x_952);
if (x_1204 == 0)
{
return x_952;
}
else
{
lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; 
x_1205 = lean_ctor_get(x_952, 0);
x_1206 = lean_ctor_get(x_952, 1);
lean_inc(x_1206);
lean_inc(x_1205);
lean_dec(x_952);
x_1207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1207, 0, x_1205);
lean_ctor_set(x_1207, 1, x_1206);
return x_1207;
}
}
}
else
{
uint8_t x_1208; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_1208 = !lean_is_exclusive(x_950);
if (x_1208 == 0)
{
return x_950;
}
else
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; 
x_1209 = lean_ctor_get(x_950, 0);
x_1210 = lean_ctor_get(x_950, 1);
lean_inc(x_1210);
lean_inc(x_1209);
lean_dec(x_950);
x_1211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1211, 0, x_1209);
lean_ctor_set(x_1211, 1, x_1210);
return x_1211;
}
}
}
}
}
else
{
uint8_t x_1216; 
lean_dec(x_2);
lean_dec(x_1);
x_1216 = !lean_is_exclusive(x_5);
if (x_1216 == 0)
{
return x_5;
}
else
{
lean_object* x_1217; lean_object* x_1218; lean_object* x_1219; 
x_1217 = lean_ctor_get(x_5, 0);
x_1218 = lean_ctor_get(x_5, 1);
lean_inc(x_1218);
lean_inc(x_1217);
lean_dec(x_5);
x_1219 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1219, 0, x_1217);
lean_ctor_set(x_1219, 1, x_1218);
return x_1219;
}
}
}
}
lean_object* l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_apply___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at_Lean_Meta_apply___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_Meta_apply___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_apply(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Init_Lean_Util_FindMVar(lean_object*);
lean_object* initialize_Init_Lean_Meta_Message(lean_object*);
lean_object* initialize_Init_Lean_Meta_ExprDefEq(lean_object*);
lean_object* initialize_Init_Lean_Meta_SynthInstance(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_Tactic_Apply(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Util_FindMVar(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Message(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_ExprDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_SynthInstance(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___closed__1 = _init_l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux___closed__1);
l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__1 = _init_l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__1);
l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2 = _init_l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2);
l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__3 = _init_l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__3();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__3);
l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__4 = _init_l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__4();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__4);
l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__5 = _init_l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__5();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__5);
l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__6 = _init_l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__6();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__6);
l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__7 = _init_l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__7();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__7);
l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__8 = _init_l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__8();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__8);
l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__1 = _init_l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__1();
lean_mark_persistent(l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__1);
l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__2 = _init_l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__2();
lean_mark_persistent(l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__2);
l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__3 = _init_l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__3();
lean_mark_persistent(l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__3);
l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst___closed__1 = _init_l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
