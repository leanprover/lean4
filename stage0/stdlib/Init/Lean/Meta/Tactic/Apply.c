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
lean_object* l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__1;
lean_object* l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__5;
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
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
if (x_18 == 0)
{
lean_dec(x_13);
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_Expr_Inhabited;
x_21 = lean_array_get(x_20, x_2, x_13);
lean_dec(x_13);
lean_inc(x_6);
lean_inc(x_21);
x_22 = l_Lean_Meta_inferType(x_21, x_6, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_6);
x_25 = l_Lean_Meta_synthInstance(x_23, x_6, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_6);
x_28 = l_Lean_Meta_isExprDefEq(x_21, x_26, x_6, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_dec(x_11);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2;
x_33 = l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances___spec__1___closed__3;
x_34 = l_Lean_Meta_throwTacticEx___rarg(x_32, x_1, x_33, x_6, x_31);
lean_dec(x_6);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_28, 1);
lean_inc(x_39);
lean_dec(x_28);
x_5 = x_11;
x_7 = x_39;
goto _start;
}
}
else
{
uint8_t x_41; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_28);
if (x_41 == 0)
{
return x_28;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_28, 0);
x_43 = lean_ctor_get(x_28, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_28);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_25);
if (x_45 == 0)
{
return x_25;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_25, 0);
x_47 = lean_ctor_get(x_25, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_25);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_22);
if (x_49 == 0)
{
return x_22;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_22, 0);
x_51 = lean_ctor_get(x_22, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_22);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_7);
return x_54;
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
uint8_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_19 = l_Lean_BinderInfo_inhabited;
x_20 = lean_box(x_19);
x_21 = lean_array_get(x_20, x_2, x_13);
lean_dec(x_13);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
x_23 = l_Lean_BinderInfo_isInstImplicit(x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_inc(x_16);
x_24 = l_Lean_Meta_getMVarTag(x_16, x_6, x_7);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Name_eraseMacroScopes(x_25);
lean_dec(x_25);
x_28 = l_Lean_Name_append___main(x_3, x_27);
x_29 = l_Lean_Meta_renameMVar(x_16, x_28, x_6, x_26);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_5 = x_11;
x_7 = x_30;
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_16);
lean_dec(x_11);
x_32 = !lean_is_exclusive(x_24);
if (x_32 == 0)
{
return x_24;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_24, 0);
x_34 = lean_ctor_get(x_24, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_24);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
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
lean_object* x_38; lean_object* x_39; 
lean_dec(x_5);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_7);
return x_39;
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
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_Name_isAnonymous(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_free_object(x_6);
x_11 = lean_array_get_size(x_2);
lean_inc(x_11);
x_12 = l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag___spec__1(x_2, x_3, x_8, x_11, x_11, x_4, x_9);
lean_dec(x_11);
lean_dec(x_8);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_8);
x_13 = lean_box(0);
lean_ctor_set(x_6, 0, x_13);
return x_6;
}
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = l_Lean_Name_isAnonymous(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_get_size(x_2);
lean_inc(x_17);
x_18 = l_Nat_forMAux___main___at___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag___spec__1(x_2, x_3, x_14, x_17, x_17, x_4, x_15);
lean_dec(x_17);
lean_dec(x_14);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_14);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
return x_6;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_6, 0);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_6);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
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
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Expr_mvarId_x21(x_1);
x_6 = lean_name_eq(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
return x_3;
}
else
{
lean_object* x_7; 
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_4);
return x_7;
}
}
else
{
return x_3;
}
}
case 5:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 1);
x_10 = l_Lean_Expr_hasMVar(x_8);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lean_Expr_hasMVar(x_9);
if (x_11 == 0)
{
return x_3;
}
else
{
x_2 = x_9;
goto _start;
}
}
else
{
lean_object* x_13; 
x_13 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_8, x_3);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = l_Lean_Expr_hasMVar(x_9);
if (x_14 == 0)
{
return x_13;
}
else
{
x_2 = x_9;
x_3 = x_13;
goto _start;
}
}
else
{
return x_13;
}
}
}
else
{
return x_3;
}
}
case 6:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_2, 1);
x_17 = lean_ctor_get(x_2, 2);
x_18 = l_Lean_Expr_hasMVar(x_16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lean_Expr_hasMVar(x_17);
if (x_19 == 0)
{
return x_3;
}
else
{
x_2 = x_17;
goto _start;
}
}
else
{
lean_object* x_21; 
x_21 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_16, x_3);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = l_Lean_Expr_hasMVar(x_17);
if (x_22 == 0)
{
return x_21;
}
else
{
x_2 = x_17;
x_3 = x_21;
goto _start;
}
}
else
{
return x_21;
}
}
}
else
{
return x_3;
}
}
case 7:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_2, 1);
x_25 = lean_ctor_get(x_2, 2);
x_26 = l_Lean_Expr_hasMVar(x_24);
if (x_26 == 0)
{
uint8_t x_27; 
x_27 = l_Lean_Expr_hasMVar(x_25);
if (x_27 == 0)
{
return x_3;
}
else
{
x_2 = x_25;
goto _start;
}
}
else
{
lean_object* x_29; 
x_29 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_24, x_3);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Expr_hasMVar(x_25);
if (x_30 == 0)
{
return x_29;
}
else
{
x_2 = x_25;
x_3 = x_29;
goto _start;
}
}
else
{
return x_29;
}
}
}
else
{
return x_3;
}
}
case 8:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_2, 1);
x_33 = lean_ctor_get(x_2, 2);
x_34 = lean_ctor_get(x_2, 3);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Expr_hasMVar(x_32);
if (x_43 == 0)
{
x_35 = x_3;
goto block_42;
}
else
{
lean_object* x_44; 
x_44 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_32, x_3);
if (lean_obj_tag(x_44) == 0)
{
x_35 = x_44;
goto block_42;
}
else
{
return x_44;
}
}
}
else
{
return x_3;
}
block_42:
{
uint8_t x_36; 
x_36 = l_Lean_Expr_hasMVar(x_33);
if (x_36 == 0)
{
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_37; 
x_37 = l_Lean_Expr_hasMVar(x_34);
if (x_37 == 0)
{
return x_35;
}
else
{
x_2 = x_34;
x_3 = x_35;
goto _start;
}
}
else
{
return x_35;
}
}
else
{
lean_object* x_39; 
x_39 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_33, x_35);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = l_Lean_Expr_hasMVar(x_34);
if (x_40 == 0)
{
return x_39;
}
else
{
x_2 = x_34;
x_3 = x_39;
goto _start;
}
}
else
{
return x_39;
}
}
}
}
case 10:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_ctor_get(x_2, 1);
x_46 = l_Lean_Expr_hasMVar(x_45);
if (x_46 == 0)
{
return x_3;
}
else
{
x_2 = x_45;
goto _start;
}
}
else
{
return x_3;
}
}
case 11:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_2, 2);
x_49 = l_Lean_Expr_hasMVar(x_48);
if (x_49 == 0)
{
return x_3;
}
else
{
x_2 = x_48;
goto _start;
}
}
else
{
return x_3;
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
lean_object* x_12; uint8_t x_13; 
x_12 = lean_array_fget(x_3, x_5);
x_13 = lean_expr_eqv(x_1, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc(x_6);
x_14 = l_Lean_Meta_inferType(x_12, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_box(0);
x_19 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_16, x_18);
lean_dec(x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_14);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_5, x_20);
lean_dec(x_5);
x_5 = x_21;
x_7 = x_17;
goto _start;
}
else
{
uint8_t x_23; lean_object* x_24; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
x_23 = 1;
x_24 = lean_box(x_23);
lean_ctor_set(x_14, 0, x_24);
return x_14;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_box(0);
x_28 = l_Lean_FindMVar_main___main___at___private_Init_Lean_Meta_Tactic_Apply_6__dependsOnOthers___spec__1(x_1, x_25, x_27);
lean_dec(x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_5, x_29);
lean_dec(x_5);
x_5 = x_30;
x_7 = x_26;
goto _start;
}
else
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
x_32 = 1;
x_33 = lean_box(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_26);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_6);
lean_dec(x_5);
x_35 = !lean_is_exclusive(x_14);
if (x_35 == 0)
{
return x_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_14, 0);
x_37 = lean_ctor_get(x_14, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_14);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_12);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_5, x_39);
lean_dec(x_5);
x_5 = x_40;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
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
lean_object* x_519; 
lean_dec(x_14);
lean_dec(x_6);
x_519 = lean_box(0);
x_19 = x_519;
goto block_518;
}
else
{
lean_object* x_520; uint8_t x_521; 
x_520 = lean_unsigned_to_nat(0u);
x_521 = l_Array_isEqvAux___main___at_Lean_Meta_apply___spec__2(x_3, x_6, lean_box(0), x_10, x_14, x_520);
lean_dec(x_14);
lean_dec(x_6);
if (x_521 == 0)
{
lean_object* x_522; 
x_522 = lean_box(0);
x_19 = x_522;
goto block_518;
}
else
{
lean_object* x_523; lean_object* x_524; 
lean_dec(x_8);
x_523 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2;
lean_inc(x_1);
x_524 = l_Lean_Meta_checkNotAssigned(x_1, x_523, x_18, x_7);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; lean_object* x_526; 
x_525 = lean_ctor_get(x_524, 1);
lean_inc(x_525);
lean_dec(x_524);
lean_inc(x_1);
x_526 = l_Lean_Meta_getMVarType(x_1, x_18, x_525);
if (lean_obj_tag(x_526) == 0)
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_527 = lean_ctor_get(x_526, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_526, 1);
lean_inc(x_528);
lean_dec(x_526);
lean_inc(x_18);
lean_inc(x_2);
x_529 = l_Lean_Meta_inferType(x_2, x_18, x_528);
if (lean_obj_tag(x_529) == 0)
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
lean_dec(x_529);
lean_inc(x_18);
lean_inc(x_530);
x_532 = l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux(x_530, x_18, x_531);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; lean_object* x_534; uint8_t x_535; 
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_533, 1);
lean_inc(x_534);
x_535 = lean_unbox(x_534);
lean_dec(x_534);
if (x_535 == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; uint8_t x_539; lean_object* x_540; 
x_536 = lean_ctor_get(x_532, 1);
lean_inc(x_536);
lean_dec(x_532);
x_537 = lean_ctor_get(x_533, 0);
lean_inc(x_537);
lean_dec(x_533);
x_538 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_538, 0, x_537);
x_539 = 0;
lean_inc(x_18);
x_540 = l_Lean_Meta_forallMetaTelescopeReducing(x_530, x_538, x_539, x_18, x_536);
lean_dec(x_538);
if (lean_obj_tag(x_540) == 0)
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_572; 
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_541, 1);
lean_inc(x_542);
x_543 = lean_ctor_get(x_540, 1);
lean_inc(x_543);
lean_dec(x_540);
x_544 = lean_ctor_get(x_541, 0);
lean_inc(x_544);
lean_dec(x_541);
x_545 = lean_ctor_get(x_542, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_542, 1);
lean_inc(x_546);
lean_dec(x_542);
lean_inc(x_18);
lean_inc(x_527);
lean_inc(x_546);
x_572 = l_Lean_Meta_isExprDefEq(x_546, x_527, x_18, x_543);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; uint8_t x_574; 
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
x_574 = lean_unbox(x_573);
lean_dec(x_573);
if (x_574 == 0)
{
lean_object* x_575; lean_object* x_576; uint8_t x_577; 
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_2);
x_575 = lean_ctor_get(x_572, 1);
lean_inc(x_575);
lean_dec(x_572);
x_576 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_546, x_527, x_18, x_575);
lean_dec(x_18);
x_577 = !lean_is_exclusive(x_576);
if (x_577 == 0)
{
return x_576;
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; 
x_578 = lean_ctor_get(x_576, 0);
x_579 = lean_ctor_get(x_576, 1);
lean_inc(x_579);
lean_inc(x_578);
lean_dec(x_576);
x_580 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_580, 0, x_578);
lean_ctor_set(x_580, 1, x_579);
return x_580;
}
}
else
{
lean_object* x_581; 
lean_dec(x_546);
lean_dec(x_527);
x_581 = lean_ctor_get(x_572, 1);
lean_inc(x_581);
lean_dec(x_572);
x_547 = x_581;
goto block_571;
}
}
else
{
uint8_t x_582; 
lean_dec(x_546);
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_527);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_582 = !lean_is_exclusive(x_572);
if (x_582 == 0)
{
return x_572;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; 
x_583 = lean_ctor_get(x_572, 0);
x_584 = lean_ctor_get(x_572, 1);
lean_inc(x_584);
lean_inc(x_583);
lean_dec(x_572);
x_585 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_585, 0, x_583);
lean_ctor_set(x_585, 1, x_584);
return x_585;
}
}
block_571:
{
lean_object* x_548; 
lean_inc(x_18);
lean_inc(x_1);
x_548 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_544, x_545, x_18, x_547);
if (lean_obj_tag(x_548) == 0)
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_549 = lean_ctor_get(x_548, 1);
lean_inc(x_549);
lean_dec(x_548);
x_550 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_544, x_544, x_520, x_2);
lean_inc(x_1);
x_551 = l_Lean_Meta_assignExprMVar(x_1, x_550, x_18, x_549);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; lean_object* x_553; 
x_552 = lean_ctor_get(x_551, 1);
lean_inc(x_552);
lean_dec(x_551);
x_553 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_544, x_545, x_18, x_552);
lean_dec(x_545);
if (lean_obj_tag(x_553) == 0)
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_554 = lean_ctor_get(x_553, 1);
lean_inc(x_554);
lean_dec(x_553);
x_555 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_544, x_520, x_520, x_18, x_554);
x_556 = lean_ctor_get(x_555, 0);
lean_inc(x_556);
x_557 = lean_ctor_get(x_555, 1);
lean_inc(x_557);
lean_dec(x_555);
x_558 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_556, x_18, x_557);
lean_dec(x_556);
return x_558;
}
else
{
uint8_t x_559; 
lean_dec(x_544);
lean_dec(x_18);
x_559 = !lean_is_exclusive(x_553);
if (x_559 == 0)
{
return x_553;
}
else
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; 
x_560 = lean_ctor_get(x_553, 0);
x_561 = lean_ctor_get(x_553, 1);
lean_inc(x_561);
lean_inc(x_560);
lean_dec(x_553);
x_562 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_562, 0, x_560);
lean_ctor_set(x_562, 1, x_561);
return x_562;
}
}
}
else
{
uint8_t x_563; 
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_18);
lean_dec(x_1);
x_563 = !lean_is_exclusive(x_551);
if (x_563 == 0)
{
return x_551;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; 
x_564 = lean_ctor_get(x_551, 0);
x_565 = lean_ctor_get(x_551, 1);
lean_inc(x_565);
lean_inc(x_564);
lean_dec(x_551);
x_566 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_566, 0, x_564);
lean_ctor_set(x_566, 1, x_565);
return x_566;
}
}
}
else
{
uint8_t x_567; 
lean_dec(x_545);
lean_dec(x_544);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_567 = !lean_is_exclusive(x_548);
if (x_567 == 0)
{
return x_548;
}
else
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_568 = lean_ctor_get(x_548, 0);
x_569 = lean_ctor_get(x_548, 1);
lean_inc(x_569);
lean_inc(x_568);
lean_dec(x_548);
x_570 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_570, 0, x_568);
lean_ctor_set(x_570, 1, x_569);
return x_570;
}
}
}
}
else
{
uint8_t x_586; 
lean_dec(x_527);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_586 = !lean_is_exclusive(x_540);
if (x_586 == 0)
{
return x_540;
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; 
x_587 = lean_ctor_get(x_540, 0);
x_588 = lean_ctor_get(x_540, 1);
lean_inc(x_588);
lean_inc(x_587);
lean_dec(x_540);
x_589 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_589, 0, x_587);
lean_ctor_set(x_589, 1, x_588);
return x_589;
}
}
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_590 = lean_ctor_get(x_532, 1);
lean_inc(x_590);
lean_dec(x_532);
x_591 = lean_ctor_get(x_533, 0);
lean_inc(x_591);
lean_dec(x_533);
lean_inc(x_18);
lean_inc(x_527);
x_592 = l___private_Init_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(x_527, x_18, x_590);
if (lean_obj_tag(x_592) == 0)
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; uint8_t x_597; lean_object* x_598; 
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_592, 1);
lean_inc(x_594);
lean_dec(x_592);
x_595 = lean_nat_sub(x_591, x_593);
lean_dec(x_593);
lean_dec(x_591);
x_596 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_596, 0, x_595);
x_597 = 0;
lean_inc(x_18);
x_598 = l_Lean_Meta_forallMetaTelescopeReducing(x_530, x_596, x_597, x_18, x_594);
lean_dec(x_596);
if (lean_obj_tag(x_598) == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_630; 
x_599 = lean_ctor_get(x_598, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_599, 1);
lean_inc(x_600);
x_601 = lean_ctor_get(x_598, 1);
lean_inc(x_601);
lean_dec(x_598);
x_602 = lean_ctor_get(x_599, 0);
lean_inc(x_602);
lean_dec(x_599);
x_603 = lean_ctor_get(x_600, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_600, 1);
lean_inc(x_604);
lean_dec(x_600);
lean_inc(x_18);
lean_inc(x_527);
lean_inc(x_604);
x_630 = l_Lean_Meta_isExprDefEq(x_604, x_527, x_18, x_601);
if (lean_obj_tag(x_630) == 0)
{
lean_object* x_631; uint8_t x_632; 
x_631 = lean_ctor_get(x_630, 0);
lean_inc(x_631);
x_632 = lean_unbox(x_631);
lean_dec(x_631);
if (x_632 == 0)
{
lean_object* x_633; lean_object* x_634; uint8_t x_635; 
lean_dec(x_603);
lean_dec(x_602);
lean_dec(x_2);
x_633 = lean_ctor_get(x_630, 1);
lean_inc(x_633);
lean_dec(x_630);
x_634 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_604, x_527, x_18, x_633);
lean_dec(x_18);
x_635 = !lean_is_exclusive(x_634);
if (x_635 == 0)
{
return x_634;
}
else
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_636 = lean_ctor_get(x_634, 0);
x_637 = lean_ctor_get(x_634, 1);
lean_inc(x_637);
lean_inc(x_636);
lean_dec(x_634);
x_638 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_638, 0, x_636);
lean_ctor_set(x_638, 1, x_637);
return x_638;
}
}
else
{
lean_object* x_639; 
lean_dec(x_604);
lean_dec(x_527);
x_639 = lean_ctor_get(x_630, 1);
lean_inc(x_639);
lean_dec(x_630);
x_605 = x_639;
goto block_629;
}
}
else
{
uint8_t x_640; 
lean_dec(x_604);
lean_dec(x_603);
lean_dec(x_602);
lean_dec(x_527);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_640 = !lean_is_exclusive(x_630);
if (x_640 == 0)
{
return x_630;
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_641 = lean_ctor_get(x_630, 0);
x_642 = lean_ctor_get(x_630, 1);
lean_inc(x_642);
lean_inc(x_641);
lean_dec(x_630);
x_643 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_643, 0, x_641);
lean_ctor_set(x_643, 1, x_642);
return x_643;
}
}
block_629:
{
lean_object* x_606; 
lean_inc(x_18);
lean_inc(x_1);
x_606 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_602, x_603, x_18, x_605);
if (lean_obj_tag(x_606) == 0)
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_607 = lean_ctor_get(x_606, 1);
lean_inc(x_607);
lean_dec(x_606);
x_608 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_602, x_602, x_520, x_2);
lean_inc(x_1);
x_609 = l_Lean_Meta_assignExprMVar(x_1, x_608, x_18, x_607);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_610; lean_object* x_611; 
x_610 = lean_ctor_get(x_609, 1);
lean_inc(x_610);
lean_dec(x_609);
x_611 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_602, x_603, x_18, x_610);
lean_dec(x_603);
if (lean_obj_tag(x_611) == 0)
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_612 = lean_ctor_get(x_611, 1);
lean_inc(x_612);
lean_dec(x_611);
x_613 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_602, x_520, x_520, x_18, x_612);
x_614 = lean_ctor_get(x_613, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_613, 1);
lean_inc(x_615);
lean_dec(x_613);
x_616 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_614, x_18, x_615);
lean_dec(x_614);
return x_616;
}
else
{
uint8_t x_617; 
lean_dec(x_602);
lean_dec(x_18);
x_617 = !lean_is_exclusive(x_611);
if (x_617 == 0)
{
return x_611;
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_618 = lean_ctor_get(x_611, 0);
x_619 = lean_ctor_get(x_611, 1);
lean_inc(x_619);
lean_inc(x_618);
lean_dec(x_611);
x_620 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_620, 0, x_618);
lean_ctor_set(x_620, 1, x_619);
return x_620;
}
}
}
else
{
uint8_t x_621; 
lean_dec(x_603);
lean_dec(x_602);
lean_dec(x_18);
lean_dec(x_1);
x_621 = !lean_is_exclusive(x_609);
if (x_621 == 0)
{
return x_609;
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_622 = lean_ctor_get(x_609, 0);
x_623 = lean_ctor_get(x_609, 1);
lean_inc(x_623);
lean_inc(x_622);
lean_dec(x_609);
x_624 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_624, 0, x_622);
lean_ctor_set(x_624, 1, x_623);
return x_624;
}
}
}
else
{
uint8_t x_625; 
lean_dec(x_603);
lean_dec(x_602);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_625 = !lean_is_exclusive(x_606);
if (x_625 == 0)
{
return x_606;
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_626 = lean_ctor_get(x_606, 0);
x_627 = lean_ctor_get(x_606, 1);
lean_inc(x_627);
lean_inc(x_626);
lean_dec(x_606);
x_628 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_628, 0, x_626);
lean_ctor_set(x_628, 1, x_627);
return x_628;
}
}
}
}
else
{
uint8_t x_644; 
lean_dec(x_527);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_644 = !lean_is_exclusive(x_598);
if (x_644 == 0)
{
return x_598;
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_645 = lean_ctor_get(x_598, 0);
x_646 = lean_ctor_get(x_598, 1);
lean_inc(x_646);
lean_inc(x_645);
lean_dec(x_598);
x_647 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_647, 0, x_645);
lean_ctor_set(x_647, 1, x_646);
return x_647;
}
}
}
else
{
uint8_t x_648; 
lean_dec(x_591);
lean_dec(x_530);
lean_dec(x_527);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_648 = !lean_is_exclusive(x_592);
if (x_648 == 0)
{
return x_592;
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_649 = lean_ctor_get(x_592, 0);
x_650 = lean_ctor_get(x_592, 1);
lean_inc(x_650);
lean_inc(x_649);
lean_dec(x_592);
x_651 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_651, 0, x_649);
lean_ctor_set(x_651, 1, x_650);
return x_651;
}
}
}
}
else
{
uint8_t x_652; 
lean_dec(x_530);
lean_dec(x_527);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_652 = !lean_is_exclusive(x_532);
if (x_652 == 0)
{
return x_532;
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_653 = lean_ctor_get(x_532, 0);
x_654 = lean_ctor_get(x_532, 1);
lean_inc(x_654);
lean_inc(x_653);
lean_dec(x_532);
x_655 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_655, 0, x_653);
lean_ctor_set(x_655, 1, x_654);
return x_655;
}
}
}
else
{
uint8_t x_656; 
lean_dec(x_527);
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_656 = !lean_is_exclusive(x_529);
if (x_656 == 0)
{
return x_529;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_657 = lean_ctor_get(x_529, 0);
x_658 = lean_ctor_get(x_529, 1);
lean_inc(x_658);
lean_inc(x_657);
lean_dec(x_529);
x_659 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_659, 0, x_657);
lean_ctor_set(x_659, 1, x_658);
return x_659;
}
}
}
else
{
uint8_t x_660; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_660 = !lean_is_exclusive(x_526);
if (x_660 == 0)
{
return x_526;
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_661 = lean_ctor_get(x_526, 0);
x_662 = lean_ctor_get(x_526, 1);
lean_inc(x_662);
lean_inc(x_661);
lean_dec(x_526);
x_663 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_663, 0, x_661);
lean_ctor_set(x_663, 1, x_662);
return x_663;
}
}
}
else
{
uint8_t x_664; 
lean_dec(x_18);
lean_dec(x_2);
lean_dec(x_1);
x_664 = !lean_is_exclusive(x_524);
if (x_664 == 0)
{
return x_524;
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_665 = lean_ctor_get(x_524, 0);
x_666 = lean_ctor_get(x_524, 1);
lean_inc(x_666);
lean_inc(x_665);
lean_dec(x_524);
x_667 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_667, 0, x_665);
lean_ctor_set(x_667, 1, x_666);
return x_667;
}
}
}
}
block_518:
{
uint8_t x_20; 
lean_dec(x_19);
x_20 = !lean_is_exclusive(x_7);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_7, 2);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_48; lean_object* x_49; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_23 = lean_ctor_get(x_21, 2);
x_72 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_21, 2, x_72);
x_73 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2;
lean_inc(x_1);
x_74 = l_Lean_Meta_checkNotAssigned(x_1, x_73, x_18, x_7);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
lean_inc(x_1);
x_76 = l_Lean_Meta_getMVarType(x_1, x_18, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_18);
lean_inc(x_2);
x_79 = l_Lean_Meta_inferType(x_2, x_18, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_18);
lean_inc(x_80);
x_82 = l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux(x_80, x_18, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; 
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_ctor_get(x_83, 0);
lean_inc(x_87);
lean_dec(x_83);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = 0;
lean_inc(x_18);
x_90 = l_Lean_Meta_forallMetaTelescopeReducing(x_80, x_88, x_89, x_18, x_86);
lean_dec(x_88);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_121; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_ctor_get(x_91, 0);
lean_inc(x_94);
lean_dec(x_91);
x_95 = lean_ctor_get(x_92, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
lean_inc(x_18);
lean_inc(x_77);
lean_inc(x_96);
x_121 = l_Lean_Meta_isExprDefEq(x_96, x_77, x_18, x_93);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_unbox(x_122);
lean_dec(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_8);
lean_dec(x_2);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_96, x_77, x_18, x_124);
lean_dec(x_18);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_48 = x_126;
x_49 = x_127;
goto block_71;
}
else
{
lean_object* x_128; 
lean_dec(x_96);
lean_dec(x_77);
x_128 = lean_ctor_get(x_121, 1);
lean_inc(x_128);
lean_dec(x_121);
x_97 = x_128;
goto block_120;
}
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_77);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_129 = lean_ctor_get(x_121, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_121, 1);
lean_inc(x_130);
lean_dec(x_121);
x_48 = x_129;
x_49 = x_130;
goto block_71;
}
block_120:
{
lean_object* x_98; 
lean_inc(x_18);
lean_inc(x_1);
x_98 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_94, x_95, x_18, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_unsigned_to_nat(0u);
x_101 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_94, x_94, x_100, x_2);
lean_inc(x_1);
x_102 = l_Lean_Meta_assignExprMVar(x_1, x_101, x_18, x_99);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_94, x_95, x_18, x_103);
lean_dec(x_95);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_94, x_100, x_100, x_18, x_105);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_107, x_18, x_108);
lean_dec(x_107);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_24 = x_110;
x_25 = x_111;
goto block_47;
}
else
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_8);
x_112 = lean_ctor_get(x_109, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_109, 1);
lean_inc(x_113);
lean_dec(x_109);
x_48 = x_112;
x_49 = x_113;
goto block_71;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_94);
lean_dec(x_18);
lean_dec(x_8);
x_114 = lean_ctor_get(x_104, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_104, 1);
lean_inc(x_115);
lean_dec(x_104);
x_48 = x_114;
x_49 = x_115;
goto block_71;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_1);
x_116 = lean_ctor_get(x_102, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_102, 1);
lean_inc(x_117);
lean_dec(x_102);
x_48 = x_116;
x_49 = x_117;
goto block_71;
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_118 = lean_ctor_get(x_98, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_98, 1);
lean_inc(x_119);
lean_dec(x_98);
x_48 = x_118;
x_49 = x_119;
goto block_71;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; 
lean_dec(x_77);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_131 = lean_ctor_get(x_90, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_90, 1);
lean_inc(x_132);
lean_dec(x_90);
x_48 = x_131;
x_49 = x_132;
goto block_71;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_82, 1);
lean_inc(x_133);
lean_dec(x_82);
x_134 = lean_ctor_get(x_83, 0);
lean_inc(x_134);
lean_dec(x_83);
lean_inc(x_18);
lean_inc(x_77);
x_135 = l___private_Init_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(x_77, x_18, x_133);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_nat_sub(x_134, x_136);
lean_dec(x_136);
lean_dec(x_134);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = 0;
lean_inc(x_18);
x_141 = l_Lean_Meta_forallMetaTelescopeReducing(x_80, x_139, x_140, x_18, x_137);
lean_dec(x_139);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_172; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_142, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_dec(x_141);
x_145 = lean_ctor_get(x_142, 0);
lean_inc(x_145);
lean_dec(x_142);
x_146 = lean_ctor_get(x_143, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
lean_dec(x_143);
lean_inc(x_18);
lean_inc(x_77);
lean_inc(x_147);
x_172 = l_Lean_Meta_isExprDefEq(x_147, x_77, x_18, x_144);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; uint8_t x_174; 
x_173 = lean_ctor_get(x_172, 0);
lean_inc(x_173);
x_174 = lean_unbox(x_173);
lean_dec(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_8);
lean_dec(x_2);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_dec(x_172);
x_176 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_147, x_77, x_18, x_175);
lean_dec(x_18);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_48 = x_177;
x_49 = x_178;
goto block_71;
}
else
{
lean_object* x_179; 
lean_dec(x_147);
lean_dec(x_77);
x_179 = lean_ctor_get(x_172, 1);
lean_inc(x_179);
lean_dec(x_172);
x_148 = x_179;
goto block_171;
}
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_147);
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_77);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_180 = lean_ctor_get(x_172, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_172, 1);
lean_inc(x_181);
lean_dec(x_172);
x_48 = x_180;
x_49 = x_181;
goto block_71;
}
block_171:
{
lean_object* x_149; 
lean_inc(x_18);
lean_inc(x_1);
x_149 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_145, x_146, x_18, x_148);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
x_151 = lean_unsigned_to_nat(0u);
x_152 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_145, x_145, x_151, x_2);
lean_inc(x_1);
x_153 = l_Lean_Meta_assignExprMVar(x_1, x_152, x_18, x_150);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec(x_153);
x_155 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_145, x_146, x_18, x_154);
lean_dec(x_146);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_157 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_145, x_151, x_151, x_18, x_156);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_158, x_18, x_159);
lean_dec(x_158);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_24 = x_161;
x_25 = x_162;
goto block_47;
}
else
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_8);
x_163 = lean_ctor_get(x_160, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_160, 1);
lean_inc(x_164);
lean_dec(x_160);
x_48 = x_163;
x_49 = x_164;
goto block_71;
}
}
else
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_145);
lean_dec(x_18);
lean_dec(x_8);
x_165 = lean_ctor_get(x_155, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_155, 1);
lean_inc(x_166);
lean_dec(x_155);
x_48 = x_165;
x_49 = x_166;
goto block_71;
}
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_1);
x_167 = lean_ctor_get(x_153, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_153, 1);
lean_inc(x_168);
lean_dec(x_153);
x_48 = x_167;
x_49 = x_168;
goto block_71;
}
}
else
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_169 = lean_ctor_get(x_149, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_149, 1);
lean_inc(x_170);
lean_dec(x_149);
x_48 = x_169;
x_49 = x_170;
goto block_71;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_77);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_182 = lean_ctor_get(x_141, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_141, 1);
lean_inc(x_183);
lean_dec(x_141);
x_48 = x_182;
x_49 = x_183;
goto block_71;
}
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_134);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_184 = lean_ctor_get(x_135, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_135, 1);
lean_inc(x_185);
lean_dec(x_135);
x_48 = x_184;
x_49 = x_185;
goto block_71;
}
}
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_186 = lean_ctor_get(x_82, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_82, 1);
lean_inc(x_187);
lean_dec(x_82);
x_48 = x_186;
x_49 = x_187;
goto block_71;
}
}
else
{
lean_object* x_188; lean_object* x_189; 
lean_dec(x_77);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_188 = lean_ctor_get(x_79, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_79, 1);
lean_inc(x_189);
lean_dec(x_79);
x_48 = x_188;
x_49 = x_189;
goto block_71;
}
}
else
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_190 = lean_ctor_get(x_76, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_76, 1);
lean_inc(x_191);
lean_dec(x_76);
x_48 = x_190;
x_49 = x_191;
goto block_71;
}
}
else
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_192 = lean_ctor_get(x_74, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_74, 1);
lean_inc(x_193);
lean_dec(x_74);
x_48 = x_192;
x_49 = x_193;
goto block_71;
}
block_47:
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 2);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 2);
lean_dec(x_29);
lean_ctor_set(x_27, 2, x_23);
if (lean_is_scalar(x_8)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_8;
}
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_27, 0);
x_32 = lean_ctor_get(x_27, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_27);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_23);
lean_ctor_set(x_25, 2, x_33);
if (lean_is_scalar(x_8)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_8;
}
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_25);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_35 = lean_ctor_get(x_25, 2);
x_36 = lean_ctor_get(x_25, 0);
x_37 = lean_ctor_get(x_25, 1);
x_38 = lean_ctor_get(x_25, 3);
x_39 = lean_ctor_get(x_25, 4);
x_40 = lean_ctor_get(x_25, 5);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_35);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_25);
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 lean_ctor_release(x_35, 2);
 x_43 = x_35;
} else {
 lean_dec_ref(x_35);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 3, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_23);
x_45 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_37);
lean_ctor_set(x_45, 2, x_44);
lean_ctor_set(x_45, 3, x_38);
lean_ctor_set(x_45, 4, x_39);
lean_ctor_set(x_45, 5, x_40);
if (lean_is_scalar(x_8)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_8;
}
lean_ctor_set(x_46, 0, x_24);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
block_71:
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_49, 2);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 2);
lean_dec(x_53);
lean_ctor_set(x_51, 2, x_23);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_49);
return x_54;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_51, 0);
x_56 = lean_ctor_get(x_51, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_51);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_23);
lean_ctor_set(x_49, 2, x_57);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_49);
return x_58;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_59 = lean_ctor_get(x_49, 2);
x_60 = lean_ctor_get(x_49, 0);
x_61 = lean_ctor_get(x_49, 1);
x_62 = lean_ctor_get(x_49, 3);
x_63 = lean_ctor_get(x_49, 4);
x_64 = lean_ctor_get(x_49, 5);
lean_inc(x_64);
lean_inc(x_63);
lean_inc(x_62);
lean_inc(x_59);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_49);
x_65 = lean_ctor_get(x_59, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_59, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 lean_ctor_release(x_59, 2);
 x_67 = x_59;
} else {
 lean_dec_ref(x_59);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(0, 3, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
lean_ctor_set(x_68, 2, x_23);
x_69 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_69, 0, x_60);
lean_ctor_set(x_69, 1, x_61);
lean_ctor_set(x_69, 2, x_68);
lean_ctor_set(x_69, 3, x_62);
lean_ctor_set(x_69, 4, x_63);
lean_ctor_set(x_69, 5, x_64);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_48);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_213; lean_object* x_214; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_194 = lean_ctor_get(x_21, 0);
x_195 = lean_ctor_get(x_21, 1);
x_196 = lean_ctor_get(x_21, 2);
lean_inc(x_196);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_21);
x_229 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_230 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_230, 0, x_194);
lean_ctor_set(x_230, 1, x_195);
lean_ctor_set(x_230, 2, x_229);
lean_ctor_set(x_7, 2, x_230);
x_231 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2;
lean_inc(x_1);
x_232 = l_Lean_Meta_checkNotAssigned(x_1, x_231, x_18, x_7);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
lean_dec(x_232);
lean_inc(x_1);
x_234 = l_Lean_Meta_getMVarType(x_1, x_18, x_233);
if (lean_obj_tag(x_234) == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_234, 1);
lean_inc(x_236);
lean_dec(x_234);
lean_inc(x_18);
lean_inc(x_2);
x_237 = l_Lean_Meta_inferType(x_2, x_18, x_236);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
lean_inc(x_18);
lean_inc(x_238);
x_240 = l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux(x_238, x_18, x_239);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_241, 1);
lean_inc(x_242);
x_243 = lean_unbox(x_242);
lean_dec(x_242);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; lean_object* x_248; 
x_244 = lean_ctor_get(x_240, 1);
lean_inc(x_244);
lean_dec(x_240);
x_245 = lean_ctor_get(x_241, 0);
lean_inc(x_245);
lean_dec(x_241);
x_246 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_246, 0, x_245);
x_247 = 0;
lean_inc(x_18);
x_248 = l_Lean_Meta_forallMetaTelescopeReducing(x_238, x_246, x_247, x_18, x_244);
lean_dec(x_246);
if (lean_obj_tag(x_248) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_279; 
x_249 = lean_ctor_get(x_248, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
x_251 = lean_ctor_get(x_248, 1);
lean_inc(x_251);
lean_dec(x_248);
x_252 = lean_ctor_get(x_249, 0);
lean_inc(x_252);
lean_dec(x_249);
x_253 = lean_ctor_get(x_250, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_250, 1);
lean_inc(x_254);
lean_dec(x_250);
lean_inc(x_18);
lean_inc(x_235);
lean_inc(x_254);
x_279 = l_Lean_Meta_isExprDefEq(x_254, x_235, x_18, x_251);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; uint8_t x_281; 
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_unbox(x_280);
lean_dec(x_280);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_8);
lean_dec(x_2);
x_282 = lean_ctor_get(x_279, 1);
lean_inc(x_282);
lean_dec(x_279);
x_283 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_254, x_235, x_18, x_282);
lean_dec(x_18);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
x_213 = x_284;
x_214 = x_285;
goto block_228;
}
else
{
lean_object* x_286; 
lean_dec(x_254);
lean_dec(x_235);
x_286 = lean_ctor_get(x_279, 1);
lean_inc(x_286);
lean_dec(x_279);
x_255 = x_286;
goto block_278;
}
}
else
{
lean_object* x_287; lean_object* x_288; 
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_235);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_287 = lean_ctor_get(x_279, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_279, 1);
lean_inc(x_288);
lean_dec(x_279);
x_213 = x_287;
x_214 = x_288;
goto block_228;
}
block_278:
{
lean_object* x_256; 
lean_inc(x_18);
lean_inc(x_1);
x_256 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_252, x_253, x_18, x_255);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_257 = lean_ctor_get(x_256, 1);
lean_inc(x_257);
lean_dec(x_256);
x_258 = lean_unsigned_to_nat(0u);
x_259 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_252, x_252, x_258, x_2);
lean_inc(x_1);
x_260 = l_Lean_Meta_assignExprMVar(x_1, x_259, x_18, x_257);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
lean_dec(x_260);
x_262 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_252, x_253, x_18, x_261);
lean_dec(x_253);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_264 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_252, x_258, x_258, x_18, x_263);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_265, x_18, x_266);
lean_dec(x_265);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
lean_dec(x_267);
x_197 = x_268;
x_198 = x_269;
goto block_212;
}
else
{
lean_object* x_270; lean_object* x_271; 
lean_dec(x_8);
x_270 = lean_ctor_get(x_267, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_267, 1);
lean_inc(x_271);
lean_dec(x_267);
x_213 = x_270;
x_214 = x_271;
goto block_228;
}
}
else
{
lean_object* x_272; lean_object* x_273; 
lean_dec(x_252);
lean_dec(x_18);
lean_dec(x_8);
x_272 = lean_ctor_get(x_262, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_262, 1);
lean_inc(x_273);
lean_dec(x_262);
x_213 = x_272;
x_214 = x_273;
goto block_228;
}
}
else
{
lean_object* x_274; lean_object* x_275; 
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_1);
x_274 = lean_ctor_get(x_260, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_260, 1);
lean_inc(x_275);
lean_dec(x_260);
x_213 = x_274;
x_214 = x_275;
goto block_228;
}
}
else
{
lean_object* x_276; lean_object* x_277; 
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_276 = lean_ctor_get(x_256, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_256, 1);
lean_inc(x_277);
lean_dec(x_256);
x_213 = x_276;
x_214 = x_277;
goto block_228;
}
}
}
else
{
lean_object* x_289; lean_object* x_290; 
lean_dec(x_235);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_289 = lean_ctor_get(x_248, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_248, 1);
lean_inc(x_290);
lean_dec(x_248);
x_213 = x_289;
x_214 = x_290;
goto block_228;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_291 = lean_ctor_get(x_240, 1);
lean_inc(x_291);
lean_dec(x_240);
x_292 = lean_ctor_get(x_241, 0);
lean_inc(x_292);
lean_dec(x_241);
lean_inc(x_18);
lean_inc(x_235);
x_293 = l___private_Init_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(x_235, x_18, x_291);
if (lean_obj_tag(x_293) == 0)
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; lean_object* x_299; 
x_294 = lean_ctor_get(x_293, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_293, 1);
lean_inc(x_295);
lean_dec(x_293);
x_296 = lean_nat_sub(x_292, x_294);
lean_dec(x_294);
lean_dec(x_292);
x_297 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_297, 0, x_296);
x_298 = 0;
lean_inc(x_18);
x_299 = l_Lean_Meta_forallMetaTelescopeReducing(x_238, x_297, x_298, x_18, x_295);
lean_dec(x_297);
if (lean_obj_tag(x_299) == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_330; 
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_300, 1);
lean_inc(x_301);
x_302 = lean_ctor_get(x_299, 1);
lean_inc(x_302);
lean_dec(x_299);
x_303 = lean_ctor_get(x_300, 0);
lean_inc(x_303);
lean_dec(x_300);
x_304 = lean_ctor_get(x_301, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_301, 1);
lean_inc(x_305);
lean_dec(x_301);
lean_inc(x_18);
lean_inc(x_235);
lean_inc(x_305);
x_330 = l_Lean_Meta_isExprDefEq(x_305, x_235, x_18, x_302);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; uint8_t x_332; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_unbox(x_331);
lean_dec(x_331);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_8);
lean_dec(x_2);
x_333 = lean_ctor_get(x_330, 1);
lean_inc(x_333);
lean_dec(x_330);
x_334 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_305, x_235, x_18, x_333);
lean_dec(x_18);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec(x_334);
x_213 = x_335;
x_214 = x_336;
goto block_228;
}
else
{
lean_object* x_337; 
lean_dec(x_305);
lean_dec(x_235);
x_337 = lean_ctor_get(x_330, 1);
lean_inc(x_337);
lean_dec(x_330);
x_306 = x_337;
goto block_329;
}
}
else
{
lean_object* x_338; lean_object* x_339; 
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_235);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_338 = lean_ctor_get(x_330, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_330, 1);
lean_inc(x_339);
lean_dec(x_330);
x_213 = x_338;
x_214 = x_339;
goto block_228;
}
block_329:
{
lean_object* x_307; 
lean_inc(x_18);
lean_inc(x_1);
x_307 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_303, x_304, x_18, x_306);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_308 = lean_ctor_get(x_307, 1);
lean_inc(x_308);
lean_dec(x_307);
x_309 = lean_unsigned_to_nat(0u);
x_310 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_303, x_303, x_309, x_2);
lean_inc(x_1);
x_311 = l_Lean_Meta_assignExprMVar(x_1, x_310, x_18, x_308);
if (lean_obj_tag(x_311) == 0)
{
lean_object* x_312; lean_object* x_313; 
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
lean_dec(x_311);
x_313 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_303, x_304, x_18, x_312);
lean_dec(x_304);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
lean_dec(x_313);
x_315 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_303, x_309, x_309, x_18, x_314);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_316, x_18, x_317);
lean_dec(x_316);
if (lean_obj_tag(x_318) == 0)
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
x_197 = x_319;
x_198 = x_320;
goto block_212;
}
else
{
lean_object* x_321; lean_object* x_322; 
lean_dec(x_8);
x_321 = lean_ctor_get(x_318, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_318, 1);
lean_inc(x_322);
lean_dec(x_318);
x_213 = x_321;
x_214 = x_322;
goto block_228;
}
}
else
{
lean_object* x_323; lean_object* x_324; 
lean_dec(x_303);
lean_dec(x_18);
lean_dec(x_8);
x_323 = lean_ctor_get(x_313, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_313, 1);
lean_inc(x_324);
lean_dec(x_313);
x_213 = x_323;
x_214 = x_324;
goto block_228;
}
}
else
{
lean_object* x_325; lean_object* x_326; 
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_1);
x_325 = lean_ctor_get(x_311, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_311, 1);
lean_inc(x_326);
lean_dec(x_311);
x_213 = x_325;
x_214 = x_326;
goto block_228;
}
}
else
{
lean_object* x_327; lean_object* x_328; 
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_327 = lean_ctor_get(x_307, 0);
lean_inc(x_327);
x_328 = lean_ctor_get(x_307, 1);
lean_inc(x_328);
lean_dec(x_307);
x_213 = x_327;
x_214 = x_328;
goto block_228;
}
}
}
else
{
lean_object* x_340; lean_object* x_341; 
lean_dec(x_235);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_340 = lean_ctor_get(x_299, 0);
lean_inc(x_340);
x_341 = lean_ctor_get(x_299, 1);
lean_inc(x_341);
lean_dec(x_299);
x_213 = x_340;
x_214 = x_341;
goto block_228;
}
}
else
{
lean_object* x_342; lean_object* x_343; 
lean_dec(x_292);
lean_dec(x_238);
lean_dec(x_235);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_342 = lean_ctor_get(x_293, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_293, 1);
lean_inc(x_343);
lean_dec(x_293);
x_213 = x_342;
x_214 = x_343;
goto block_228;
}
}
}
else
{
lean_object* x_344; lean_object* x_345; 
lean_dec(x_238);
lean_dec(x_235);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_344 = lean_ctor_get(x_240, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_240, 1);
lean_inc(x_345);
lean_dec(x_240);
x_213 = x_344;
x_214 = x_345;
goto block_228;
}
}
else
{
lean_object* x_346; lean_object* x_347; 
lean_dec(x_235);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_346 = lean_ctor_get(x_237, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_237, 1);
lean_inc(x_347);
lean_dec(x_237);
x_213 = x_346;
x_214 = x_347;
goto block_228;
}
}
else
{
lean_object* x_348; lean_object* x_349; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_348 = lean_ctor_get(x_234, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_234, 1);
lean_inc(x_349);
lean_dec(x_234);
x_213 = x_348;
x_214 = x_349;
goto block_228;
}
}
else
{
lean_object* x_350; lean_object* x_351; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_350 = lean_ctor_get(x_232, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_232, 1);
lean_inc(x_351);
lean_dec(x_232);
x_213 = x_350;
x_214 = x_351;
goto block_228;
}
block_212:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_199 = lean_ctor_get(x_198, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_198, 3);
lean_inc(x_202);
x_203 = lean_ctor_get(x_198, 4);
lean_inc(x_203);
x_204 = lean_ctor_get(x_198, 5);
lean_inc(x_204);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 lean_ctor_release(x_198, 4);
 lean_ctor_release(x_198, 5);
 x_205 = x_198;
} else {
 lean_dec_ref(x_198);
 x_205 = lean_box(0);
}
x_206 = lean_ctor_get(x_199, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_199, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 x_208 = x_199;
} else {
 lean_dec_ref(x_199);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(0, 3, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
lean_ctor_set(x_209, 2, x_196);
if (lean_is_scalar(x_205)) {
 x_210 = lean_alloc_ctor(0, 6, 0);
} else {
 x_210 = x_205;
}
lean_ctor_set(x_210, 0, x_200);
lean_ctor_set(x_210, 1, x_201);
lean_ctor_set(x_210, 2, x_209);
lean_ctor_set(x_210, 3, x_202);
lean_ctor_set(x_210, 4, x_203);
lean_ctor_set(x_210, 5, x_204);
if (lean_is_scalar(x_8)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_8;
}
lean_ctor_set(x_211, 0, x_197);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
block_228:
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_215 = lean_ctor_get(x_214, 2);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_214, 1);
lean_inc(x_217);
x_218 = lean_ctor_get(x_214, 3);
lean_inc(x_218);
x_219 = lean_ctor_get(x_214, 4);
lean_inc(x_219);
x_220 = lean_ctor_get(x_214, 5);
lean_inc(x_220);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 lean_ctor_release(x_214, 2);
 lean_ctor_release(x_214, 3);
 lean_ctor_release(x_214, 4);
 lean_ctor_release(x_214, 5);
 x_221 = x_214;
} else {
 lean_dec_ref(x_214);
 x_221 = lean_box(0);
}
x_222 = lean_ctor_get(x_215, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_215, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 lean_ctor_release(x_215, 2);
 x_224 = x_215;
} else {
 lean_dec_ref(x_215);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(0, 3, 0);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_223);
lean_ctor_set(x_225, 2, x_196);
if (lean_is_scalar(x_221)) {
 x_226 = lean_alloc_ctor(0, 6, 0);
} else {
 x_226 = x_221;
}
lean_ctor_set(x_226, 0, x_216);
lean_ctor_set(x_226, 1, x_217);
lean_ctor_set(x_226, 2, x_225);
lean_ctor_set(x_226, 3, x_218);
lean_ctor_set(x_226, 4, x_219);
lean_ctor_set(x_226, 5, x_220);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_213);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_378; lean_object* x_379; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_352 = lean_ctor_get(x_7, 2);
x_353 = lean_ctor_get(x_7, 0);
x_354 = lean_ctor_get(x_7, 1);
x_355 = lean_ctor_get(x_7, 3);
x_356 = lean_ctor_get(x_7, 4);
x_357 = lean_ctor_get(x_7, 5);
lean_inc(x_357);
lean_inc(x_356);
lean_inc(x_355);
lean_inc(x_352);
lean_inc(x_354);
lean_inc(x_353);
lean_dec(x_7);
x_358 = lean_ctor_get(x_352, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_352, 1);
lean_inc(x_359);
x_360 = lean_ctor_get(x_352, 2);
lean_inc(x_360);
if (lean_is_exclusive(x_352)) {
 lean_ctor_release(x_352, 0);
 lean_ctor_release(x_352, 1);
 lean_ctor_release(x_352, 2);
 x_361 = x_352;
} else {
 lean_dec_ref(x_352);
 x_361 = lean_box(0);
}
x_394 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_361)) {
 x_395 = lean_alloc_ctor(0, 3, 0);
} else {
 x_395 = x_361;
}
lean_ctor_set(x_395, 0, x_358);
lean_ctor_set(x_395, 1, x_359);
lean_ctor_set(x_395, 2, x_394);
x_396 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_396, 0, x_353);
lean_ctor_set(x_396, 1, x_354);
lean_ctor_set(x_396, 2, x_395);
lean_ctor_set(x_396, 3, x_355);
lean_ctor_set(x_396, 4, x_356);
lean_ctor_set(x_396, 5, x_357);
x_397 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg___closed__2;
lean_inc(x_1);
x_398 = l_Lean_Meta_checkNotAssigned(x_1, x_397, x_18, x_396);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_398, 1);
lean_inc(x_399);
lean_dec(x_398);
lean_inc(x_1);
x_400 = l_Lean_Meta_getMVarType(x_1, x_18, x_399);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_400, 1);
lean_inc(x_402);
lean_dec(x_400);
lean_inc(x_18);
lean_inc(x_2);
x_403 = l_Lean_Meta_inferType(x_2, x_18, x_402);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
lean_inc(x_18);
lean_inc(x_404);
x_406 = l___private_Init_Lean_Meta_Tactic_Apply_1__getExpectedNumArgsAux(x_404, x_18, x_405);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; uint8_t x_409; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_407, 1);
lean_inc(x_408);
x_409 = lean_unbox(x_408);
lean_dec(x_408);
if (x_409 == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; lean_object* x_414; 
x_410 = lean_ctor_get(x_406, 1);
lean_inc(x_410);
lean_dec(x_406);
x_411 = lean_ctor_get(x_407, 0);
lean_inc(x_411);
lean_dec(x_407);
x_412 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_412, 0, x_411);
x_413 = 0;
lean_inc(x_18);
x_414 = l_Lean_Meta_forallMetaTelescopeReducing(x_404, x_412, x_413, x_18, x_410);
lean_dec(x_412);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_445; 
x_415 = lean_ctor_get(x_414, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_415, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_414, 1);
lean_inc(x_417);
lean_dec(x_414);
x_418 = lean_ctor_get(x_415, 0);
lean_inc(x_418);
lean_dec(x_415);
x_419 = lean_ctor_get(x_416, 0);
lean_inc(x_419);
x_420 = lean_ctor_get(x_416, 1);
lean_inc(x_420);
lean_dec(x_416);
lean_inc(x_18);
lean_inc(x_401);
lean_inc(x_420);
x_445 = l_Lean_Meta_isExprDefEq(x_420, x_401, x_18, x_417);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; uint8_t x_447; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_unbox(x_446);
lean_dec(x_446);
if (x_447 == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_8);
lean_dec(x_2);
x_448 = lean_ctor_get(x_445, 1);
lean_inc(x_448);
lean_dec(x_445);
x_449 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_420, x_401, x_18, x_448);
lean_dec(x_18);
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_449, 1);
lean_inc(x_451);
lean_dec(x_449);
x_378 = x_450;
x_379 = x_451;
goto block_393;
}
else
{
lean_object* x_452; 
lean_dec(x_420);
lean_dec(x_401);
x_452 = lean_ctor_get(x_445, 1);
lean_inc(x_452);
lean_dec(x_445);
x_421 = x_452;
goto block_444;
}
}
else
{
lean_object* x_453; lean_object* x_454; 
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_401);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_453 = lean_ctor_get(x_445, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_445, 1);
lean_inc(x_454);
lean_dec(x_445);
x_378 = x_453;
x_379 = x_454;
goto block_393;
}
block_444:
{
lean_object* x_422; 
lean_inc(x_18);
lean_inc(x_1);
x_422 = l___private_Init_Lean_Meta_Tactic_Apply_4__synthInstances(x_1, x_418, x_419, x_18, x_421);
if (lean_obj_tag(x_422) == 0)
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_423 = lean_ctor_get(x_422, 1);
lean_inc(x_423);
lean_dec(x_422);
x_424 = lean_unsigned_to_nat(0u);
x_425 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_418, x_418, x_424, x_2);
lean_inc(x_1);
x_426 = l_Lean_Meta_assignExprMVar(x_1, x_425, x_18, x_423);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; lean_object* x_428; 
x_427 = lean_ctor_get(x_426, 1);
lean_inc(x_427);
lean_dec(x_426);
x_428 = l___private_Init_Lean_Meta_Tactic_Apply_5__appendParentTag(x_1, x_418, x_419, x_18, x_427);
lean_dec(x_419);
if (lean_obj_tag(x_428) == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_429 = lean_ctor_get(x_428, 1);
lean_inc(x_429);
lean_dec(x_428);
x_430 = l_Array_filterMAux___main___at_Lean_Meta_apply___spec__1(x_418, x_424, x_424, x_18, x_429);
x_431 = lean_ctor_get(x_430, 0);
lean_inc(x_431);
x_432 = lean_ctor_get(x_430, 1);
lean_inc(x_432);
lean_dec(x_430);
x_433 = l___private_Init_Lean_Meta_Tactic_Apply_7__reorderNonDependentFirst(x_431, x_18, x_432);
lean_dec(x_431);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; lean_object* x_435; 
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
lean_dec(x_433);
x_362 = x_434;
x_363 = x_435;
goto block_377;
}
else
{
lean_object* x_436; lean_object* x_437; 
lean_dec(x_8);
x_436 = lean_ctor_get(x_433, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_433, 1);
lean_inc(x_437);
lean_dec(x_433);
x_378 = x_436;
x_379 = x_437;
goto block_393;
}
}
else
{
lean_object* x_438; lean_object* x_439; 
lean_dec(x_418);
lean_dec(x_18);
lean_dec(x_8);
x_438 = lean_ctor_get(x_428, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_428, 1);
lean_inc(x_439);
lean_dec(x_428);
x_378 = x_438;
x_379 = x_439;
goto block_393;
}
}
else
{
lean_object* x_440; lean_object* x_441; 
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_1);
x_440 = lean_ctor_get(x_426, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_426, 1);
lean_inc(x_441);
lean_dec(x_426);
x_378 = x_440;
x_379 = x_441;
goto block_393;
}
}
else
{
lean_object* x_442; lean_object* x_443; 
lean_dec(x_419);
lean_dec(x_418);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_442 = lean_ctor_get(x_422, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_422, 1);
lean_inc(x_443);
lean_dec(x_422);
x_378 = x_442;
x_379 = x_443;
goto block_393;
}
}
}
else
{
lean_object* x_455; lean_object* x_456; 
lean_dec(x_401);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_455 = lean_ctor_get(x_414, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_414, 1);
lean_inc(x_456);
lean_dec(x_414);
x_378 = x_455;
x_379 = x_456;
goto block_393;
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_406, 1);
lean_inc(x_457);
lean_dec(x_406);
x_458 = lean_ctor_get(x_407, 0);
lean_inc(x_458);
lean_dec(x_407);
lean_inc(x_18);
lean_inc(x_401);
x_459 = l___private_Init_Lean_Meta_Tactic_Apply_2__getExpectedNumArgs(x_401, x_18, x_457);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; uint8_t x_464; lean_object* x_465; 
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
lean_dec(x_459);
x_462 = lean_nat_sub(x_458, x_460);
lean_dec(x_460);
lean_dec(x_458);
x_463 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_463, 0, x_462);
x_464 = 0;
lean_inc(x_18);
x_465 = l_Lean_Meta_forallMetaTelescopeReducing(x_404, x_463, x_464, x_18, x_461);
lean_dec(x_463);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_496; 
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
lean_inc(x_401);
lean_inc(x_471);
x_496 = l_Lean_Meta_isExprDefEq(x_471, x_401, x_18, x_468);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; uint8_t x_498; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
x_498 = lean_unbox(x_497);
lean_dec(x_497);
if (x_498 == 0)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_8);
lean_dec(x_2);
x_499 = lean_ctor_get(x_496, 1);
lean_inc(x_499);
lean_dec(x_496);
x_500 = l___private_Init_Lean_Meta_Tactic_Apply_3__throwApplyError___rarg(x_1, x_471, x_401, x_18, x_499);
lean_dec(x_18);
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
x_378 = x_501;
x_379 = x_502;
goto block_393;
}
else
{
lean_object* x_503; 
lean_dec(x_471);
lean_dec(x_401);
x_503 = lean_ctor_get(x_496, 1);
lean_inc(x_503);
lean_dec(x_496);
x_472 = x_503;
goto block_495;
}
}
else
{
lean_object* x_504; lean_object* x_505; 
lean_dec(x_471);
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_401);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_504 = lean_ctor_get(x_496, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_496, 1);
lean_inc(x_505);
lean_dec(x_496);
x_378 = x_504;
x_379 = x_505;
goto block_393;
}
block_495:
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
if (lean_obj_tag(x_484) == 0)
{
lean_object* x_485; lean_object* x_486; 
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_484, 1);
lean_inc(x_486);
lean_dec(x_484);
x_362 = x_485;
x_363 = x_486;
goto block_377;
}
else
{
lean_object* x_487; lean_object* x_488; 
lean_dec(x_8);
x_487 = lean_ctor_get(x_484, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_484, 1);
lean_inc(x_488);
lean_dec(x_484);
x_378 = x_487;
x_379 = x_488;
goto block_393;
}
}
else
{
lean_object* x_489; lean_object* x_490; 
lean_dec(x_469);
lean_dec(x_18);
lean_dec(x_8);
x_489 = lean_ctor_get(x_479, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_479, 1);
lean_inc(x_490);
lean_dec(x_479);
x_378 = x_489;
x_379 = x_490;
goto block_393;
}
}
else
{
lean_object* x_491; lean_object* x_492; 
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_1);
x_491 = lean_ctor_get(x_477, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_477, 1);
lean_inc(x_492);
lean_dec(x_477);
x_378 = x_491;
x_379 = x_492;
goto block_393;
}
}
else
{
lean_object* x_493; lean_object* x_494; 
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_493 = lean_ctor_get(x_473, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_473, 1);
lean_inc(x_494);
lean_dec(x_473);
x_378 = x_493;
x_379 = x_494;
goto block_393;
}
}
}
else
{
lean_object* x_506; lean_object* x_507; 
lean_dec(x_401);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_506 = lean_ctor_get(x_465, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_465, 1);
lean_inc(x_507);
lean_dec(x_465);
x_378 = x_506;
x_379 = x_507;
goto block_393;
}
}
else
{
lean_object* x_508; lean_object* x_509; 
lean_dec(x_458);
lean_dec(x_404);
lean_dec(x_401);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_508 = lean_ctor_get(x_459, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_459, 1);
lean_inc(x_509);
lean_dec(x_459);
x_378 = x_508;
x_379 = x_509;
goto block_393;
}
}
}
else
{
lean_object* x_510; lean_object* x_511; 
lean_dec(x_404);
lean_dec(x_401);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_510 = lean_ctor_get(x_406, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_406, 1);
lean_inc(x_511);
lean_dec(x_406);
x_378 = x_510;
x_379 = x_511;
goto block_393;
}
}
else
{
lean_object* x_512; lean_object* x_513; 
lean_dec(x_401);
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_512 = lean_ctor_get(x_403, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_403, 1);
lean_inc(x_513);
lean_dec(x_403);
x_378 = x_512;
x_379 = x_513;
goto block_393;
}
}
else
{
lean_object* x_514; lean_object* x_515; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_514 = lean_ctor_get(x_400, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_400, 1);
lean_inc(x_515);
lean_dec(x_400);
x_378 = x_514;
x_379 = x_515;
goto block_393;
}
}
else
{
lean_object* x_516; lean_object* x_517; 
lean_dec(x_18);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_516 = lean_ctor_get(x_398, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_398, 1);
lean_inc(x_517);
lean_dec(x_398);
x_378 = x_516;
x_379 = x_517;
goto block_393;
}
block_377:
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_364 = lean_ctor_get(x_363, 2);
lean_inc(x_364);
x_365 = lean_ctor_get(x_363, 0);
lean_inc(x_365);
x_366 = lean_ctor_get(x_363, 1);
lean_inc(x_366);
x_367 = lean_ctor_get(x_363, 3);
lean_inc(x_367);
x_368 = lean_ctor_get(x_363, 4);
lean_inc(x_368);
x_369 = lean_ctor_get(x_363, 5);
lean_inc(x_369);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 lean_ctor_release(x_363, 2);
 lean_ctor_release(x_363, 3);
 lean_ctor_release(x_363, 4);
 lean_ctor_release(x_363, 5);
 x_370 = x_363;
} else {
 lean_dec_ref(x_363);
 x_370 = lean_box(0);
}
x_371 = lean_ctor_get(x_364, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_364, 1);
lean_inc(x_372);
if (lean_is_exclusive(x_364)) {
 lean_ctor_release(x_364, 0);
 lean_ctor_release(x_364, 1);
 lean_ctor_release(x_364, 2);
 x_373 = x_364;
} else {
 lean_dec_ref(x_364);
 x_373 = lean_box(0);
}
if (lean_is_scalar(x_373)) {
 x_374 = lean_alloc_ctor(0, 3, 0);
} else {
 x_374 = x_373;
}
lean_ctor_set(x_374, 0, x_371);
lean_ctor_set(x_374, 1, x_372);
lean_ctor_set(x_374, 2, x_360);
if (lean_is_scalar(x_370)) {
 x_375 = lean_alloc_ctor(0, 6, 0);
} else {
 x_375 = x_370;
}
lean_ctor_set(x_375, 0, x_365);
lean_ctor_set(x_375, 1, x_366);
lean_ctor_set(x_375, 2, x_374);
lean_ctor_set(x_375, 3, x_367);
lean_ctor_set(x_375, 4, x_368);
lean_ctor_set(x_375, 5, x_369);
if (lean_is_scalar(x_8)) {
 x_376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_376 = x_8;
}
lean_ctor_set(x_376, 0, x_362);
lean_ctor_set(x_376, 1, x_375);
return x_376;
}
block_393:
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_380 = lean_ctor_get(x_379, 2);
lean_inc(x_380);
x_381 = lean_ctor_get(x_379, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_379, 1);
lean_inc(x_382);
x_383 = lean_ctor_get(x_379, 3);
lean_inc(x_383);
x_384 = lean_ctor_get(x_379, 4);
lean_inc(x_384);
x_385 = lean_ctor_get(x_379, 5);
lean_inc(x_385);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 lean_ctor_release(x_379, 2);
 lean_ctor_release(x_379, 3);
 lean_ctor_release(x_379, 4);
 lean_ctor_release(x_379, 5);
 x_386 = x_379;
} else {
 lean_dec_ref(x_379);
 x_386 = lean_box(0);
}
x_387 = lean_ctor_get(x_380, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_380, 1);
lean_inc(x_388);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 lean_ctor_release(x_380, 2);
 x_389 = x_380;
} else {
 lean_dec_ref(x_380);
 x_389 = lean_box(0);
}
if (lean_is_scalar(x_389)) {
 x_390 = lean_alloc_ctor(0, 3, 0);
} else {
 x_390 = x_389;
}
lean_ctor_set(x_390, 0, x_387);
lean_ctor_set(x_390, 1, x_388);
lean_ctor_set(x_390, 2, x_360);
if (lean_is_scalar(x_386)) {
 x_391 = lean_alloc_ctor(0, 6, 0);
} else {
 x_391 = x_386;
}
lean_ctor_set(x_391, 0, x_381);
lean_ctor_set(x_391, 1, x_382);
lean_ctor_set(x_391, 2, x_390);
lean_ctor_set(x_391, 3, x_383);
lean_ctor_set(x_391, 4, x_384);
lean_ctor_set(x_391, 5, x_385);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_378);
lean_ctor_set(x_392, 1, x_391);
return x_392;
}
}
}
}
else
{
uint8_t x_668; 
lean_dec(x_2);
lean_dec(x_1);
x_668 = !lean_is_exclusive(x_5);
if (x_668 == 0)
{
return x_5;
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; 
x_669 = lean_ctor_get(x_5, 0);
x_670 = lean_ctor_get(x_5, 1);
lean_inc(x_670);
lean_inc(x_669);
lean_dec(x_5);
x_671 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_671, 0, x_669);
lean_ctor_set(x_671, 1, x_670);
return x_671;
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
