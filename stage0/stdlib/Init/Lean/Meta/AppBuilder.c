// Lean compiler output
// Module: Init.Lean.Meta.AppBuilder
// Imports: Init.Default Init.Lean.Meta.SynthInstance
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
lean_object* l_Lean_Expr_eq_x3f___closed__1;
lean_object* l___private_Init_Lean_Util_Trace_2__addNode___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Expr_eq_x3f___boxed(lean_object*);
lean_object* l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqSymm___closed__2;
lean_object* l_Lean_Meta_mkCongr___closed__1;
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__3;
lean_object* l_Lean_Meta_mkHEqSymm___closed__1;
lean_object* l_Lean_Meta_mkEqSymm___closed__1;
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongr___closed__2;
extern lean_object* l___private_Init_Lean_Meta_Basic_10__regTraceClasses___closed__2;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_mkCongrArg___closed__2;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Exception_toTraceMessageData___closed__68;
lean_object* l_Lean_Meta_mkAppM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg___closed__1;
lean_object* l_Lean_Meta_mkEqSymm___closed__2;
lean_object* l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_AppBuilder_1__infer(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg___closed__3;
lean_object* l_Lean_Expr_heq_x3f___closed__2;
lean_object* l_Lean_Expr_heq_x3f(lean_object*);
lean_object* lean_instantiate_type_lparams(lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl___closed__1;
lean_object* l_Lean_Expr_eq_x3f(lean_object*);
lean_object* l_Lean_Meta_mkEqTrans___closed__1;
lean_object* l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans___closed__2;
uint8_t l_coeDecidableEq(uint8_t);
lean_object* l_Lean_Meta_mkCongrFun___closed__1;
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun___closed__2;
lean_object* l_Lean_Meta_mkEqSymm___closed__3;
extern uint8_t l_String_posOfAux___main___closed__2;
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_mkEqRefl___closed__1;
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_String_posOfAux___main___closed__1;
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Meta_mkEqRefl___closed__2;
lean_object* l_Lean_Expr_heq_x3f___closed__1;
lean_object* l_Lean_Expr_heq_x3f___boxed(lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_arrow_x3f(lean_object*);
lean_object* l_List_mapM___main___at_Lean_Meta_mkAppM___spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqSymm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM___closed__1;
lean_object* l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_incDepth(lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqTrans(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__1;
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_List_mapM___main___at_Lean_Meta_mkAppM___spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConstInfo(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_arrow_x3f___boxed(lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar___rarg(lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqTrans___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Util_Trace_3__getResetTraces___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__1___rarg(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun___closed__3;
lean_object* l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__2;
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* _init_l_Lean_Expr_eq_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Eq");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_eq_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_eq_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_eq_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_2 = l_Lean_Expr_eq_x3f___closed__2;
x_3 = lean_unsigned_to_nat(3u);
x_4 = l_Lean_Expr_isAppOfArity___main(x_1, x_2, x_3);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_7);
x_9 = lean_nat_sub(x_8, x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_9, x_10);
lean_dec(x_9);
x_12 = l_Lean_Expr_getRevArg_x21___main(x_1, x_11);
x_13 = lean_nat_sub(x_8, x_10);
x_14 = lean_nat_sub(x_13, x_10);
lean_dec(x_13);
x_15 = l_Lean_Expr_getRevArg_x21___main(x_1, x_14);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_sub(x_8, x_16);
lean_dec(x_8);
x_18 = lean_nat_sub(x_17, x_10);
lean_dec(x_17);
x_19 = l_Lean_Expr_getRevArg_x21___main(x_1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_12);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
lean_object* l_Lean_Expr_eq_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_eq_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Expr_heq_x3f___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HEq");
return x_1;
}
}
lean_object* _init_l_Lean_Expr_heq_x3f___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_heq_x3f___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Expr_heq_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_2 = l_Lean_Expr_heq_x3f___closed__2;
x_3 = lean_unsigned_to_nat(4u);
x_4 = l_Lean_Expr_isAppOfArity___main(x_1, x_2, x_3);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_7);
x_9 = lean_nat_sub(x_8, x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_9, x_10);
lean_dec(x_9);
x_12 = l_Lean_Expr_getRevArg_x21___main(x_1, x_11);
x_13 = lean_nat_sub(x_8, x_10);
x_14 = lean_nat_sub(x_13, x_10);
lean_dec(x_13);
x_15 = l_Lean_Expr_getRevArg_x21___main(x_1, x_14);
x_16 = lean_unsigned_to_nat(2u);
x_17 = lean_nat_sub(x_8, x_16);
x_18 = lean_nat_sub(x_17, x_10);
lean_dec(x_17);
x_19 = l_Lean_Expr_getRevArg_x21___main(x_1, x_18);
x_20 = lean_nat_sub(x_8, x_3);
lean_dec(x_8);
x_21 = lean_nat_sub(x_20, x_10);
lean_dec(x_20);
x_22 = l_Lean_Expr_getRevArg_x21___main(x_1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_12);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
}
}
lean_object* l_Lean_Expr_heq_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_heq_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Expr_arrow_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_Lean_Expr_hasLooseBVars(x_3);
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
lean_inc(x_2);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_3);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
}
else
{
lean_object* x_9; 
x_9 = lean_box(0);
return x_9;
}
}
}
lean_object* l_Lean_Expr_arrow_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_arrow_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_mkEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Meta_inferType(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_6);
x_8 = l_Lean_Meta_getLevel(x_6, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Expr_eq_x3f___closed__2;
x_14 = l_Lean_mkConst(x_13, x_12);
x_15 = l_Lean_mkApp3(x_14, x_6, x_1, x_2);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Expr_eq_x3f___closed__2;
x_21 = l_Lean_mkConst(x_20, x_19);
x_22 = l_Lean_mkApp3(x_21, x_6, x_1, x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
return x_8;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_5);
if (x_28 == 0)
{
return x_5;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
lean_object* l_Lean_Meta_mkHEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l_Lean_Meta_inferType(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_Meta_inferType(x_2, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
x_11 = l_Lean_Meta_getLevel(x_6, x_3, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Expr_heq_x3f___closed__2;
x_17 = l_Lean_mkConst(x_16, x_15);
x_18 = l_Lean_mkApp4(x_17, x_6, x_1, x_9, x_2);
lean_ctor_set(x_11, 0, x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_Expr_heq_x3f___closed__2;
x_24 = l_Lean_mkConst(x_23, x_22);
x_25 = l_Lean_mkApp4(x_24, x_6, x_1, x_9, x_2);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_20);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_11);
if (x_27 == 0)
{
return x_11;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_11, 0);
x_29 = lean_ctor_get(x_11, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_11);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_8);
if (x_31 == 0)
{
return x_8;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_8, 0);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_8);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_5);
if (x_35 == 0)
{
return x_5;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_5, 0);
x_37 = lean_ctor_get(x_5, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_5);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
lean_object* _init_l_Lean_Meta_mkEqRefl___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("refl");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkEqRefl___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l_Lean_Meta_mkEqRefl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkEqRefl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Meta_inferType(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_5);
x_7 = l_Lean_Meta_getLevel(x_5, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_mkEqRefl___closed__2;
x_13 = l_Lean_mkConst(x_12, x_11);
x_14 = l_Lean_mkAppB(x_13, x_5, x_1);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_mkEqRefl___closed__2;
x_20 = l_Lean_mkConst(x_19, x_18);
x_21 = l_Lean_mkAppB(x_20, x_5, x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_4);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* _init_l_Lean_Meta_mkHEqRefl___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_heq_x3f___closed__2;
x_2 = l_Lean_Meta_mkEqRefl___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkHEqRefl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_1);
x_4 = l_Lean_Meta_inferType(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
lean_inc(x_5);
x_7 = l_Lean_Meta_getLevel(x_5, x_2, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_mkHEqRefl___closed__1;
x_13 = l_Lean_mkConst(x_12, x_11);
x_14 = l_Lean_mkAppB(x_13, x_5, x_1);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 0);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_7);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Meta_mkHEqRefl___closed__1;
x_20 = l_Lean_mkConst(x_19, x_18);
x_21 = l_Lean_mkAppB(x_20, x_5, x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_5);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 0);
x_25 = lean_ctor_get(x_7, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_7);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_4);
if (x_27 == 0)
{
return x_4;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_4, 0);
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_4);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
lean_object* l___private_Init_Lean_Meta_AppBuilder_1__infer(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
x_4 = l_Lean_Meta_inferType(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lean_Meta_whnfD(x_5, x_2, x_6);
return x_7;
}
else
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = !lean_is_exclusive(x_4);
if (x_8 == 0)
{
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
}
lean_object* _init_l_Lean_Meta_mkEqSymm___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("symm");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkEqSymm___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l_Lean_Meta_mkEqSymm___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkEqSymm___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality proof expected");
return x_1;
}
}
lean_object* l_Lean_Meta_mkEqSymm(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_4 = l_Lean_Meta_mkEqRefl___closed__2;
x_5 = l_Lean_Expr_isAppOf(x_1, x_4);
x_6 = l_coeDecidableEq(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = l___private_Init_Lean_Meta_AppBuilder_1__infer(x_1, x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_Expr_eq_x3f___closed__2;
x_12 = lean_unsigned_to_nat(3u);
x_13 = l_Lean_Expr_isAppOfArity___main(x_9, x_11, x_12);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_19);
x_21 = l_Lean_mkOptionalNode___closed__2;
x_22 = lean_array_push(x_21, x_1);
x_23 = l_Lean_Meta_mkEqSymm___closed__2;
x_24 = l_Lean_Meta_mkEqSymm___closed__3;
x_25 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_25);
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_free_object(x_7);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_26);
x_28 = lean_nat_sub(x_27, x_26);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_28, x_29);
lean_dec(x_28);
x_31 = l_Lean_Expr_getRevArg_x21___main(x_9, x_30);
x_32 = lean_nat_sub(x_27, x_29);
x_33 = lean_nat_sub(x_32, x_29);
lean_dec(x_32);
x_34 = l_Lean_Expr_getRevArg_x21___main(x_9, x_33);
x_35 = lean_unsigned_to_nat(2u);
x_36 = lean_nat_sub(x_27, x_35);
lean_dec(x_27);
x_37 = lean_nat_sub(x_36, x_29);
lean_dec(x_36);
x_38 = l_Lean_Expr_getRevArg_x21___main(x_9, x_37);
lean_dec(x_9);
lean_inc(x_31);
x_39 = l_Lean_Meta_getLevel(x_31, x_2, x_10);
if (lean_obj_tag(x_39) == 0)
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Lean_Meta_mkEqSymm___closed__2;
x_45 = l_Lean_mkConst(x_44, x_43);
x_46 = l_Lean_mkApp4(x_45, x_31, x_34, x_38, x_1);
lean_ctor_set(x_39, 0, x_46);
return x_39;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_39, 0);
x_48 = lean_ctor_get(x_39, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_39);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Meta_mkEqSymm___closed__2;
x_52 = l_Lean_mkConst(x_51, x_50);
x_53 = l_Lean_mkApp4(x_52, x_31, x_34, x_38, x_1);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_48);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_39);
if (x_55 == 0)
{
return x_39;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_39, 0);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_39);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; 
x_59 = lean_ctor_get(x_7, 0);
x_60 = lean_ctor_get(x_7, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_7);
x_61 = l_Lean_Expr_eq_x3f___closed__2;
x_62 = lean_unsigned_to_nat(3u);
x_63 = l_Lean_Expr_isAppOfArity___main(x_59, x_61, x_62);
x_64 = l_coeDecidableEq(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_59);
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_2, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_2, 0);
lean_inc(x_68);
lean_dec(x_2);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_66);
lean_ctor_set(x_70, 2, x_67);
lean_ctor_set(x_70, 3, x_69);
x_71 = l_Lean_mkOptionalNode___closed__2;
x_72 = lean_array_push(x_71, x_1);
x_73 = l_Lean_Meta_mkEqSymm___closed__2;
x_74 = l_Lean_Meta_mkEqSymm___closed__3;
x_75 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
lean_ctor_set(x_75, 2, x_72);
lean_ctor_set(x_75, 3, x_70);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_60);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_77 = lean_unsigned_to_nat(0u);
x_78 = l_Lean_Expr_getAppNumArgsAux___main(x_59, x_77);
x_79 = lean_nat_sub(x_78, x_77);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_sub(x_79, x_80);
lean_dec(x_79);
x_82 = l_Lean_Expr_getRevArg_x21___main(x_59, x_81);
x_83 = lean_nat_sub(x_78, x_80);
x_84 = lean_nat_sub(x_83, x_80);
lean_dec(x_83);
x_85 = l_Lean_Expr_getRevArg_x21___main(x_59, x_84);
x_86 = lean_unsigned_to_nat(2u);
x_87 = lean_nat_sub(x_78, x_86);
lean_dec(x_78);
x_88 = lean_nat_sub(x_87, x_80);
lean_dec(x_87);
x_89 = l_Lean_Expr_getRevArg_x21___main(x_59, x_88);
lean_dec(x_59);
lean_inc(x_82);
x_90 = l_Lean_Meta_getLevel(x_82, x_2, x_60);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_91);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Meta_mkEqSymm___closed__2;
x_97 = l_Lean_mkConst(x_96, x_95);
x_98 = l_Lean_mkApp4(x_97, x_82, x_85, x_89, x_1);
if (lean_is_scalar(x_93)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_93;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_92);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_89);
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_1);
x_100 = lean_ctor_get(x_90, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_90, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_102 = x_90;
} else {
 lean_dec_ref(x_90);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
}
else
{
uint8_t x_104; 
lean_dec(x_2);
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_7);
if (x_104 == 0)
{
return x_7;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_7, 0);
x_106 = lean_ctor_get(x_7, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_7);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
lean_object* x_108; 
lean_dec(x_2);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_1);
lean_ctor_set(x_108, 1, x_3);
return x_108;
}
}
}
lean_object* _init_l_Lean_Meta_mkEqTrans___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("trans");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkEqTrans___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_eq_x3f___closed__2;
x_2 = l_Lean_Meta_mkEqTrans___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkEqTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_5 = l_Lean_Meta_mkEqRefl___closed__2;
x_6 = l_Lean_Expr_isAppOf(x_1, x_5);
x_7 = l_coeDecidableEq(x_6);
if (x_7 == 0)
{
uint8_t x_8; uint8_t x_9; 
x_8 = l_Lean_Expr_isAppOf(x_2, x_5);
x_9 = l_coeDecidableEq(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_3);
lean_inc(x_1);
x_10 = l___private_Init_Lean_Meta_AppBuilder_1__infer(x_1, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
lean_inc(x_3);
lean_inc(x_2);
x_14 = l___private_Init_Lean_Meta_AppBuilder_1__infer(x_2, x_3, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_61; lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_110 = l_Lean_Expr_eq_x3f___closed__2;
x_111 = lean_unsigned_to_nat(3u);
x_112 = l_Lean_Expr_isAppOfArity___main(x_11, x_110, x_111);
x_113 = l_coeDecidableEq(x_112);
x_114 = l_Lean_Expr_isAppOfArity___main(x_15, x_110, x_111);
x_115 = l_coeDecidableEq(x_114);
if (x_113 == 0)
{
lean_dec(x_11);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
x_116 = lean_ctor_get(x_16, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_16, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_3, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_3, 0);
lean_inc(x_119);
lean_dec(x_3);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec(x_119);
x_121 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_121, 0, x_116);
lean_ctor_set(x_121, 1, x_117);
lean_ctor_set(x_121, 2, x_118);
lean_ctor_set(x_121, 3, x_120);
x_122 = l_Lean_mkAppStx___closed__9;
x_123 = lean_array_push(x_122, x_1);
x_124 = lean_array_push(x_123, x_2);
x_125 = l_Lean_Meta_mkEqTrans___closed__2;
x_126 = l_Lean_Meta_mkEqSymm___closed__3;
x_127 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_127, 2, x_124);
lean_ctor_set(x_127, 3, x_121);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_16);
return x_128;
}
else
{
lean_object* x_129; 
x_129 = lean_box(0);
x_61 = x_129;
goto block_109;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_130 = lean_unsigned_to_nat(0u);
x_131 = l_Lean_Expr_getAppNumArgsAux___main(x_11, x_130);
x_132 = lean_nat_sub(x_131, x_130);
x_133 = lean_unsigned_to_nat(1u);
x_134 = lean_nat_sub(x_132, x_133);
lean_dec(x_132);
x_135 = l_Lean_Expr_getRevArg_x21___main(x_11, x_134);
x_136 = lean_nat_sub(x_131, x_133);
x_137 = lean_nat_sub(x_136, x_133);
lean_dec(x_136);
x_138 = l_Lean_Expr_getRevArg_x21___main(x_11, x_137);
x_139 = lean_unsigned_to_nat(2u);
x_140 = lean_nat_sub(x_131, x_139);
lean_dec(x_131);
x_141 = lean_nat_sub(x_140, x_133);
lean_dec(x_140);
x_142 = l_Lean_Expr_getRevArg_x21___main(x_11, x_141);
lean_dec(x_11);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_138);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_135);
lean_ctor_set(x_144, 1, x_143);
if (x_115 == 0)
{
lean_object* x_145; 
lean_dec(x_15);
lean_dec(x_13);
x_145 = lean_box(0);
x_18 = x_145;
x_19 = x_144;
goto block_60;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_144);
x_61 = x_146;
goto block_109;
}
}
block_60:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_20);
lean_dec(x_19);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_25);
x_27 = l_Lean_mkAppStx___closed__9;
x_28 = lean_array_push(x_27, x_1);
x_29 = lean_array_push(x_28, x_2);
x_30 = l_Lean_Meta_mkEqTrans___closed__2;
x_31 = l_Lean_Meta_mkEqSymm___closed__3;
x_32 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set(x_32, 2, x_29);
lean_ctor_set(x_32, 3, x_26);
if (lean_is_scalar(x_17)) {
 x_33 = lean_alloc_ctor(1, 2, 0);
} else {
 x_33 = x_17;
 lean_ctor_set_tag(x_33, 1);
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_16);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_17);
x_34 = lean_ctor_get(x_18, 0);
lean_inc(x_34);
lean_dec(x_18);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_19, 0);
lean_inc(x_36);
lean_dec(x_19);
x_37 = lean_ctor_get(x_20, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_dec(x_20);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
lean_inc(x_36);
x_40 = l_Lean_Meta_getLevel(x_36, x_3, x_16);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_Meta_mkEqTrans___closed__2;
x_46 = l_Lean_mkConst(x_45, x_44);
x_47 = l_Lean_mkApp6(x_46, x_36, x_37, x_38, x_39, x_1, x_2);
lean_ctor_set(x_40, 0, x_47);
return x_40;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_ctor_get(x_40, 0);
x_49 = lean_ctor_get(x_40, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_40);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Meta_mkEqTrans___closed__2;
x_53 = l_Lean_mkConst(x_52, x_51);
x_54 = l_Lean_mkApp6(x_53, x_36, x_37, x_38, x_39, x_1, x_2);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_49);
return x_55;
}
}
else
{
uint8_t x_56; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_40);
if (x_56 == 0)
{
return x_40;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_40, 0);
x_58 = lean_ctor_get(x_40, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_40);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
block_109:
{
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_17);
lean_dec(x_15);
x_62 = lean_ctor_get(x_16, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_16, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_3, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_3, 0);
lean_inc(x_65);
lean_dec(x_3);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
x_67 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_63);
lean_ctor_set(x_67, 2, x_64);
lean_ctor_set(x_67, 3, x_66);
x_68 = l_Lean_mkAppStx___closed__9;
x_69 = lean_array_push(x_68, x_1);
x_70 = lean_array_push(x_69, x_2);
x_71 = l_Lean_Meta_mkEqTrans___closed__2;
x_72 = l_Lean_Meta_mkEqSymm___closed__3;
x_73 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
lean_ctor_set(x_73, 2, x_70);
lean_ctor_set(x_73, 3, x_67);
if (lean_is_scalar(x_13)) {
 x_74 = lean_alloc_ctor(1, 2, 0);
} else {
 x_74 = x_13;
 lean_ctor_set_tag(x_74, 1);
}
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_16);
return x_74;
}
else
{
uint8_t x_75; 
lean_dec(x_13);
x_75 = !lean_is_exclusive(x_61);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_76 = lean_ctor_get(x_61, 0);
x_77 = lean_unsigned_to_nat(0u);
x_78 = l_Lean_Expr_getAppNumArgsAux___main(x_15, x_77);
x_79 = lean_nat_sub(x_78, x_77);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_sub(x_79, x_80);
lean_dec(x_79);
x_82 = l_Lean_Expr_getRevArg_x21___main(x_15, x_81);
x_83 = lean_nat_sub(x_78, x_80);
x_84 = lean_nat_sub(x_83, x_80);
lean_dec(x_83);
x_85 = l_Lean_Expr_getRevArg_x21___main(x_15, x_84);
x_86 = lean_unsigned_to_nat(2u);
x_87 = lean_nat_sub(x_78, x_86);
lean_dec(x_78);
x_88 = lean_nat_sub(x_87, x_80);
lean_dec(x_87);
x_89 = l_Lean_Expr_getRevArg_x21___main(x_15, x_88);
lean_dec(x_15);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_85);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_82);
lean_ctor_set(x_91, 1, x_90);
lean_ctor_set(x_61, 0, x_91);
x_18 = x_61;
x_19 = x_76;
goto block_60;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_92 = lean_ctor_get(x_61, 0);
lean_inc(x_92);
lean_dec(x_61);
x_93 = lean_unsigned_to_nat(0u);
x_94 = l_Lean_Expr_getAppNumArgsAux___main(x_15, x_93);
x_95 = lean_nat_sub(x_94, x_93);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_sub(x_95, x_96);
lean_dec(x_95);
x_98 = l_Lean_Expr_getRevArg_x21___main(x_15, x_97);
x_99 = lean_nat_sub(x_94, x_96);
x_100 = lean_nat_sub(x_99, x_96);
lean_dec(x_99);
x_101 = l_Lean_Expr_getRevArg_x21___main(x_15, x_100);
x_102 = lean_unsigned_to_nat(2u);
x_103 = lean_nat_sub(x_94, x_102);
lean_dec(x_94);
x_104 = lean_nat_sub(x_103, x_96);
lean_dec(x_103);
x_105 = l_Lean_Expr_getRevArg_x21___main(x_15, x_104);
lean_dec(x_15);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_101);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_98);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_18 = x_108;
x_19 = x_92;
goto block_60;
}
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_147 = !lean_is_exclusive(x_14);
if (x_147 == 0)
{
return x_14;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_14, 0);
x_149 = lean_ctor_get(x_14, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_14);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_151 = !lean_is_exclusive(x_10);
if (x_151 == 0)
{
return x_10;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_10, 0);
x_153 = lean_ctor_get(x_10, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_10);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
else
{
lean_object* x_155; 
lean_dec(x_3);
lean_dec(x_2);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_1);
lean_ctor_set(x_155, 1, x_4);
return x_155;
}
}
else
{
lean_object* x_156; 
lean_dec(x_3);
lean_dec(x_1);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_2);
lean_ctor_set(x_156, 1, x_4);
return x_156;
}
}
}
lean_object* _init_l_Lean_Meta_mkHEqSymm___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_heq_x3f___closed__2;
x_2 = l_Lean_Meta_mkEqSymm___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkHEqSymm___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("heterogeneous equality proof expected");
return x_1;
}
}
lean_object* l_Lean_Meta_mkHEqSymm(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_4 = l_Lean_Meta_mkHEqRefl___closed__1;
x_5 = l_Lean_Expr_isAppOf(x_1, x_4);
x_6 = l_coeDecidableEq(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = l___private_Init_Lean_Meta_AppBuilder_1__infer(x_1, x_2, x_3);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_Expr_heq_x3f___closed__2;
x_12 = lean_unsigned_to_nat(4u);
x_13 = l_Lean_Expr_isAppOfArity___main(x_9, x_11, x_12);
x_14 = l_coeDecidableEq(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_19);
x_21 = l_Lean_mkOptionalNode___closed__2;
x_22 = lean_array_push(x_21, x_1);
x_23 = l_Lean_Meta_mkHEqSymm___closed__1;
x_24 = l_Lean_Meta_mkHEqSymm___closed__2;
x_25 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_22);
lean_ctor_set(x_25, 3, x_20);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_25);
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_7);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_26);
x_28 = lean_nat_sub(x_27, x_26);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_sub(x_28, x_29);
lean_dec(x_28);
x_31 = l_Lean_Expr_getRevArg_x21___main(x_9, x_30);
x_32 = lean_nat_sub(x_27, x_29);
x_33 = lean_nat_sub(x_32, x_29);
lean_dec(x_32);
x_34 = l_Lean_Expr_getRevArg_x21___main(x_9, x_33);
x_35 = lean_unsigned_to_nat(2u);
x_36 = lean_nat_sub(x_27, x_35);
x_37 = lean_nat_sub(x_36, x_29);
lean_dec(x_36);
x_38 = l_Lean_Expr_getRevArg_x21___main(x_9, x_37);
x_39 = lean_nat_sub(x_27, x_12);
lean_dec(x_27);
x_40 = lean_nat_sub(x_39, x_29);
lean_dec(x_39);
x_41 = l_Lean_Expr_getRevArg_x21___main(x_9, x_40);
lean_dec(x_9);
lean_inc(x_31);
x_42 = l_Lean_Meta_getLevel(x_31, x_2, x_10);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Meta_mkHEqSymm___closed__1;
x_48 = l_Lean_mkConst(x_47, x_46);
x_49 = l_Lean_mkApp5(x_48, x_31, x_38, x_34, x_41, x_1);
lean_ctor_set(x_42, 0, x_49);
return x_42;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_42, 0);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_42);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_Meta_mkHEqSymm___closed__1;
x_55 = l_Lean_mkConst(x_54, x_53);
x_56 = l_Lean_mkApp5(x_55, x_31, x_38, x_34, x_41, x_1);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_51);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_42);
if (x_58 == 0)
{
return x_42;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_42, 0);
x_60 = lean_ctor_get(x_42, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_42);
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
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_67; 
x_62 = lean_ctor_get(x_7, 0);
x_63 = lean_ctor_get(x_7, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_7);
x_64 = l_Lean_Expr_heq_x3f___closed__2;
x_65 = lean_unsigned_to_nat(4u);
x_66 = l_Lean_Expr_isAppOfArity___main(x_62, x_64, x_65);
x_67 = l_coeDecidableEq(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_62);
x_68 = lean_ctor_get(x_63, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_2, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_2, 0);
lean_inc(x_71);
lean_dec(x_2);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_69);
lean_ctor_set(x_73, 2, x_70);
lean_ctor_set(x_73, 3, x_72);
x_74 = l_Lean_mkOptionalNode___closed__2;
x_75 = lean_array_push(x_74, x_1);
x_76 = l_Lean_Meta_mkHEqSymm___closed__1;
x_77 = l_Lean_Meta_mkHEqSymm___closed__2;
x_78 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_78, 2, x_75);
lean_ctor_set(x_78, 3, x_73);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_63);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_80 = lean_unsigned_to_nat(0u);
x_81 = l_Lean_Expr_getAppNumArgsAux___main(x_62, x_80);
x_82 = lean_nat_sub(x_81, x_80);
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_nat_sub(x_82, x_83);
lean_dec(x_82);
x_85 = l_Lean_Expr_getRevArg_x21___main(x_62, x_84);
x_86 = lean_nat_sub(x_81, x_83);
x_87 = lean_nat_sub(x_86, x_83);
lean_dec(x_86);
x_88 = l_Lean_Expr_getRevArg_x21___main(x_62, x_87);
x_89 = lean_unsigned_to_nat(2u);
x_90 = lean_nat_sub(x_81, x_89);
x_91 = lean_nat_sub(x_90, x_83);
lean_dec(x_90);
x_92 = l_Lean_Expr_getRevArg_x21___main(x_62, x_91);
x_93 = lean_nat_sub(x_81, x_65);
lean_dec(x_81);
x_94 = lean_nat_sub(x_93, x_83);
lean_dec(x_93);
x_95 = l_Lean_Expr_getRevArg_x21___main(x_62, x_94);
lean_dec(x_62);
lean_inc(x_85);
x_96 = l_Lean_Meta_getLevel(x_85, x_2, x_63);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_99 = x_96;
} else {
 lean_dec_ref(x_96);
 x_99 = lean_box(0);
}
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_Meta_mkHEqSymm___closed__1;
x_103 = l_Lean_mkConst(x_102, x_101);
x_104 = l_Lean_mkApp5(x_103, x_85, x_92, x_88, x_95, x_1);
if (lean_is_scalar(x_99)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_99;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_98);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_95);
lean_dec(x_92);
lean_dec(x_88);
lean_dec(x_85);
lean_dec(x_1);
x_106 = lean_ctor_get(x_96, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_96, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_108 = x_96;
} else {
 lean_dec_ref(x_96);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_7);
if (x_110 == 0)
{
return x_7;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_7, 0);
x_112 = lean_ctor_get(x_7, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_7);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; 
lean_dec(x_2);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_1);
lean_ctor_set(x_114, 1, x_3);
return x_114;
}
}
}
lean_object* _init_l_Lean_Meta_mkHEqTrans___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Expr_heq_x3f___closed__2;
x_2 = l_Lean_Meta_mkEqTrans___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkHEqTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_5 = l_Lean_Meta_mkHEqRefl___closed__1;
x_6 = l_Lean_Expr_isAppOf(x_1, x_5);
x_7 = l_coeDecidableEq(x_6);
if (x_7 == 0)
{
uint8_t x_8; uint8_t x_9; 
x_8 = l_Lean_Expr_isAppOf(x_2, x_5);
x_9 = l_coeDecidableEq(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_inc(x_3);
lean_inc(x_1);
x_10 = l___private_Init_Lean_Meta_AppBuilder_1__infer(x_1, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
lean_inc(x_3);
lean_inc(x_2);
x_14 = l___private_Init_Lean_Meta_AppBuilder_1__infer(x_2, x_3, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_65; lean_object* x_124; lean_object* x_125; uint8_t x_126; uint8_t x_127; uint8_t x_128; uint8_t x_129; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_124 = l_Lean_Expr_heq_x3f___closed__2;
x_125 = lean_unsigned_to_nat(4u);
x_126 = l_Lean_Expr_isAppOfArity___main(x_11, x_124, x_125);
x_127 = l_coeDecidableEq(x_126);
x_128 = l_Lean_Expr_isAppOfArity___main(x_15, x_124, x_125);
x_129 = l_coeDecidableEq(x_128);
if (x_127 == 0)
{
lean_dec(x_11);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
x_130 = lean_ctor_get(x_16, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_16, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_3, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_3, 0);
lean_inc(x_133);
lean_dec(x_3);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
lean_dec(x_133);
x_135 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_135, 0, x_130);
lean_ctor_set(x_135, 1, x_131);
lean_ctor_set(x_135, 2, x_132);
lean_ctor_set(x_135, 3, x_134);
x_136 = l_Lean_mkAppStx___closed__9;
x_137 = lean_array_push(x_136, x_1);
x_138 = lean_array_push(x_137, x_2);
x_139 = l_Lean_Meta_mkHEqTrans___closed__1;
x_140 = l_Lean_Meta_mkHEqSymm___closed__2;
x_141 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
lean_ctor_set(x_141, 2, x_138);
lean_ctor_set(x_141, 3, x_135);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_16);
return x_142;
}
else
{
lean_object* x_143; 
x_143 = lean_box(0);
x_65 = x_143;
goto block_123;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_144 = lean_unsigned_to_nat(0u);
x_145 = l_Lean_Expr_getAppNumArgsAux___main(x_11, x_144);
x_146 = lean_nat_sub(x_145, x_144);
x_147 = lean_unsigned_to_nat(1u);
x_148 = lean_nat_sub(x_146, x_147);
lean_dec(x_146);
x_149 = l_Lean_Expr_getRevArg_x21___main(x_11, x_148);
x_150 = lean_nat_sub(x_145, x_147);
x_151 = lean_nat_sub(x_150, x_147);
lean_dec(x_150);
x_152 = l_Lean_Expr_getRevArg_x21___main(x_11, x_151);
x_153 = lean_unsigned_to_nat(2u);
x_154 = lean_nat_sub(x_145, x_153);
x_155 = lean_nat_sub(x_154, x_147);
lean_dec(x_154);
x_156 = l_Lean_Expr_getRevArg_x21___main(x_11, x_155);
x_157 = lean_nat_sub(x_145, x_125);
lean_dec(x_145);
x_158 = lean_nat_sub(x_157, x_147);
lean_dec(x_157);
x_159 = l_Lean_Expr_getRevArg_x21___main(x_11, x_158);
lean_dec(x_11);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_156);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_152);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_162, 0, x_149);
lean_ctor_set(x_162, 1, x_161);
if (x_129 == 0)
{
lean_object* x_163; 
lean_dec(x_15);
lean_dec(x_13);
x_163 = lean_box(0);
x_18 = x_163;
x_19 = x_162;
goto block_64;
}
else
{
lean_object* x_164; 
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_162);
x_65 = x_164;
goto block_123;
}
}
block_64:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
lean_dec(x_3);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_26);
x_28 = l_Lean_mkAppStx___closed__9;
x_29 = lean_array_push(x_28, x_1);
x_30 = lean_array_push(x_29, x_2);
x_31 = l_Lean_Meta_mkHEqTrans___closed__1;
x_32 = l_Lean_Meta_mkHEqSymm___closed__2;
x_33 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_27);
if (lean_is_scalar(x_17)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_17;
 lean_ctor_set_tag(x_34, 1);
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_16);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_17);
x_35 = lean_ctor_get(x_18, 0);
lean_inc(x_35);
lean_dec(x_18);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_ctor_get(x_19, 0);
lean_inc(x_38);
lean_dec(x_19);
x_39 = lean_ctor_get(x_20, 0);
lean_inc(x_39);
lean_dec(x_20);
x_40 = lean_ctor_get(x_21, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_dec(x_21);
x_42 = lean_ctor_get(x_37, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_37, 1);
lean_inc(x_43);
lean_dec(x_37);
lean_inc(x_38);
x_44 = l_Lean_Meta_getLevel(x_38, x_3, x_16);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Meta_mkHEqTrans___closed__1;
x_50 = l_Lean_mkConst(x_49, x_48);
x_51 = l_Lean_mkApp8(x_50, x_38, x_40, x_42, x_39, x_41, x_43, x_1, x_2);
lean_ctor_set(x_44, 0, x_51);
return x_44;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_44, 0);
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_44);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_Meta_mkHEqTrans___closed__1;
x_57 = l_Lean_mkConst(x_56, x_55);
x_58 = l_Lean_mkApp8(x_57, x_38, x_40, x_42, x_39, x_41, x_43, x_1, x_2);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_53);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_44);
if (x_60 == 0)
{
return x_44;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_44, 0);
x_62 = lean_ctor_get(x_44, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_44);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
block_123:
{
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_17);
lean_dec(x_15);
x_66 = lean_ctor_get(x_16, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_16, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_3, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_3, 0);
lean_inc(x_69);
lean_dec(x_3);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_67);
lean_ctor_set(x_71, 2, x_68);
lean_ctor_set(x_71, 3, x_70);
x_72 = l_Lean_mkAppStx___closed__9;
x_73 = lean_array_push(x_72, x_1);
x_74 = lean_array_push(x_73, x_2);
x_75 = l_Lean_Meta_mkHEqTrans___closed__1;
x_76 = l_Lean_Meta_mkHEqSymm___closed__2;
x_77 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_74);
lean_ctor_set(x_77, 3, x_71);
if (lean_is_scalar(x_13)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_13;
 lean_ctor_set_tag(x_78, 1);
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_16);
return x_78;
}
else
{
uint8_t x_79; 
lean_dec(x_13);
x_79 = !lean_is_exclusive(x_65);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_80 = lean_ctor_get(x_65, 0);
x_81 = lean_unsigned_to_nat(0u);
x_82 = l_Lean_Expr_getAppNumArgsAux___main(x_15, x_81);
x_83 = lean_nat_sub(x_82, x_81);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_nat_sub(x_83, x_84);
lean_dec(x_83);
x_86 = l_Lean_Expr_getRevArg_x21___main(x_15, x_85);
x_87 = lean_nat_sub(x_82, x_84);
x_88 = lean_nat_sub(x_87, x_84);
lean_dec(x_87);
x_89 = l_Lean_Expr_getRevArg_x21___main(x_15, x_88);
x_90 = lean_unsigned_to_nat(2u);
x_91 = lean_nat_sub(x_82, x_90);
x_92 = lean_nat_sub(x_91, x_84);
lean_dec(x_91);
x_93 = l_Lean_Expr_getRevArg_x21___main(x_15, x_92);
x_94 = lean_unsigned_to_nat(4u);
x_95 = lean_nat_sub(x_82, x_94);
lean_dec(x_82);
x_96 = lean_nat_sub(x_95, x_84);
lean_dec(x_95);
x_97 = l_Lean_Expr_getRevArg_x21___main(x_15, x_96);
lean_dec(x_15);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_93);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_89);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_86);
lean_ctor_set(x_100, 1, x_99);
lean_ctor_set(x_65, 0, x_100);
x_18 = x_65;
x_19 = x_80;
goto block_64;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_101 = lean_ctor_get(x_65, 0);
lean_inc(x_101);
lean_dec(x_65);
x_102 = lean_unsigned_to_nat(0u);
x_103 = l_Lean_Expr_getAppNumArgsAux___main(x_15, x_102);
x_104 = lean_nat_sub(x_103, x_102);
x_105 = lean_unsigned_to_nat(1u);
x_106 = lean_nat_sub(x_104, x_105);
lean_dec(x_104);
x_107 = l_Lean_Expr_getRevArg_x21___main(x_15, x_106);
x_108 = lean_nat_sub(x_103, x_105);
x_109 = lean_nat_sub(x_108, x_105);
lean_dec(x_108);
x_110 = l_Lean_Expr_getRevArg_x21___main(x_15, x_109);
x_111 = lean_unsigned_to_nat(2u);
x_112 = lean_nat_sub(x_103, x_111);
x_113 = lean_nat_sub(x_112, x_105);
lean_dec(x_112);
x_114 = l_Lean_Expr_getRevArg_x21___main(x_15, x_113);
x_115 = lean_unsigned_to_nat(4u);
x_116 = lean_nat_sub(x_103, x_115);
lean_dec(x_103);
x_117 = lean_nat_sub(x_116, x_105);
lean_dec(x_116);
x_118 = l_Lean_Expr_getRevArg_x21___main(x_15, x_117);
lean_dec(x_15);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_114);
lean_ctor_set(x_119, 1, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_110);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_107);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_18 = x_122;
x_19 = x_101;
goto block_64;
}
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_165 = !lean_is_exclusive(x_14);
if (x_165 == 0)
{
return x_14;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_14, 0);
x_167 = lean_ctor_get(x_14, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_14);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_10);
if (x_169 == 0)
{
return x_10;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_10, 0);
x_171 = lean_ctor_get(x_10, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_10);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
lean_object* x_173; 
lean_dec(x_3);
lean_dec(x_2);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_1);
lean_ctor_set(x_173, 1, x_4);
return x_173;
}
}
else
{
lean_object* x_174; 
lean_dec(x_3);
lean_dec(x_1);
x_174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_174, 0, x_2);
lean_ctor_set(x_174, 1, x_4);
return x_174;
}
}
}
lean_object* _init_l_Lean_Meta_mkCongrArg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("congrArg");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkCongrArg___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkCongrArg___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkCongrArg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("non-dependent function expected");
return x_1;
}
}
lean_object* l_Lean_Meta_mkCongrArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = l___private_Init_Lean_Meta_AppBuilder_1__infer(x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
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
lean_inc(x_3);
lean_inc(x_1);
x_9 = l___private_Init_Lean_Meta_AppBuilder_1__infer(x_1, x_3, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_64; lean_object* x_81; lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_133; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_130 = l_Lean_Expr_eq_x3f___closed__2;
x_131 = lean_unsigned_to_nat(3u);
x_132 = l_Lean_Expr_isAppOfArity___main(x_6, x_130, x_131);
x_133 = l_coeDecidableEq(x_132);
if (lean_obj_tag(x_10) == 7)
{
lean_object* x_134; lean_object* x_135; uint8_t x_136; uint8_t x_137; 
x_134 = lean_ctor_get(x_10, 1);
lean_inc(x_134);
x_135 = lean_ctor_get(x_10, 2);
lean_inc(x_135);
lean_dec(x_10);
x_136 = l_Lean_Expr_hasLooseBVars(x_135);
x_137 = l_coeDecidableEq(x_136);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_134);
lean_ctor_set(x_138, 1, x_135);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
if (x_133 == 0)
{
lean_dec(x_6);
x_64 = x_139;
goto block_80;
}
else
{
lean_dec(x_8);
x_81 = x_139;
goto block_129;
}
}
else
{
lean_object* x_140; 
lean_dec(x_135);
lean_dec(x_134);
x_140 = lean_box(0);
if (x_133 == 0)
{
lean_dec(x_6);
x_64 = x_140;
goto block_80;
}
else
{
lean_dec(x_8);
x_81 = x_140;
goto block_129;
}
}
}
else
{
lean_object* x_141; 
lean_dec(x_10);
x_141 = lean_box(0);
if (x_133 == 0)
{
lean_dec(x_6);
x_64 = x_141;
goto block_80;
}
else
{
lean_dec(x_8);
x_81 = x_141;
goto block_129;
}
}
block_63:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_14);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_19);
x_21 = l_Lean_mkAppStx___closed__9;
x_22 = lean_array_push(x_21, x_1);
x_23 = lean_array_push(x_22, x_2);
x_24 = l_Lean_Meta_mkCongrArg___closed__2;
x_25 = l_Lean_Meta_mkEqSymm___closed__3;
x_26 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_23);
lean_ctor_set(x_26, 3, x_20);
if (lean_is_scalar(x_12)) {
 x_27 = lean_alloc_ctor(1, 2, 0);
} else {
 x_27 = x_12;
 lean_ctor_set_tag(x_27, 1);
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_11);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_12);
x_28 = lean_ctor_get(x_13, 0);
lean_inc(x_28);
lean_dec(x_13);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_14, 1);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_ctor_get(x_29, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_29, 1);
lean_inc(x_33);
lean_dec(x_29);
lean_inc(x_3);
lean_inc(x_30);
x_34 = l_Lean_Meta_getLevel(x_30, x_3, x_11);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_31);
x_37 = l_Lean_Meta_getLevel(x_31, x_3, x_36);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Meta_mkCongrArg___closed__2;
x_44 = l_Lean_mkConst(x_43, x_42);
x_45 = l_Lean_mkApp6(x_44, x_30, x_31, x_32, x_33, x_1, x_2);
lean_ctor_set(x_37, 0, x_45);
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_ctor_get(x_37, 0);
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_37);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_35);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Meta_mkCongrArg___closed__2;
x_52 = l_Lean_mkConst(x_51, x_50);
x_53 = l_Lean_mkApp6(x_52, x_30, x_31, x_32, x_33, x_1, x_2);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_47);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_37);
if (x_55 == 0)
{
return x_37;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_37, 0);
x_57 = lean_ctor_get(x_37, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_37);
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
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_34);
if (x_59 == 0)
{
return x_34;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_34, 0);
x_61 = lean_ctor_get(x_34, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_34);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
block_80:
{
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_12);
x_65 = lean_ctor_get(x_11, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_11, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_3, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_3, 0);
lean_inc(x_68);
lean_dec(x_3);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_66);
lean_ctor_set(x_70, 2, x_67);
lean_ctor_set(x_70, 3, x_69);
x_71 = l_Lean_mkAppStx___closed__9;
x_72 = lean_array_push(x_71, x_1);
x_73 = lean_array_push(x_72, x_2);
x_74 = l_Lean_Meta_mkCongrArg___closed__2;
x_75 = l_Lean_Meta_mkCongrArg___closed__3;
x_76 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
lean_ctor_set(x_76, 2, x_73);
lean_ctor_set(x_76, 3, x_70);
if (lean_is_scalar(x_8)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_8;
 lean_ctor_set_tag(x_77, 1);
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_11);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_8);
x_78 = lean_ctor_get(x_64, 0);
lean_inc(x_78);
lean_dec(x_64);
x_79 = lean_box(0);
x_13 = x_79;
x_14 = x_78;
goto block_63;
}
}
block_129:
{
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_12);
lean_dec(x_6);
x_82 = lean_ctor_get(x_11, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_11, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_3, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_3, 0);
lean_inc(x_85);
lean_dec(x_3);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
lean_dec(x_85);
x_87 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_83);
lean_ctor_set(x_87, 2, x_84);
lean_ctor_set(x_87, 3, x_86);
x_88 = l_Lean_mkAppStx___closed__9;
x_89 = lean_array_push(x_88, x_1);
x_90 = lean_array_push(x_89, x_2);
x_91 = l_Lean_Meta_mkCongrArg___closed__2;
x_92 = l_Lean_Meta_mkCongrArg___closed__3;
x_93 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_90);
lean_ctor_set(x_93, 3, x_87);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_11);
return x_94;
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_81);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_96 = lean_ctor_get(x_81, 0);
x_97 = lean_unsigned_to_nat(0u);
x_98 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_97);
x_99 = lean_nat_sub(x_98, x_97);
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_sub(x_99, x_100);
lean_dec(x_99);
x_102 = l_Lean_Expr_getRevArg_x21___main(x_6, x_101);
x_103 = lean_nat_sub(x_98, x_100);
x_104 = lean_nat_sub(x_103, x_100);
lean_dec(x_103);
x_105 = l_Lean_Expr_getRevArg_x21___main(x_6, x_104);
x_106 = lean_unsigned_to_nat(2u);
x_107 = lean_nat_sub(x_98, x_106);
lean_dec(x_98);
x_108 = lean_nat_sub(x_107, x_100);
lean_dec(x_107);
x_109 = l_Lean_Expr_getRevArg_x21___main(x_6, x_108);
lean_dec(x_6);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_105);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_102);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_81, 0, x_111);
x_13 = x_81;
x_14 = x_96;
goto block_63;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_112 = lean_ctor_get(x_81, 0);
lean_inc(x_112);
lean_dec(x_81);
x_113 = lean_unsigned_to_nat(0u);
x_114 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_113);
x_115 = lean_nat_sub(x_114, x_113);
x_116 = lean_unsigned_to_nat(1u);
x_117 = lean_nat_sub(x_115, x_116);
lean_dec(x_115);
x_118 = l_Lean_Expr_getRevArg_x21___main(x_6, x_117);
x_119 = lean_nat_sub(x_114, x_116);
x_120 = lean_nat_sub(x_119, x_116);
lean_dec(x_119);
x_121 = l_Lean_Expr_getRevArg_x21___main(x_6, x_120);
x_122 = lean_unsigned_to_nat(2u);
x_123 = lean_nat_sub(x_114, x_122);
lean_dec(x_114);
x_124 = lean_nat_sub(x_123, x_116);
lean_dec(x_123);
x_125 = l_Lean_Expr_getRevArg_x21___main(x_6, x_124);
lean_dec(x_6);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_121);
lean_ctor_set(x_126, 1, x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_118);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
x_13 = x_128;
x_14 = x_112;
goto block_63;
}
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_9);
if (x_142 == 0)
{
return x_9;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_9, 0);
x_144 = lean_ctor_get(x_9, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_9);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_146 = !lean_is_exclusive(x_5);
if (x_146 == 0)
{
return x_5;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_5, 0);
x_148 = lean_ctor_get(x_5, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_5);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
}
lean_object* _init_l_Lean_Meta_mkCongrFun___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("congrFun");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkCongrFun___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkCongrFun___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkCongrFun___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("equality proof between functions expected");
return x_1;
}
}
lean_object* l_Lean_Meta_mkCongrFun(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l___private_Init_Lean_Meta_AppBuilder_1__infer(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_Expr_eq_x3f___closed__2;
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Expr_isAppOfArity___main(x_7, x_9, x_10);
x_12 = l_coeDecidableEq(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_7);
x_13 = lean_ctor_get(x_8, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_17);
x_19 = l_Lean_mkAppStx___closed__9;
x_20 = lean_array_push(x_19, x_1);
x_21 = lean_array_push(x_20, x_2);
x_22 = l_Lean_Meta_mkCongrFun___closed__2;
x_23 = l_Lean_Meta_mkEqSymm___closed__3;
x_24 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_18);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_24);
return x_5;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_5);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Expr_getAppNumArgsAux___main(x_7, x_25);
x_27 = lean_nat_sub(x_26, x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_sub(x_27, x_28);
lean_dec(x_27);
x_30 = l_Lean_Expr_getRevArg_x21___main(x_7, x_29);
x_31 = lean_nat_sub(x_26, x_28);
x_32 = lean_nat_sub(x_31, x_28);
lean_dec(x_31);
x_33 = l_Lean_Expr_getRevArg_x21___main(x_7, x_32);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_nat_sub(x_26, x_34);
lean_dec(x_26);
x_36 = lean_nat_sub(x_35, x_28);
lean_dec(x_35);
x_37 = l_Lean_Expr_getRevArg_x21___main(x_7, x_36);
lean_dec(x_7);
lean_inc(x_3);
x_38 = l_Lean_Meta_whnfD(x_30, x_3, x_8);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_41 = x_38;
} else {
 lean_dec_ref(x_38);
 x_41 = lean_box(0);
}
if (lean_obj_tag(x_39) == 7)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_41);
x_57 = lean_ctor_get(x_39, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_39, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_39, 2);
lean_inc(x_59);
lean_dec(x_39);
x_60 = 0;
lean_inc(x_58);
x_61 = l_Lean_mkLambda(x_57, x_60, x_58, x_59);
lean_inc(x_3);
lean_inc(x_58);
x_62 = l_Lean_Meta_getLevel(x_58, x_3, x_40);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_2);
lean_inc(x_61);
x_65 = l_Lean_mkApp(x_61, x_2);
x_66 = l_Lean_Meta_getLevel(x_65, x_3, x_64);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_68 = lean_ctor_get(x_66, 0);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_63);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Meta_mkCongrFun___closed__2;
x_73 = l_Lean_mkConst(x_72, x_71);
x_74 = l_Lean_mkApp6(x_73, x_58, x_61, x_33, x_37, x_1, x_2);
lean_ctor_set(x_66, 0, x_74);
return x_66;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_75 = lean_ctor_get(x_66, 0);
x_76 = lean_ctor_get(x_66, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_66);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_63);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_Meta_mkCongrFun___closed__2;
x_81 = l_Lean_mkConst(x_80, x_79);
x_82 = l_Lean_mkApp6(x_81, x_58, x_61, x_33, x_37, x_1, x_2);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_76);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_dec(x_63);
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_66);
if (x_84 == 0)
{
return x_66;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_66, 0);
x_86 = lean_ctor_get(x_66, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_66);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_61);
lean_dec(x_58);
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_62);
if (x_88 == 0)
{
return x_62;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_62, 0);
x_90 = lean_ctor_get(x_62, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_62);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
lean_object* x_92; 
lean_dec(x_39);
lean_dec(x_37);
lean_dec(x_33);
x_92 = lean_box(0);
x_42 = x_92;
goto block_56;
}
block_56:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_42);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_3, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
lean_dec(x_3);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_43);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_45);
lean_ctor_set(x_48, 3, x_47);
x_49 = l_Lean_mkAppStx___closed__9;
x_50 = lean_array_push(x_49, x_1);
x_51 = lean_array_push(x_50, x_2);
x_52 = l_Lean_Meta_mkCongrFun___closed__2;
x_53 = l_Lean_Meta_mkCongrFun___closed__3;
x_54 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_54, 2, x_51);
lean_ctor_set(x_54, 3, x_48);
if (lean_is_scalar(x_41)) {
 x_55 = lean_alloc_ctor(1, 2, 0);
} else {
 x_55 = x_41;
 lean_ctor_set_tag(x_55, 1);
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_40);
return x_55;
}
}
else
{
uint8_t x_93; 
lean_dec(x_37);
lean_dec(x_33);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_38);
if (x_93 == 0)
{
return x_38;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_38, 0);
x_95 = lean_ctor_get(x_38, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_38);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_102; 
x_97 = lean_ctor_get(x_5, 0);
x_98 = lean_ctor_get(x_5, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_5);
x_99 = l_Lean_Expr_eq_x3f___closed__2;
x_100 = lean_unsigned_to_nat(3u);
x_101 = l_Lean_Expr_isAppOfArity___main(x_97, x_99, x_100);
x_102 = l_coeDecidableEq(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_97);
x_103 = lean_ctor_get(x_98, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
x_105 = lean_ctor_get(x_3, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_3, 0);
lean_inc(x_106);
lean_dec(x_3);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_108, 0, x_103);
lean_ctor_set(x_108, 1, x_104);
lean_ctor_set(x_108, 2, x_105);
lean_ctor_set(x_108, 3, x_107);
x_109 = l_Lean_mkAppStx___closed__9;
x_110 = lean_array_push(x_109, x_1);
x_111 = lean_array_push(x_110, x_2);
x_112 = l_Lean_Meta_mkCongrFun___closed__2;
x_113 = l_Lean_Meta_mkEqSymm___closed__3;
x_114 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
lean_ctor_set(x_114, 2, x_111);
lean_ctor_set(x_114, 3, x_108);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_98);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_116 = lean_unsigned_to_nat(0u);
x_117 = l_Lean_Expr_getAppNumArgsAux___main(x_97, x_116);
x_118 = lean_nat_sub(x_117, x_116);
x_119 = lean_unsigned_to_nat(1u);
x_120 = lean_nat_sub(x_118, x_119);
lean_dec(x_118);
x_121 = l_Lean_Expr_getRevArg_x21___main(x_97, x_120);
x_122 = lean_nat_sub(x_117, x_119);
x_123 = lean_nat_sub(x_122, x_119);
lean_dec(x_122);
x_124 = l_Lean_Expr_getRevArg_x21___main(x_97, x_123);
x_125 = lean_unsigned_to_nat(2u);
x_126 = lean_nat_sub(x_117, x_125);
lean_dec(x_117);
x_127 = lean_nat_sub(x_126, x_119);
lean_dec(x_126);
x_128 = l_Lean_Expr_getRevArg_x21___main(x_97, x_127);
lean_dec(x_97);
lean_inc(x_3);
x_129 = l_Lean_Meta_whnfD(x_121, x_3, x_98);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_132 = x_129;
} else {
 lean_dec_ref(x_129);
 x_132 = lean_box(0);
}
if (lean_obj_tag(x_130) == 7)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_132);
x_148 = lean_ctor_get(x_130, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_130, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_130, 2);
lean_inc(x_150);
lean_dec(x_130);
x_151 = 0;
lean_inc(x_149);
x_152 = l_Lean_mkLambda(x_148, x_151, x_149, x_150);
lean_inc(x_3);
lean_inc(x_149);
x_153 = l_Lean_Meta_getLevel(x_149, x_3, x_131);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
lean_inc(x_2);
lean_inc(x_152);
x_156 = l_Lean_mkApp(x_152, x_2);
x_157 = l_Lean_Meta_getLevel(x_156, x_3, x_155);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_160 = x_157;
} else {
 lean_dec_ref(x_157);
 x_160 = lean_box(0);
}
x_161 = lean_box(0);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_158);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_163, 0, x_154);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Lean_Meta_mkCongrFun___closed__2;
x_165 = l_Lean_mkConst(x_164, x_163);
x_166 = l_Lean_mkApp6(x_165, x_149, x_152, x_124, x_128, x_1, x_2);
if (lean_is_scalar(x_160)) {
 x_167 = lean_alloc_ctor(0, 2, 0);
} else {
 x_167 = x_160;
}
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_159);
return x_167;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_154);
lean_dec(x_152);
lean_dec(x_149);
lean_dec(x_128);
lean_dec(x_124);
lean_dec(x_2);
lean_dec(x_1);
x_168 = lean_ctor_get(x_157, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_157, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_170 = x_157;
} else {
 lean_dec_ref(x_157);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(1, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_152);
lean_dec(x_149);
lean_dec(x_128);
lean_dec(x_124);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_172 = lean_ctor_get(x_153, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_153, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_174 = x_153;
} else {
 lean_dec_ref(x_153);
 x_174 = lean_box(0);
}
if (lean_is_scalar(x_174)) {
 x_175 = lean_alloc_ctor(1, 2, 0);
} else {
 x_175 = x_174;
}
lean_ctor_set(x_175, 0, x_172);
lean_ctor_set(x_175, 1, x_173);
return x_175;
}
}
else
{
lean_object* x_176; 
lean_dec(x_130);
lean_dec(x_128);
lean_dec(x_124);
x_176 = lean_box(0);
x_133 = x_176;
goto block_147;
}
block_147:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_133);
x_134 = lean_ctor_get(x_131, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_3, 1);
lean_inc(x_136);
x_137 = lean_ctor_get(x_3, 0);
lean_inc(x_137);
lean_dec(x_3);
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec(x_137);
x_139 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_139, 0, x_134);
lean_ctor_set(x_139, 1, x_135);
lean_ctor_set(x_139, 2, x_136);
lean_ctor_set(x_139, 3, x_138);
x_140 = l_Lean_mkAppStx___closed__9;
x_141 = lean_array_push(x_140, x_1);
x_142 = lean_array_push(x_141, x_2);
x_143 = l_Lean_Meta_mkCongrFun___closed__2;
x_144 = l_Lean_Meta_mkCongrFun___closed__3;
x_145 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
lean_ctor_set(x_145, 2, x_142);
lean_ctor_set(x_145, 3, x_139);
if (lean_is_scalar(x_132)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_132;
 lean_ctor_set_tag(x_146, 1);
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_131);
return x_146;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_128);
lean_dec(x_124);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_177 = lean_ctor_get(x_129, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_129, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_179 = x_129;
} else {
 lean_dec_ref(x_129);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_181 = !lean_is_exclusive(x_5);
if (x_181 == 0)
{
return x_5;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_5, 0);
x_183 = lean_ctor_get(x_5, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_5);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
}
lean_object* _init_l_Lean_Meta_mkCongr___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("congr");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_mkCongr___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_mkCongr___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkCongr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
lean_inc(x_1);
x_5 = l___private_Init_Lean_Meta_AppBuilder_1__infer(x_1, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l___private_Init_Lean_Meta_AppBuilder_1__infer(x_2, x_3, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_27; lean_object* x_28; lean_object* x_97; lean_object* x_98; uint8_t x_99; uint8_t x_100; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_97 = l_Lean_Expr_eq_x3f___closed__2;
x_98 = lean_unsigned_to_nat(3u);
x_99 = l_Lean_Expr_isAppOfArity___main(x_6, x_97, x_98);
x_100 = l_coeDecidableEq(x_99);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec(x_9);
lean_dec(x_6);
x_101 = lean_box(0);
x_12 = x_101;
goto block_26;
}
else
{
uint8_t x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_102 = l_Lean_Expr_isAppOfArity___main(x_9, x_97, x_98);
x_103 = l_coeDecidableEq(x_102);
x_104 = lean_unsigned_to_nat(0u);
x_105 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_104);
x_106 = lean_nat_sub(x_105, x_104);
x_107 = lean_unsigned_to_nat(1u);
x_108 = lean_nat_sub(x_106, x_107);
lean_dec(x_106);
x_109 = l_Lean_Expr_getRevArg_x21___main(x_6, x_108);
x_110 = lean_nat_sub(x_105, x_107);
x_111 = lean_nat_sub(x_110, x_107);
lean_dec(x_110);
x_112 = l_Lean_Expr_getRevArg_x21___main(x_6, x_111);
x_113 = lean_unsigned_to_nat(2u);
x_114 = lean_nat_sub(x_105, x_113);
lean_dec(x_105);
x_115 = lean_nat_sub(x_114, x_107);
lean_dec(x_114);
x_116 = l_Lean_Expr_getRevArg_x21___main(x_6, x_115);
lean_dec(x_6);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_112);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_109);
lean_ctor_set(x_118, 1, x_117);
if (x_103 == 0)
{
lean_object* x_119; 
lean_dec(x_9);
x_119 = lean_box(0);
x_27 = x_119;
x_28 = x_118;
goto block_96;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_120 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_104);
x_121 = lean_nat_sub(x_120, x_104);
x_122 = lean_nat_sub(x_121, x_107);
lean_dec(x_121);
x_123 = l_Lean_Expr_getRevArg_x21___main(x_9, x_122);
x_124 = lean_nat_sub(x_120, x_107);
x_125 = lean_nat_sub(x_124, x_107);
lean_dec(x_124);
x_126 = l_Lean_Expr_getRevArg_x21___main(x_9, x_125);
x_127 = lean_nat_sub(x_120, x_113);
lean_dec(x_120);
x_128 = lean_nat_sub(x_127, x_107);
lean_dec(x_127);
x_129 = l_Lean_Expr_getRevArg_x21___main(x_9, x_128);
lean_dec(x_9);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_126);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_123);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_27 = x_132;
x_28 = x_118;
goto block_96;
}
}
block_26:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_17);
x_19 = l_Lean_mkAppStx___closed__9;
x_20 = lean_array_push(x_19, x_1);
x_21 = lean_array_push(x_20, x_2);
x_22 = l_Lean_Meta_mkCongr___closed__2;
x_23 = l_Lean_Meta_mkEqSymm___closed__3;
x_24 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_18);
if (lean_is_scalar(x_11)) {
 x_25 = lean_alloc_ctor(1, 2, 0);
} else {
 x_25 = x_11;
 lean_ctor_set_tag(x_25, 1);
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
block_96:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_30; 
lean_dec(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_12 = x_30;
goto block_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_11);
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec(x_27);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_dec(x_29);
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec(x_31);
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_dec(x_32);
lean_inc(x_3);
x_39 = l_Lean_Meta_whnfD(x_33, x_3, x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_42 = x_39;
} else {
 lean_dec_ref(x_39);
 x_42 = lean_box(0);
}
if (lean_obj_tag(x_40) == 7)
{
lean_object* x_58; uint8_t x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_40, 2);
lean_inc(x_58);
lean_dec(x_40);
x_59 = l_Lean_Expr_hasLooseBVars(x_58);
x_60 = l_coeDecidableEq(x_59);
if (x_60 == 0)
{
lean_object* x_61; 
lean_dec(x_42);
lean_inc(x_3);
lean_inc(x_36);
x_61 = l_Lean_Meta_getLevel(x_36, x_3, x_41);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_58);
x_64 = l_Lean_Meta_getLevel(x_58, x_3, x_63);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_68);
x_70 = l_Lean_Meta_mkCongr___closed__2;
x_71 = l_Lean_mkConst(x_70, x_69);
x_72 = l_Lean_mkApp8(x_71, x_36, x_58, x_34, x_35, x_37, x_38, x_1, x_2);
lean_ctor_set(x_64, 0, x_72);
return x_64;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_73 = lean_ctor_get(x_64, 0);
x_74 = lean_ctor_get(x_64, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_64);
x_75 = lean_box(0);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_62);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Meta_mkCongr___closed__2;
x_79 = l_Lean_mkConst(x_78, x_77);
x_80 = l_Lean_mkApp8(x_79, x_36, x_58, x_34, x_35, x_37, x_38, x_1, x_2);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_74);
return x_81;
}
}
else
{
uint8_t x_82; 
lean_dec(x_62);
lean_dec(x_58);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_64);
if (x_82 == 0)
{
return x_64;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_64, 0);
x_84 = lean_ctor_get(x_64, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_64);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_58);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_61);
if (x_86 == 0)
{
return x_61;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_61, 0);
x_88 = lean_ctor_get(x_61, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_61);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; 
lean_dec(x_58);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_90 = lean_box(0);
x_43 = x_90;
goto block_57;
}
}
else
{
lean_object* x_91; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_91 = lean_box(0);
x_43 = x_91;
goto block_57;
}
block_57:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_43);
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_3, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 0);
lean_inc(x_47);
lean_dec(x_3);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_48);
x_50 = l_Lean_mkAppStx___closed__9;
x_51 = lean_array_push(x_50, x_1);
x_52 = lean_array_push(x_51, x_2);
x_53 = l_Lean_Meta_mkCongr___closed__2;
x_54 = l_Lean_Meta_mkCongrArg___closed__3;
x_55 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_55, 2, x_52);
lean_ctor_set(x_55, 3, x_49);
if (lean_is_scalar(x_42)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_42;
 lean_ctor_set_tag(x_56, 1);
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_41);
return x_56;
}
}
else
{
uint8_t x_92; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_39);
if (x_92 == 0)
{
return x_39;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_39, 0);
x_94 = lean_ctor_get(x_39, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_39);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_8);
if (x_133 == 0)
{
return x_8;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_8, 0);
x_135 = lean_ctor_get(x_8, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_8);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_5);
if (x_137 == 0)
{
return x_5;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_5, 0);
x_139 = lean_ctor_get(x_5, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_5);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_2, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_array_fget(x_1, x_2);
lean_inc(x_9);
x_10 = l_Lean_Meta_getMVarDecl(x_9, x_3, x_4);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 2);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_3);
x_14 = l_Lean_Meta_synthInstance(x_13, x_3, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_assignExprMVar(x_9, x_15, x_3, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_2 = x_20;
x_4 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
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
lean_dec(x_9);
lean_dec(x_3);
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
else
{
uint8_t x_30; 
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_10);
if (x_30 == 0)
{
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_10, 0);
x_32 = lean_ctor_get(x_10, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_10);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
lean_object* _init_l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("mkAppM");
return x_1;
}
}
lean_object* _init_l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("result contains metavariables");
return x_1;
}
}
lean_object* l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(0u);
lean_inc(x_4);
x_7 = l_Array_forMAux___main___at___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___spec__1(x_3, x_6, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_2, x_2, x_6, x_1);
x_10 = l_Lean_Meta_instantiateMVars(x_9, x_4, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_hasAssignableMVar(x_11, x_4, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
uint8_t x_16; 
lean_dec(x_4);
x_16 = !lean_is_exclusive(x_13);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_13, 0);
lean_dec(x_17);
lean_ctor_set(x_13, 0, x_11);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_13);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_21 = lean_ctor_get(x_13, 1);
x_22 = lean_ctor_get(x_13, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
lean_dec(x_4);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_27);
x_29 = l_Lean_mkOptionalNode___closed__2;
x_30 = lean_array_push(x_29, x_11);
x_31 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__2;
x_32 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__3;
x_33 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_30);
lean_ctor_set(x_33, 3, x_28);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_33);
return x_13;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_dec(x_13);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_4, 0);
lean_inc(x_38);
lean_dec(x_4);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_35);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_40, 2, x_37);
lean_ctor_set(x_40, 3, x_39);
x_41 = l_Lean_mkOptionalNode___closed__2;
x_42 = lean_array_push(x_41, x_11);
x_43 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__2;
x_44 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__3;
x_45 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_40);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_34);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_4);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_7);
if (x_47 == 0)
{
return x_7;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_7, 0);
x_49 = lean_ctor_get(x_7, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_7);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
lean_object* l_Array_forMAux___main___at___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_forMAux___main___at___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
lean_object* _init_l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("too many explicit arguments provided");
return x_1;
}
}
lean_object* l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
if (lean_obj_tag(x_7) == 7)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint64_t x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_119; lean_object* x_120; 
x_65 = lean_ctor_get(x_7, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_7, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_7, 2);
lean_inc(x_67);
x_68 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_69 = lean_array_get_size(x_4);
x_70 = lean_expr_instantiate_rev_range(x_66, x_5, x_69, x_4);
lean_dec(x_69);
lean_dec(x_66);
x_119 = (uint8_t)((x_68 << 24) >> 61);
x_120 = lean_box(x_119);
switch (lean_obj_tag(x_120)) {
case 1:
{
uint8_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_121 = 0;
lean_inc(x_8);
x_122 = l_Lean_Meta_mkFreshExprMVar(x_70, x_65, x_121, x_8, x_9);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_array_push(x_4, x_123);
x_4 = x_125;
x_7 = x_67;
x_9 = x_124;
goto _start;
}
case 3:
{
uint8_t x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_127 = 1;
lean_inc(x_8);
x_128 = l_Lean_Meta_mkFreshExprMVar(x_70, x_65, x_127, x_8, x_9);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
lean_inc(x_129);
x_131 = lean_array_push(x_4, x_129);
x_132 = l_Lean_Expr_mvarId_x21(x_129);
lean_dec(x_129);
x_133 = lean_array_push(x_6, x_132);
x_4 = x_131;
x_6 = x_133;
x_7 = x_67;
x_9 = x_130;
goto _start;
}
default: 
{
lean_object* x_135; 
lean_dec(x_120);
lean_dec(x_65);
x_135 = lean_box(0);
x_71 = x_135;
goto block_118;
}
}
block_118:
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_71);
x_72 = lean_array_get_size(x_2);
x_73 = lean_nat_dec_lt(x_3, x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_5);
lean_dec(x_3);
x_74 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal(x_1, x_4, x_6, x_8, x_9);
lean_dec(x_6);
lean_dec(x_4);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_array_fget(x_2, x_3);
lean_inc(x_8);
lean_inc(x_75);
x_76 = l_Lean_Meta_inferType(x_75, x_8, x_9);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
lean_inc(x_8);
x_79 = l_Lean_Meta_isExprDefEq(x_70, x_77, x_8, x_78);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
uint8_t x_82; 
lean_dec(x_67);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_82 = !lean_is_exclusive(x_79);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_83 = lean_ctor_get(x_79, 1);
x_84 = lean_ctor_get(x_79, 0);
lean_dec(x_84);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_8, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_8, 0);
lean_inc(x_88);
lean_dec(x_8);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec(x_88);
x_90 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_90, 0, x_85);
lean_ctor_set(x_90, 1, x_86);
lean_ctor_set(x_90, 2, x_87);
lean_ctor_set(x_90, 3, x_89);
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_4, x_4, x_91, x_1);
lean_dec(x_4);
x_93 = lean_alloc_ctor(14, 3, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_75);
lean_ctor_set(x_93, 2, x_90);
lean_ctor_set_tag(x_79, 1);
lean_ctor_set(x_79, 0, x_93);
return x_79;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_94 = lean_ctor_get(x_79, 1);
lean_inc(x_94);
lean_dec(x_79);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_8, 1);
lean_inc(x_97);
x_98 = lean_ctor_get(x_8, 0);
lean_inc(x_98);
lean_dec(x_8);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_96);
lean_ctor_set(x_100, 2, x_97);
lean_ctor_set(x_100, 3, x_99);
x_101 = lean_unsigned_to_nat(0u);
x_102 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_4, x_4, x_101, x_1);
lean_dec(x_4);
x_103 = lean_alloc_ctor(14, 3, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_75);
lean_ctor_set(x_103, 2, x_100);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_94);
return x_104;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_79, 1);
lean_inc(x_105);
lean_dec(x_79);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_add(x_3, x_106);
lean_dec(x_3);
x_108 = lean_array_push(x_4, x_75);
x_3 = x_107;
x_4 = x_108;
x_7 = x_67;
x_9 = x_105;
goto _start;
}
}
else
{
uint8_t x_110; 
lean_dec(x_75);
lean_dec(x_67);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_79);
if (x_110 == 0)
{
return x_79;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_79, 0);
x_112 = lean_ctor_get(x_79, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_79);
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
lean_dec(x_75);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_76);
if (x_114 == 0)
{
return x_76;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_76, 0);
x_116 = lean_ctor_get(x_76, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_76);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
else
{
lean_object* x_136; 
x_136 = lean_box(0);
x_10 = x_136;
goto block_64;
}
block_64:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
x_11 = lean_array_get_size(x_4);
x_12 = lean_expr_instantiate_rev_range(x_7, x_5, x_11, x_4);
lean_dec(x_5);
lean_dec(x_7);
lean_inc(x_8);
x_13 = l_Lean_Meta_whnfD(x_12, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Expr_isForall(x_15);
x_18 = l_coeDecidableEq(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; uint8_t x_21; 
lean_dec(x_15);
lean_dec(x_11);
x_19 = lean_array_get_size(x_2);
x_20 = lean_nat_dec_eq(x_3, x_19);
lean_dec(x_19);
lean_dec(x_3);
x_21 = l_coeDecidableEq(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_6);
lean_dec(x_4);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_8, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_8, 0);
lean_inc(x_25);
lean_dec(x_8);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_26);
x_28 = l_Lean_mkOptionalNode___closed__2;
x_29 = lean_array_push(x_28, x_1);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2, x_2, x_30, x_29);
x_32 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__2;
x_33 = l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main___closed__1;
x_34 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_31);
lean_ctor_set(x_34, 3, x_27);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_34);
return x_13;
}
else
{
lean_object* x_35; 
lean_free_object(x_13);
x_35 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal(x_1, x_4, x_6, x_8, x_16);
lean_dec(x_6);
lean_dec(x_4);
return x_35;
}
}
else
{
lean_free_object(x_13);
x_5 = x_11;
x_7 = x_15;
x_9 = x_16;
goto _start;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_13, 0);
x_38 = lean_ctor_get(x_13, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_13);
x_39 = l_Lean_Expr_isForall(x_37);
x_40 = l_coeDecidableEq(x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; uint8_t x_43; 
lean_dec(x_37);
lean_dec(x_11);
x_41 = lean_array_get_size(x_2);
x_42 = lean_nat_dec_eq(x_3, x_41);
lean_dec(x_41);
lean_dec(x_3);
x_43 = l_coeDecidableEq(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_6);
lean_dec(x_4);
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_8, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_8, 0);
lean_inc(x_47);
lean_dec(x_8);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_44);
lean_ctor_set(x_49, 1, x_45);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_48);
x_50 = l_Lean_mkOptionalNode___closed__2;
x_51 = lean_array_push(x_50, x_1);
x_52 = lean_unsigned_to_nat(0u);
x_53 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2, x_2, x_52, x_51);
x_54 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__2;
x_55 = l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main___closed__1;
x_56 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
lean_ctor_set(x_56, 2, x_53);
lean_ctor_set(x_56, 3, x_49);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_38);
return x_57;
}
else
{
lean_object* x_58; 
x_58 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal(x_1, x_4, x_6, x_8, x_38);
lean_dec(x_6);
lean_dec(x_4);
return x_58;
}
}
else
{
x_5 = x_11;
x_7 = x_37;
x_9 = x_38;
goto _start;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_13);
if (x_60 == 0)
{
return x_13;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_13, 0);
x_62 = lean_ctor_get(x_13, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_13);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
lean_object* l_List_mapM___main___at_Lean_Meta_mkAppM___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_ctor_get(x_1, 0);
lean_dec(x_8);
x_9 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_List_mapM___main___at_Lean_Meta_mkAppM___spec__1(x_7, x_2, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_1, 1, x_14);
lean_ctor_set(x_1, 0, x_10);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_1, 1, x_15);
lean_ctor_set(x_1, 0, x_10);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = l_Lean_Meta_mkFreshLevelMVar___rarg(x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_List_mapM___main___at_Lean_Meta_mkAppM___spec__1(x_18, x_2, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_20);
lean_ctor_set(x_26, 1, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
}
lean_object* _init_l_Lean_Meta_mkAppM___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_Basic_10__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__68;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkAppM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_389; uint8_t x_390; 
x_389 = lean_ctor_get(x_4, 4);
lean_inc(x_389);
x_390 = lean_ctor_get_uint8(x_389, sizeof(void*)*1);
lean_dec(x_389);
if (x_390 == 0)
{
uint8_t x_391; 
x_391 = l_String_posOfAux___main___closed__2;
if (x_391 == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; uint8_t x_396; 
x_392 = l_Lean_Meta_mkAppM___closed__1;
x_393 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_392, x_3, x_4);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
lean_dec(x_393);
x_396 = lean_unbox(x_394);
lean_dec(x_394);
x_5 = x_396;
x_6 = x_395;
goto block_388;
}
else
{
uint8_t x_397; 
x_397 = 0;
x_5 = x_397;
x_6 = x_4;
goto block_388;
}
}
else
{
uint8_t x_398; 
x_398 = l_String_posOfAux___main___closed__1;
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; uint8_t x_403; 
x_399 = l_Lean_Meta_mkAppM___closed__1;
x_400 = l___private_Init_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_399, x_3, x_4);
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_400, 1);
lean_inc(x_402);
lean_dec(x_400);
x_403 = lean_unbox(x_401);
lean_dec(x_401);
x_5 = x_403;
x_6 = x_402;
goto block_388;
}
else
{
uint8_t x_404; 
x_404 = 0;
x_5 = x_404;
x_6 = x_4;
goto block_388;
}
}
block_388:
{
uint8_t x_7; 
if (x_5 == 0)
{
uint8_t x_386; 
x_386 = 1;
x_7 = x_386;
goto block_385;
}
else
{
uint8_t x_387; 
x_387 = 0;
x_7 = x_387;
goto block_385;
}
block_385:
{
uint8_t x_8; 
x_8 = l_coeDecidableEq(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = l___private_Init_Lean_Util_Trace_3__getResetTraces___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__1___rarg(x_6);
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = l_Lean_MetavarContext_incDepth(x_13);
lean_ctor_set(x_10, 1, x_14);
lean_inc(x_1);
x_15 = l_Lean_Meta_getConstInfo(x_1, x_3, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_ConstantInfo_lparams(x_16);
x_19 = l_List_mapM___main___at_Lean_Meta_mkAppM___spec__1(x_18, x_3, x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_20);
x_22 = l_Lean_mkConst(x_1, x_20);
x_23 = lean_instantiate_type_lparams(x_16, x_20);
lean_dec(x_20);
lean_dec(x_16);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Array_empty___closed__1;
lean_inc(x_3);
x_26 = l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main(x_22, x_2, x_24, x_25, x_24, x_25, x_23, x_3, x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_27, 1);
lean_dec(x_30);
lean_ctor_set(x_27, 1, x_13);
x_31 = l_Lean_Meta_mkAppM___closed__1;
x_32 = l___private_Init_Lean_Util_Trace_2__addNode___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_11, x_31, x_3, x_27);
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
lean_ctor_set(x_32, 0, x_28);
return x_32;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_27, 0);
x_38 = lean_ctor_get(x_27, 2);
x_39 = lean_ctor_get(x_27, 3);
x_40 = lean_ctor_get(x_27, 4);
x_41 = lean_ctor_get(x_27, 5);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_27);
x_42 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_13);
lean_ctor_set(x_42, 2, x_38);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 4, x_40);
lean_ctor_set(x_42, 5, x_41);
x_43 = l_Lean_Meta_mkAppM___closed__1;
x_44 = l___private_Init_Lean_Util_Trace_2__addNode___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_11, x_43, x_3, x_42);
lean_dec(x_3);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
if (lean_is_scalar(x_46)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_46;
}
lean_ctor_set(x_47, 0, x_28);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_26, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_26, 0);
lean_inc(x_49);
lean_dec(x_26);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_48, 1);
lean_dec(x_51);
lean_ctor_set(x_48, 1, x_13);
x_52 = l_Lean_Meta_mkAppM___closed__1;
x_53 = l___private_Init_Lean_Util_Trace_2__addNode___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_11, x_52, x_3, x_48);
lean_dec(x_3);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set_tag(x_53, 1);
lean_ctor_set(x_53, 0, x_49);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_58 = lean_ctor_get(x_48, 0);
x_59 = lean_ctor_get(x_48, 2);
x_60 = lean_ctor_get(x_48, 3);
x_61 = lean_ctor_get(x_48, 4);
x_62 = lean_ctor_get(x_48, 5);
lean_inc(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_48);
x_63 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_63, 0, x_58);
lean_ctor_set(x_63, 1, x_13);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_60);
lean_ctor_set(x_63, 4, x_61);
lean_ctor_set(x_63, 5, x_62);
x_64 = l_Lean_Meta_mkAppM___closed__1;
x_65 = l___private_Init_Lean_Util_Trace_2__addNode___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_11, x_64, x_3, x_63);
lean_dec(x_3);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_67 = x_65;
} else {
 lean_dec_ref(x_65);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
 lean_ctor_set_tag(x_68, 1);
}
lean_ctor_set(x_68, 0, x_49);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_dec(x_1);
x_69 = lean_ctor_get(x_15, 1);
lean_inc(x_69);
x_70 = lean_ctor_get(x_15, 0);
lean_inc(x_70);
lean_dec(x_15);
x_71 = !lean_is_exclusive(x_69);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_69, 1);
lean_dec(x_72);
lean_ctor_set(x_69, 1, x_13);
x_73 = l_Lean_Meta_mkAppM___closed__1;
x_74 = l___private_Init_Lean_Util_Trace_2__addNode___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_11, x_73, x_3, x_69);
lean_dec(x_3);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
lean_ctor_set_tag(x_74, 1);
lean_ctor_set(x_74, 0, x_70);
return x_74;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_74, 1);
lean_inc(x_77);
lean_dec(x_74);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_70);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_79 = lean_ctor_get(x_69, 0);
x_80 = lean_ctor_get(x_69, 2);
x_81 = lean_ctor_get(x_69, 3);
x_82 = lean_ctor_get(x_69, 4);
x_83 = lean_ctor_get(x_69, 5);
lean_inc(x_83);
lean_inc(x_82);
lean_inc(x_81);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_69);
x_84 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_13);
lean_ctor_set(x_84, 2, x_80);
lean_ctor_set(x_84, 3, x_81);
lean_ctor_set(x_84, 4, x_82);
lean_ctor_set(x_84, 5, x_83);
x_85 = l_Lean_Meta_mkAppM___closed__1;
x_86 = l___private_Init_Lean_Util_Trace_2__addNode___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_11, x_85, x_3, x_84);
lean_dec(x_3);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_88 = x_86;
} else {
 lean_dec_ref(x_86);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
 lean_ctor_set_tag(x_89, 1);
}
lean_ctor_set(x_89, 0, x_70);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_90 = lean_ctor_get(x_10, 0);
x_91 = lean_ctor_get(x_10, 1);
x_92 = lean_ctor_get(x_10, 2);
x_93 = lean_ctor_get(x_10, 3);
x_94 = lean_ctor_get(x_10, 4);
x_95 = lean_ctor_get(x_10, 5);
lean_inc(x_95);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_10);
lean_inc(x_91);
x_96 = l_Lean_MetavarContext_incDepth(x_91);
x_97 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_97, 0, x_90);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_97, 2, x_92);
lean_ctor_set(x_97, 3, x_93);
lean_ctor_set(x_97, 4, x_94);
lean_ctor_set(x_97, 5, x_95);
lean_inc(x_1);
x_98 = l_Lean_Meta_getConstInfo(x_1, x_3, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = l_Lean_ConstantInfo_lparams(x_99);
x_102 = l_List_mapM___main___at_Lean_Meta_mkAppM___spec__1(x_101, x_3, x_100);
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
lean_inc(x_103);
x_105 = l_Lean_mkConst(x_1, x_103);
x_106 = lean_instantiate_type_lparams(x_99, x_103);
lean_dec(x_103);
lean_dec(x_99);
x_107 = lean_unsigned_to_nat(0u);
x_108 = l_Array_empty___closed__1;
lean_inc(x_3);
x_109 = l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main(x_105, x_2, x_107, x_108, x_107, x_108, x_106, x_3, x_104);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_110 = lean_ctor_get(x_109, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 0);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_110, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_110, 3);
lean_inc(x_114);
x_115 = lean_ctor_get(x_110, 4);
lean_inc(x_115);
x_116 = lean_ctor_get(x_110, 5);
lean_inc(x_116);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 lean_ctor_release(x_110, 2);
 lean_ctor_release(x_110, 3);
 lean_ctor_release(x_110, 4);
 lean_ctor_release(x_110, 5);
 x_117 = x_110;
} else {
 lean_dec_ref(x_110);
 x_117 = lean_box(0);
}
if (lean_is_scalar(x_117)) {
 x_118 = lean_alloc_ctor(0, 6, 0);
} else {
 x_118 = x_117;
}
lean_ctor_set(x_118, 0, x_112);
lean_ctor_set(x_118, 1, x_91);
lean_ctor_set(x_118, 2, x_113);
lean_ctor_set(x_118, 3, x_114);
lean_ctor_set(x_118, 4, x_115);
lean_ctor_set(x_118, 5, x_116);
x_119 = l_Lean_Meta_mkAppM___closed__1;
x_120 = l___private_Init_Lean_Util_Trace_2__addNode___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_11, x_119, x_3, x_118);
lean_dec(x_3);
x_121 = lean_ctor_get(x_120, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_111);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_124 = lean_ctor_get(x_109, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_109, 0);
lean_inc(x_125);
lean_dec(x_109);
x_126 = lean_ctor_get(x_124, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_124, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_124, 3);
lean_inc(x_128);
x_129 = lean_ctor_get(x_124, 4);
lean_inc(x_129);
x_130 = lean_ctor_get(x_124, 5);
lean_inc(x_130);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 lean_ctor_release(x_124, 3);
 lean_ctor_release(x_124, 4);
 lean_ctor_release(x_124, 5);
 x_131 = x_124;
} else {
 lean_dec_ref(x_124);
 x_131 = lean_box(0);
}
if (lean_is_scalar(x_131)) {
 x_132 = lean_alloc_ctor(0, 6, 0);
} else {
 x_132 = x_131;
}
lean_ctor_set(x_132, 0, x_126);
lean_ctor_set(x_132, 1, x_91);
lean_ctor_set(x_132, 2, x_127);
lean_ctor_set(x_132, 3, x_128);
lean_ctor_set(x_132, 4, x_129);
lean_ctor_set(x_132, 5, x_130);
x_133 = l_Lean_Meta_mkAppM___closed__1;
x_134 = l___private_Init_Lean_Util_Trace_2__addNode___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_11, x_133, x_3, x_132);
lean_dec(x_3);
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_136 = x_134;
} else {
 lean_dec_ref(x_134);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
 lean_ctor_set_tag(x_137, 1);
}
lean_ctor_set(x_137, 0, x_125);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_1);
x_138 = lean_ctor_get(x_98, 1);
lean_inc(x_138);
x_139 = lean_ctor_get(x_98, 0);
lean_inc(x_139);
lean_dec(x_98);
x_140 = lean_ctor_get(x_138, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_138, 2);
lean_inc(x_141);
x_142 = lean_ctor_get(x_138, 3);
lean_inc(x_142);
x_143 = lean_ctor_get(x_138, 4);
lean_inc(x_143);
x_144 = lean_ctor_get(x_138, 5);
lean_inc(x_144);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 lean_ctor_release(x_138, 2);
 lean_ctor_release(x_138, 3);
 lean_ctor_release(x_138, 4);
 lean_ctor_release(x_138, 5);
 x_145 = x_138;
} else {
 lean_dec_ref(x_138);
 x_145 = lean_box(0);
}
if (lean_is_scalar(x_145)) {
 x_146 = lean_alloc_ctor(0, 6, 0);
} else {
 x_146 = x_145;
}
lean_ctor_set(x_146, 0, x_140);
lean_ctor_set(x_146, 1, x_91);
lean_ctor_set(x_146, 2, x_141);
lean_ctor_set(x_146, 3, x_142);
lean_ctor_set(x_146, 4, x_143);
lean_ctor_set(x_146, 5, x_144);
x_147 = l_Lean_Meta_mkAppM___closed__1;
x_148 = l___private_Init_Lean_Util_Trace_2__addNode___at___private_Init_Lean_Meta_LevelDefEq_10__processPostponedStep___spec__7(x_11, x_147, x_3, x_146);
lean_dec(x_3);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_150 = x_148;
} else {
 lean_dec_ref(x_148);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
 lean_ctor_set_tag(x_151, 1);
}
lean_ctor_set(x_151, 0, x_139);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
else
{
uint8_t x_152; 
x_152 = !lean_is_exclusive(x_6);
if (x_152 == 0)
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_ctor_get(x_6, 4);
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
lean_object* x_155; uint8_t x_156; uint8_t x_157; lean_object* x_158; lean_object* x_159; 
x_155 = lean_ctor_get(x_6, 1);
x_156 = lean_ctor_get_uint8(x_153, sizeof(void*)*1);
x_157 = 0;
lean_ctor_set_uint8(x_153, sizeof(void*)*1, x_157);
lean_inc(x_155);
x_158 = l_Lean_MetavarContext_incDepth(x_155);
lean_ctor_set(x_6, 1, x_158);
lean_inc(x_1);
x_159 = l_Lean_Meta_getConstInfo(x_1, x_3, x_6);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = l_Lean_ConstantInfo_lparams(x_160);
x_163 = l_List_mapM___main___at_Lean_Meta_mkAppM___spec__1(x_162, x_3, x_161);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
lean_inc(x_164);
x_166 = l_Lean_mkConst(x_1, x_164);
x_167 = lean_instantiate_type_lparams(x_160, x_164);
lean_dec(x_164);
lean_dec(x_160);
x_168 = lean_unsigned_to_nat(0u);
x_169 = l_Array_empty___closed__1;
x_170 = l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main(x_166, x_2, x_168, x_169, x_168, x_169, x_167, x_3, x_165);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
x_172 = lean_ctor_get(x_171, 4);
lean_inc(x_172);
x_173 = !lean_is_exclusive(x_170);
if (x_173 == 0)
{
lean_object* x_174; uint8_t x_175; 
x_174 = lean_ctor_get(x_170, 1);
lean_dec(x_174);
x_175 = !lean_is_exclusive(x_171);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_176 = lean_ctor_get(x_171, 4);
lean_dec(x_176);
x_177 = lean_ctor_get(x_171, 1);
lean_dec(x_177);
x_178 = !lean_is_exclusive(x_172);
if (x_178 == 0)
{
lean_ctor_set_uint8(x_172, sizeof(void*)*1, x_156);
lean_ctor_set(x_171, 1, x_155);
return x_170;
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_172, 0);
lean_inc(x_179);
lean_dec(x_172);
x_180 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set_uint8(x_180, sizeof(void*)*1, x_156);
lean_ctor_set(x_171, 4, x_180);
lean_ctor_set(x_171, 1, x_155);
return x_170;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_181 = lean_ctor_get(x_171, 0);
x_182 = lean_ctor_get(x_171, 2);
x_183 = lean_ctor_get(x_171, 3);
x_184 = lean_ctor_get(x_171, 5);
lean_inc(x_184);
lean_inc(x_183);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_171);
x_185 = lean_ctor_get(x_172, 0);
lean_inc(x_185);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 x_186 = x_172;
} else {
 lean_dec_ref(x_172);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(0, 1, 1);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set_uint8(x_187, sizeof(void*)*1, x_156);
x_188 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_188, 0, x_181);
lean_ctor_set(x_188, 1, x_155);
lean_ctor_set(x_188, 2, x_182);
lean_ctor_set(x_188, 3, x_183);
lean_ctor_set(x_188, 4, x_187);
lean_ctor_set(x_188, 5, x_184);
lean_ctor_set(x_170, 1, x_188);
return x_170;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_189 = lean_ctor_get(x_170, 0);
lean_inc(x_189);
lean_dec(x_170);
x_190 = lean_ctor_get(x_171, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_171, 2);
lean_inc(x_191);
x_192 = lean_ctor_get(x_171, 3);
lean_inc(x_192);
x_193 = lean_ctor_get(x_171, 5);
lean_inc(x_193);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 lean_ctor_release(x_171, 2);
 lean_ctor_release(x_171, 3);
 lean_ctor_release(x_171, 4);
 lean_ctor_release(x_171, 5);
 x_194 = x_171;
} else {
 lean_dec_ref(x_171);
 x_194 = lean_box(0);
}
x_195 = lean_ctor_get(x_172, 0);
lean_inc(x_195);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 x_196 = x_172;
} else {
 lean_dec_ref(x_172);
 x_196 = lean_box(0);
}
if (lean_is_scalar(x_196)) {
 x_197 = lean_alloc_ctor(0, 1, 1);
} else {
 x_197 = x_196;
}
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set_uint8(x_197, sizeof(void*)*1, x_156);
if (lean_is_scalar(x_194)) {
 x_198 = lean_alloc_ctor(0, 6, 0);
} else {
 x_198 = x_194;
}
lean_ctor_set(x_198, 0, x_190);
lean_ctor_set(x_198, 1, x_155);
lean_ctor_set(x_198, 2, x_191);
lean_ctor_set(x_198, 3, x_192);
lean_ctor_set(x_198, 4, x_197);
lean_ctor_set(x_198, 5, x_193);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_189);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; 
x_200 = lean_ctor_get(x_170, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_200, 4);
lean_inc(x_201);
x_202 = !lean_is_exclusive(x_170);
if (x_202 == 0)
{
lean_object* x_203; uint8_t x_204; 
x_203 = lean_ctor_get(x_170, 1);
lean_dec(x_203);
x_204 = !lean_is_exclusive(x_200);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; 
x_205 = lean_ctor_get(x_200, 4);
lean_dec(x_205);
x_206 = lean_ctor_get(x_200, 1);
lean_dec(x_206);
x_207 = !lean_is_exclusive(x_201);
if (x_207 == 0)
{
lean_ctor_set_uint8(x_201, sizeof(void*)*1, x_156);
lean_ctor_set(x_200, 1, x_155);
return x_170;
}
else
{
lean_object* x_208; lean_object* x_209; 
x_208 = lean_ctor_get(x_201, 0);
lean_inc(x_208);
lean_dec(x_201);
x_209 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_209, 0, x_208);
lean_ctor_set_uint8(x_209, sizeof(void*)*1, x_156);
lean_ctor_set(x_200, 4, x_209);
lean_ctor_set(x_200, 1, x_155);
return x_170;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_210 = lean_ctor_get(x_200, 0);
x_211 = lean_ctor_get(x_200, 2);
x_212 = lean_ctor_get(x_200, 3);
x_213 = lean_ctor_get(x_200, 5);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_200);
x_214 = lean_ctor_get(x_201, 0);
lean_inc(x_214);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_215 = x_201;
} else {
 lean_dec_ref(x_201);
 x_215 = lean_box(0);
}
if (lean_is_scalar(x_215)) {
 x_216 = lean_alloc_ctor(0, 1, 1);
} else {
 x_216 = x_215;
}
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set_uint8(x_216, sizeof(void*)*1, x_156);
x_217 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_217, 0, x_210);
lean_ctor_set(x_217, 1, x_155);
lean_ctor_set(x_217, 2, x_211);
lean_ctor_set(x_217, 3, x_212);
lean_ctor_set(x_217, 4, x_216);
lean_ctor_set(x_217, 5, x_213);
lean_ctor_set(x_170, 1, x_217);
return x_170;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_218 = lean_ctor_get(x_170, 0);
lean_inc(x_218);
lean_dec(x_170);
x_219 = lean_ctor_get(x_200, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_200, 2);
lean_inc(x_220);
x_221 = lean_ctor_get(x_200, 3);
lean_inc(x_221);
x_222 = lean_ctor_get(x_200, 5);
lean_inc(x_222);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 lean_ctor_release(x_200, 2);
 lean_ctor_release(x_200, 3);
 lean_ctor_release(x_200, 4);
 lean_ctor_release(x_200, 5);
 x_223 = x_200;
} else {
 lean_dec_ref(x_200);
 x_223 = lean_box(0);
}
x_224 = lean_ctor_get(x_201, 0);
lean_inc(x_224);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 x_225 = x_201;
} else {
 lean_dec_ref(x_201);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(0, 1, 1);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set_uint8(x_226, sizeof(void*)*1, x_156);
if (lean_is_scalar(x_223)) {
 x_227 = lean_alloc_ctor(0, 6, 0);
} else {
 x_227 = x_223;
}
lean_ctor_set(x_227, 0, x_219);
lean_ctor_set(x_227, 1, x_155);
lean_ctor_set(x_227, 2, x_220);
lean_ctor_set(x_227, 3, x_221);
lean_ctor_set(x_227, 4, x_226);
lean_ctor_set(x_227, 5, x_222);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_218);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
else
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; 
lean_dec(x_3);
lean_dec(x_1);
x_229 = lean_ctor_get(x_159, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_229, 4);
lean_inc(x_230);
x_231 = !lean_is_exclusive(x_159);
if (x_231 == 0)
{
lean_object* x_232; uint8_t x_233; 
x_232 = lean_ctor_get(x_159, 1);
lean_dec(x_232);
x_233 = !lean_is_exclusive(x_229);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; uint8_t x_236; 
x_234 = lean_ctor_get(x_229, 4);
lean_dec(x_234);
x_235 = lean_ctor_get(x_229, 1);
lean_dec(x_235);
x_236 = !lean_is_exclusive(x_230);
if (x_236 == 0)
{
lean_ctor_set_uint8(x_230, sizeof(void*)*1, x_156);
lean_ctor_set(x_229, 1, x_155);
return x_159;
}
else
{
lean_object* x_237; lean_object* x_238; 
x_237 = lean_ctor_get(x_230, 0);
lean_inc(x_237);
lean_dec(x_230);
x_238 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set_uint8(x_238, sizeof(void*)*1, x_156);
lean_ctor_set(x_229, 4, x_238);
lean_ctor_set(x_229, 1, x_155);
return x_159;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_239 = lean_ctor_get(x_229, 0);
x_240 = lean_ctor_get(x_229, 2);
x_241 = lean_ctor_get(x_229, 3);
x_242 = lean_ctor_get(x_229, 5);
lean_inc(x_242);
lean_inc(x_241);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_229);
x_243 = lean_ctor_get(x_230, 0);
lean_inc(x_243);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 x_244 = x_230;
} else {
 lean_dec_ref(x_230);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(0, 1, 1);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set_uint8(x_245, sizeof(void*)*1, x_156);
x_246 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_246, 0, x_239);
lean_ctor_set(x_246, 1, x_155);
lean_ctor_set(x_246, 2, x_240);
lean_ctor_set(x_246, 3, x_241);
lean_ctor_set(x_246, 4, x_245);
lean_ctor_set(x_246, 5, x_242);
lean_ctor_set(x_159, 1, x_246);
return x_159;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_247 = lean_ctor_get(x_159, 0);
lean_inc(x_247);
lean_dec(x_159);
x_248 = lean_ctor_get(x_229, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_229, 2);
lean_inc(x_249);
x_250 = lean_ctor_get(x_229, 3);
lean_inc(x_250);
x_251 = lean_ctor_get(x_229, 5);
lean_inc(x_251);
if (lean_is_exclusive(x_229)) {
 lean_ctor_release(x_229, 0);
 lean_ctor_release(x_229, 1);
 lean_ctor_release(x_229, 2);
 lean_ctor_release(x_229, 3);
 lean_ctor_release(x_229, 4);
 lean_ctor_release(x_229, 5);
 x_252 = x_229;
} else {
 lean_dec_ref(x_229);
 x_252 = lean_box(0);
}
x_253 = lean_ctor_get(x_230, 0);
lean_inc(x_253);
if (lean_is_exclusive(x_230)) {
 lean_ctor_release(x_230, 0);
 x_254 = x_230;
} else {
 lean_dec_ref(x_230);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(0, 1, 1);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set_uint8(x_255, sizeof(void*)*1, x_156);
if (lean_is_scalar(x_252)) {
 x_256 = lean_alloc_ctor(0, 6, 0);
} else {
 x_256 = x_252;
}
lean_ctor_set(x_256, 0, x_248);
lean_ctor_set(x_256, 1, x_155);
lean_ctor_set(x_256, 2, x_249);
lean_ctor_set(x_256, 3, x_250);
lean_ctor_set(x_256, 4, x_255);
lean_ctor_set(x_256, 5, x_251);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_247);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
}
}
else
{
lean_object* x_258; uint8_t x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_258 = lean_ctor_get(x_6, 1);
x_259 = lean_ctor_get_uint8(x_153, sizeof(void*)*1);
x_260 = lean_ctor_get(x_153, 0);
lean_inc(x_260);
lean_dec(x_153);
x_261 = 0;
x_262 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set_uint8(x_262, sizeof(void*)*1, x_261);
lean_inc(x_258);
x_263 = l_Lean_MetavarContext_incDepth(x_258);
lean_ctor_set(x_6, 4, x_262);
lean_ctor_set(x_6, 1, x_263);
lean_inc(x_1);
x_264 = l_Lean_Meta_getConstInfo(x_1, x_3, x_6);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
x_267 = l_Lean_ConstantInfo_lparams(x_265);
x_268 = l_List_mapM___main___at_Lean_Meta_mkAppM___spec__1(x_267, x_3, x_266);
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
lean_inc(x_269);
x_271 = l_Lean_mkConst(x_1, x_269);
x_272 = lean_instantiate_type_lparams(x_265, x_269);
lean_dec(x_269);
lean_dec(x_265);
x_273 = lean_unsigned_to_nat(0u);
x_274 = l_Array_empty___closed__1;
x_275 = l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main(x_271, x_2, x_273, x_274, x_273, x_274, x_272, x_3, x_270);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
x_277 = lean_ctor_get(x_276, 4);
lean_inc(x_277);
x_278 = lean_ctor_get(x_275, 0);
lean_inc(x_278);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_279 = x_275;
} else {
 lean_dec_ref(x_275);
 x_279 = lean_box(0);
}
x_280 = lean_ctor_get(x_276, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_276, 2);
lean_inc(x_281);
x_282 = lean_ctor_get(x_276, 3);
lean_inc(x_282);
x_283 = lean_ctor_get(x_276, 5);
lean_inc(x_283);
if (lean_is_exclusive(x_276)) {
 lean_ctor_release(x_276, 0);
 lean_ctor_release(x_276, 1);
 lean_ctor_release(x_276, 2);
 lean_ctor_release(x_276, 3);
 lean_ctor_release(x_276, 4);
 lean_ctor_release(x_276, 5);
 x_284 = x_276;
} else {
 lean_dec_ref(x_276);
 x_284 = lean_box(0);
}
x_285 = lean_ctor_get(x_277, 0);
lean_inc(x_285);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 x_286 = x_277;
} else {
 lean_dec_ref(x_277);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(0, 1, 1);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_285);
lean_ctor_set_uint8(x_287, sizeof(void*)*1, x_259);
if (lean_is_scalar(x_284)) {
 x_288 = lean_alloc_ctor(0, 6, 0);
} else {
 x_288 = x_284;
}
lean_ctor_set(x_288, 0, x_280);
lean_ctor_set(x_288, 1, x_258);
lean_ctor_set(x_288, 2, x_281);
lean_ctor_set(x_288, 3, x_282);
lean_ctor_set(x_288, 4, x_287);
lean_ctor_set(x_288, 5, x_283);
if (lean_is_scalar(x_279)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_279;
}
lean_ctor_set(x_289, 0, x_278);
lean_ctor_set(x_289, 1, x_288);
return x_289;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_290 = lean_ctor_get(x_275, 1);
lean_inc(x_290);
x_291 = lean_ctor_get(x_290, 4);
lean_inc(x_291);
x_292 = lean_ctor_get(x_275, 0);
lean_inc(x_292);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_293 = x_275;
} else {
 lean_dec_ref(x_275);
 x_293 = lean_box(0);
}
x_294 = lean_ctor_get(x_290, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_290, 2);
lean_inc(x_295);
x_296 = lean_ctor_get(x_290, 3);
lean_inc(x_296);
x_297 = lean_ctor_get(x_290, 5);
lean_inc(x_297);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 lean_ctor_release(x_290, 2);
 lean_ctor_release(x_290, 3);
 lean_ctor_release(x_290, 4);
 lean_ctor_release(x_290, 5);
 x_298 = x_290;
} else {
 lean_dec_ref(x_290);
 x_298 = lean_box(0);
}
x_299 = lean_ctor_get(x_291, 0);
lean_inc(x_299);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 x_300 = x_291;
} else {
 lean_dec_ref(x_291);
 x_300 = lean_box(0);
}
if (lean_is_scalar(x_300)) {
 x_301 = lean_alloc_ctor(0, 1, 1);
} else {
 x_301 = x_300;
}
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set_uint8(x_301, sizeof(void*)*1, x_259);
if (lean_is_scalar(x_298)) {
 x_302 = lean_alloc_ctor(0, 6, 0);
} else {
 x_302 = x_298;
}
lean_ctor_set(x_302, 0, x_294);
lean_ctor_set(x_302, 1, x_258);
lean_ctor_set(x_302, 2, x_295);
lean_ctor_set(x_302, 3, x_296);
lean_ctor_set(x_302, 4, x_301);
lean_ctor_set(x_302, 5, x_297);
if (lean_is_scalar(x_293)) {
 x_303 = lean_alloc_ctor(1, 2, 0);
} else {
 x_303 = x_293;
}
lean_ctor_set(x_303, 0, x_292);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; 
lean_dec(x_3);
lean_dec(x_1);
x_304 = lean_ctor_get(x_264, 1);
lean_inc(x_304);
x_305 = lean_ctor_get(x_304, 4);
lean_inc(x_305);
x_306 = lean_ctor_get(x_264, 0);
lean_inc(x_306);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_307 = x_264;
} else {
 lean_dec_ref(x_264);
 x_307 = lean_box(0);
}
x_308 = lean_ctor_get(x_304, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_304, 2);
lean_inc(x_309);
x_310 = lean_ctor_get(x_304, 3);
lean_inc(x_310);
x_311 = lean_ctor_get(x_304, 5);
lean_inc(x_311);
if (lean_is_exclusive(x_304)) {
 lean_ctor_release(x_304, 0);
 lean_ctor_release(x_304, 1);
 lean_ctor_release(x_304, 2);
 lean_ctor_release(x_304, 3);
 lean_ctor_release(x_304, 4);
 lean_ctor_release(x_304, 5);
 x_312 = x_304;
} else {
 lean_dec_ref(x_304);
 x_312 = lean_box(0);
}
x_313 = lean_ctor_get(x_305, 0);
lean_inc(x_313);
if (lean_is_exclusive(x_305)) {
 lean_ctor_release(x_305, 0);
 x_314 = x_305;
} else {
 lean_dec_ref(x_305);
 x_314 = lean_box(0);
}
if (lean_is_scalar(x_314)) {
 x_315 = lean_alloc_ctor(0, 1, 1);
} else {
 x_315 = x_314;
}
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set_uint8(x_315, sizeof(void*)*1, x_259);
if (lean_is_scalar(x_312)) {
 x_316 = lean_alloc_ctor(0, 6, 0);
} else {
 x_316 = x_312;
}
lean_ctor_set(x_316, 0, x_308);
lean_ctor_set(x_316, 1, x_258);
lean_ctor_set(x_316, 2, x_309);
lean_ctor_set(x_316, 3, x_310);
lean_ctor_set(x_316, 4, x_315);
lean_ctor_set(x_316, 5, x_311);
if (lean_is_scalar(x_307)) {
 x_317 = lean_alloc_ctor(1, 2, 0);
} else {
 x_317 = x_307;
}
lean_ctor_set(x_317, 0, x_306);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
}
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; uint8_t x_324; lean_object* x_325; lean_object* x_326; uint8_t x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_318 = lean_ctor_get(x_6, 4);
x_319 = lean_ctor_get(x_6, 0);
x_320 = lean_ctor_get(x_6, 1);
x_321 = lean_ctor_get(x_6, 2);
x_322 = lean_ctor_get(x_6, 3);
x_323 = lean_ctor_get(x_6, 5);
lean_inc(x_323);
lean_inc(x_318);
lean_inc(x_322);
lean_inc(x_321);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_6);
x_324 = lean_ctor_get_uint8(x_318, sizeof(void*)*1);
x_325 = lean_ctor_get(x_318, 0);
lean_inc(x_325);
if (lean_is_exclusive(x_318)) {
 lean_ctor_release(x_318, 0);
 x_326 = x_318;
} else {
 lean_dec_ref(x_318);
 x_326 = lean_box(0);
}
x_327 = 0;
if (lean_is_scalar(x_326)) {
 x_328 = lean_alloc_ctor(0, 1, 1);
} else {
 x_328 = x_326;
}
lean_ctor_set(x_328, 0, x_325);
lean_ctor_set_uint8(x_328, sizeof(void*)*1, x_327);
lean_inc(x_320);
x_329 = l_Lean_MetavarContext_incDepth(x_320);
x_330 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_330, 0, x_319);
lean_ctor_set(x_330, 1, x_329);
lean_ctor_set(x_330, 2, x_321);
lean_ctor_set(x_330, 3, x_322);
lean_ctor_set(x_330, 4, x_328);
lean_ctor_set(x_330, 5, x_323);
lean_inc(x_1);
x_331 = l_Lean_Meta_getConstInfo(x_1, x_3, x_330);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
x_334 = l_Lean_ConstantInfo_lparams(x_332);
x_335 = l_List_mapM___main___at_Lean_Meta_mkAppM___spec__1(x_334, x_3, x_333);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
lean_inc(x_336);
x_338 = l_Lean_mkConst(x_1, x_336);
x_339 = lean_instantiate_type_lparams(x_332, x_336);
lean_dec(x_336);
lean_dec(x_332);
x_340 = lean_unsigned_to_nat(0u);
x_341 = l_Array_empty___closed__1;
x_342 = l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main(x_338, x_2, x_340, x_341, x_340, x_341, x_339, x_3, x_337);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_343 = lean_ctor_get(x_342, 1);
lean_inc(x_343);
x_344 = lean_ctor_get(x_343, 4);
lean_inc(x_344);
x_345 = lean_ctor_get(x_342, 0);
lean_inc(x_345);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_346 = x_342;
} else {
 lean_dec_ref(x_342);
 x_346 = lean_box(0);
}
x_347 = lean_ctor_get(x_343, 0);
lean_inc(x_347);
x_348 = lean_ctor_get(x_343, 2);
lean_inc(x_348);
x_349 = lean_ctor_get(x_343, 3);
lean_inc(x_349);
x_350 = lean_ctor_get(x_343, 5);
lean_inc(x_350);
if (lean_is_exclusive(x_343)) {
 lean_ctor_release(x_343, 0);
 lean_ctor_release(x_343, 1);
 lean_ctor_release(x_343, 2);
 lean_ctor_release(x_343, 3);
 lean_ctor_release(x_343, 4);
 lean_ctor_release(x_343, 5);
 x_351 = x_343;
} else {
 lean_dec_ref(x_343);
 x_351 = lean_box(0);
}
x_352 = lean_ctor_get(x_344, 0);
lean_inc(x_352);
if (lean_is_exclusive(x_344)) {
 lean_ctor_release(x_344, 0);
 x_353 = x_344;
} else {
 lean_dec_ref(x_344);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(0, 1, 1);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_352);
lean_ctor_set_uint8(x_354, sizeof(void*)*1, x_324);
if (lean_is_scalar(x_351)) {
 x_355 = lean_alloc_ctor(0, 6, 0);
} else {
 x_355 = x_351;
}
lean_ctor_set(x_355, 0, x_347);
lean_ctor_set(x_355, 1, x_320);
lean_ctor_set(x_355, 2, x_348);
lean_ctor_set(x_355, 3, x_349);
lean_ctor_set(x_355, 4, x_354);
lean_ctor_set(x_355, 5, x_350);
if (lean_is_scalar(x_346)) {
 x_356 = lean_alloc_ctor(0, 2, 0);
} else {
 x_356 = x_346;
}
lean_ctor_set(x_356, 0, x_345);
lean_ctor_set(x_356, 1, x_355);
return x_356;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_357 = lean_ctor_get(x_342, 1);
lean_inc(x_357);
x_358 = lean_ctor_get(x_357, 4);
lean_inc(x_358);
x_359 = lean_ctor_get(x_342, 0);
lean_inc(x_359);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_360 = x_342;
} else {
 lean_dec_ref(x_342);
 x_360 = lean_box(0);
}
x_361 = lean_ctor_get(x_357, 0);
lean_inc(x_361);
x_362 = lean_ctor_get(x_357, 2);
lean_inc(x_362);
x_363 = lean_ctor_get(x_357, 3);
lean_inc(x_363);
x_364 = lean_ctor_get(x_357, 5);
lean_inc(x_364);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 lean_ctor_release(x_357, 2);
 lean_ctor_release(x_357, 3);
 lean_ctor_release(x_357, 4);
 lean_ctor_release(x_357, 5);
 x_365 = x_357;
} else {
 lean_dec_ref(x_357);
 x_365 = lean_box(0);
}
x_366 = lean_ctor_get(x_358, 0);
lean_inc(x_366);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 x_367 = x_358;
} else {
 lean_dec_ref(x_358);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(0, 1, 1);
} else {
 x_368 = x_367;
}
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set_uint8(x_368, sizeof(void*)*1, x_324);
if (lean_is_scalar(x_365)) {
 x_369 = lean_alloc_ctor(0, 6, 0);
} else {
 x_369 = x_365;
}
lean_ctor_set(x_369, 0, x_361);
lean_ctor_set(x_369, 1, x_320);
lean_ctor_set(x_369, 2, x_362);
lean_ctor_set(x_369, 3, x_363);
lean_ctor_set(x_369, 4, x_368);
lean_ctor_set(x_369, 5, x_364);
if (lean_is_scalar(x_360)) {
 x_370 = lean_alloc_ctor(1, 2, 0);
} else {
 x_370 = x_360;
}
lean_ctor_set(x_370, 0, x_359);
lean_ctor_set(x_370, 1, x_369);
return x_370;
}
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_3);
lean_dec(x_1);
x_371 = lean_ctor_get(x_331, 1);
lean_inc(x_371);
x_372 = lean_ctor_get(x_371, 4);
lean_inc(x_372);
x_373 = lean_ctor_get(x_331, 0);
lean_inc(x_373);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_374 = x_331;
} else {
 lean_dec_ref(x_331);
 x_374 = lean_box(0);
}
x_375 = lean_ctor_get(x_371, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_371, 2);
lean_inc(x_376);
x_377 = lean_ctor_get(x_371, 3);
lean_inc(x_377);
x_378 = lean_ctor_get(x_371, 5);
lean_inc(x_378);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 lean_ctor_release(x_371, 2);
 lean_ctor_release(x_371, 3);
 lean_ctor_release(x_371, 4);
 lean_ctor_release(x_371, 5);
 x_379 = x_371;
} else {
 lean_dec_ref(x_371);
 x_379 = lean_box(0);
}
x_380 = lean_ctor_get(x_372, 0);
lean_inc(x_380);
if (lean_is_exclusive(x_372)) {
 lean_ctor_release(x_372, 0);
 x_381 = x_372;
} else {
 lean_dec_ref(x_372);
 x_381 = lean_box(0);
}
if (lean_is_scalar(x_381)) {
 x_382 = lean_alloc_ctor(0, 1, 1);
} else {
 x_382 = x_381;
}
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set_uint8(x_382, sizeof(void*)*1, x_324);
if (lean_is_scalar(x_379)) {
 x_383 = lean_alloc_ctor(0, 6, 0);
} else {
 x_383 = x_379;
}
lean_ctor_set(x_383, 0, x_375);
lean_ctor_set(x_383, 1, x_320);
lean_ctor_set(x_383, 2, x_376);
lean_ctor_set(x_383, 3, x_377);
lean_ctor_set(x_383, 4, x_382);
lean_ctor_set(x_383, 5, x_378);
if (lean_is_scalar(x_374)) {
 x_384 = lean_alloc_ctor(1, 2, 0);
} else {
 x_384 = x_374;
}
lean_ctor_set(x_384, 0, x_373);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
}
}
}
}
lean_object* l_List_mapM___main___at_Lean_Meta_mkAppM___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapM___main___at_Lean_Meta_mkAppM___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_mkAppM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_mkAppM(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init_Default(lean_object*);
lean_object* initialize_Init_Lean_Meta_SynthInstance(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_AppBuilder(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Default(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_SynthInstance(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_eq_x3f___closed__1 = _init_l_Lean_Expr_eq_x3f___closed__1();
lean_mark_persistent(l_Lean_Expr_eq_x3f___closed__1);
l_Lean_Expr_eq_x3f___closed__2 = _init_l_Lean_Expr_eq_x3f___closed__2();
lean_mark_persistent(l_Lean_Expr_eq_x3f___closed__2);
l_Lean_Expr_heq_x3f___closed__1 = _init_l_Lean_Expr_heq_x3f___closed__1();
lean_mark_persistent(l_Lean_Expr_heq_x3f___closed__1);
l_Lean_Expr_heq_x3f___closed__2 = _init_l_Lean_Expr_heq_x3f___closed__2();
lean_mark_persistent(l_Lean_Expr_heq_x3f___closed__2);
l_Lean_Meta_mkEqRefl___closed__1 = _init_l_Lean_Meta_mkEqRefl___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqRefl___closed__1);
l_Lean_Meta_mkEqRefl___closed__2 = _init_l_Lean_Meta_mkEqRefl___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqRefl___closed__2);
l_Lean_Meta_mkHEqRefl___closed__1 = _init_l_Lean_Meta_mkHEqRefl___closed__1();
lean_mark_persistent(l_Lean_Meta_mkHEqRefl___closed__1);
l_Lean_Meta_mkEqSymm___closed__1 = _init_l_Lean_Meta_mkEqSymm___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqSymm___closed__1);
l_Lean_Meta_mkEqSymm___closed__2 = _init_l_Lean_Meta_mkEqSymm___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqSymm___closed__2);
l_Lean_Meta_mkEqSymm___closed__3 = _init_l_Lean_Meta_mkEqSymm___closed__3();
lean_mark_persistent(l_Lean_Meta_mkEqSymm___closed__3);
l_Lean_Meta_mkEqTrans___closed__1 = _init_l_Lean_Meta_mkEqTrans___closed__1();
lean_mark_persistent(l_Lean_Meta_mkEqTrans___closed__1);
l_Lean_Meta_mkEqTrans___closed__2 = _init_l_Lean_Meta_mkEqTrans___closed__2();
lean_mark_persistent(l_Lean_Meta_mkEqTrans___closed__2);
l_Lean_Meta_mkHEqSymm___closed__1 = _init_l_Lean_Meta_mkHEqSymm___closed__1();
lean_mark_persistent(l_Lean_Meta_mkHEqSymm___closed__1);
l_Lean_Meta_mkHEqSymm___closed__2 = _init_l_Lean_Meta_mkHEqSymm___closed__2();
lean_mark_persistent(l_Lean_Meta_mkHEqSymm___closed__2);
l_Lean_Meta_mkHEqTrans___closed__1 = _init_l_Lean_Meta_mkHEqTrans___closed__1();
lean_mark_persistent(l_Lean_Meta_mkHEqTrans___closed__1);
l_Lean_Meta_mkCongrArg___closed__1 = _init_l_Lean_Meta_mkCongrArg___closed__1();
lean_mark_persistent(l_Lean_Meta_mkCongrArg___closed__1);
l_Lean_Meta_mkCongrArg___closed__2 = _init_l_Lean_Meta_mkCongrArg___closed__2();
lean_mark_persistent(l_Lean_Meta_mkCongrArg___closed__2);
l_Lean_Meta_mkCongrArg___closed__3 = _init_l_Lean_Meta_mkCongrArg___closed__3();
lean_mark_persistent(l_Lean_Meta_mkCongrArg___closed__3);
l_Lean_Meta_mkCongrFun___closed__1 = _init_l_Lean_Meta_mkCongrFun___closed__1();
lean_mark_persistent(l_Lean_Meta_mkCongrFun___closed__1);
l_Lean_Meta_mkCongrFun___closed__2 = _init_l_Lean_Meta_mkCongrFun___closed__2();
lean_mark_persistent(l_Lean_Meta_mkCongrFun___closed__2);
l_Lean_Meta_mkCongrFun___closed__3 = _init_l_Lean_Meta_mkCongrFun___closed__3();
lean_mark_persistent(l_Lean_Meta_mkCongrFun___closed__3);
l_Lean_Meta_mkCongr___closed__1 = _init_l_Lean_Meta_mkCongr___closed__1();
lean_mark_persistent(l_Lean_Meta_mkCongr___closed__1);
l_Lean_Meta_mkCongr___closed__2 = _init_l_Lean_Meta_mkCongr___closed__2();
lean_mark_persistent(l_Lean_Meta_mkCongr___closed__2);
l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__1 = _init_l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__1);
l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__2 = _init_l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__2();
lean_mark_persistent(l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__2);
l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__3 = _init_l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__3();
lean_mark_persistent(l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__3);
l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main___closed__1 = _init_l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main___closed__1);
l_Lean_Meta_mkAppM___closed__1 = _init_l_Lean_Meta_mkAppM___closed__1();
lean_mark_persistent(l_Lean_Meta_mkAppM___closed__1);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
