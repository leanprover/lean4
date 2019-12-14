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
lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Expr_eq_x3f___boxed(lean_object*);
lean_object* l_Lean_Meta_mkHEqSymm___closed__2;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkCongr___closed__1;
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__3;
lean_object* l_Lean_Meta_mkHEqSymm___closed__1;
lean_object* l_Lean_Meta_mkEqSymm___closed__1;
lean_object* l_Lean_Meta_mkEqTrans___closed__3;
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongr___closed__2;
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_FileMap_ofString___closed__1;
lean_object* l_Lean_Meta_mkCongrArg___closed__2;
lean_object* l___private_Init_Lean_Util_Trace_4__checkTraceOption___at_Lean_Meta_isLevelDefEqAux___main___spec__1(lean_object*, lean_object*, lean_object*);
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
extern lean_object* l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_append___main(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Util_Trace_2__getResetTraces___at___private_Init_Lean_Meta_LevelDefEq_9__processPostponedStep___spec__6___rarg(lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Meta_Basic_11__regTraceClasses___closed__2;
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
lean_object* l_Lean_Meta_mkAppM___closed__2;
lean_object* l_Lean_Meta_mkCongrFun___closed__1;
lean_object* l_Lean_mkLambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrFun___closed__2;
lean_object* l_Lean_Meta_mkEqSymm___closed__3;
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Meta_mkEqRefl___closed__1;
lean_object* l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l_Lean_Meta_mkEqRefl___closed__2;
lean_object* l_Lean_Expr_heq_x3f___closed__1;
lean_object* l_Lean_Expr_heq_x3f___boxed(lean_object*);
lean_object* l_Lean_ConstantInfo_lparams(lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_synthInstance(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l___private_Init_Lean_Util_Trace_1__addNode___at___private_Init_Lean_Meta_LevelDefEq_9__processPostponedStep___spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkCongrArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__1;
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
lean_object* l_Lean_Meta_mkHEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqTrans___closed__1;
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_eq_x3f___closed__2;
x_3 = lean_unsigned_to_nat(3u);
x_4 = l_Lean_Expr_isAppOfArity___main(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_6);
x_8 = lean_nat_sub(x_7, x_6);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = l_Lean_Expr_getRevArg_x21___main(x_1, x_10);
x_12 = lean_nat_sub(x_7, x_9);
x_13 = lean_nat_sub(x_12, x_9);
lean_dec(x_12);
x_14 = l_Lean_Expr_getRevArg_x21___main(x_1, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_sub(x_7, x_15);
lean_dec(x_7);
x_17 = lean_nat_sub(x_16, x_9);
lean_dec(x_16);
x_18 = l_Lean_Expr_getRevArg_x21___main(x_1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
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
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Expr_heq_x3f___closed__2;
x_3 = lean_unsigned_to_nat(4u);
x_4 = l_Lean_Expr_isAppOfArity___main(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Expr_getAppNumArgsAux___main(x_1, x_6);
x_8 = lean_nat_sub(x_7, x_6);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_8, x_9);
lean_dec(x_8);
x_11 = l_Lean_Expr_getRevArg_x21___main(x_1, x_10);
x_12 = lean_nat_sub(x_7, x_9);
x_13 = lean_nat_sub(x_12, x_9);
lean_dec(x_12);
x_14 = l_Lean_Expr_getRevArg_x21___main(x_1, x_13);
x_15 = lean_unsigned_to_nat(2u);
x_16 = lean_nat_sub(x_7, x_15);
x_17 = lean_nat_sub(x_16, x_9);
lean_dec(x_16);
x_18 = l_Lean_Expr_getRevArg_x21___main(x_1, x_17);
x_19 = lean_nat_sub(x_7, x_3);
lean_dec(x_7);
x_20 = lean_nat_sub(x_19, x_9);
lean_dec(x_19);
x_21 = l_Lean_Expr_getRevArg_x21___main(x_1, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_14);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_11);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
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
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 1);
x_3 = lean_ctor_get(x_1, 2);
x_4 = l_Lean_Expr_hasLooseBVars(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_inc(x_3);
lean_inc(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
else
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
}
else
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
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
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Meta_mkEqRefl___closed__2;
x_5 = l_Lean_Expr_isAppOf(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_inc(x_2);
lean_inc(x_1);
x_6 = l___private_Init_Lean_Meta_AppBuilder_1__infer(x_1, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_Expr_eq_x3f___closed__2;
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Expr_isAppOfArity___main(x_8, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = l_Lean_FileMap_ofString___closed__1;
x_18 = lean_array_push(x_17, x_1);
x_19 = l_Lean_Meta_mkEqSymm___closed__2;
x_20 = l_Lean_Meta_mkEqSymm___closed__3;
x_21 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_16);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_21);
return x_6;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_6);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Expr_getAppNumArgsAux___main(x_8, x_22);
x_24 = lean_nat_sub(x_23, x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_24, x_25);
lean_dec(x_24);
x_27 = l_Lean_Expr_getRevArg_x21___main(x_8, x_26);
x_28 = lean_nat_sub(x_23, x_25);
x_29 = lean_nat_sub(x_28, x_25);
lean_dec(x_28);
x_30 = l_Lean_Expr_getRevArg_x21___main(x_8, x_29);
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_nat_sub(x_23, x_31);
lean_dec(x_23);
x_33 = lean_nat_sub(x_32, x_25);
lean_dec(x_32);
x_34 = l_Lean_Expr_getRevArg_x21___main(x_8, x_33);
lean_dec(x_8);
lean_inc(x_27);
x_35 = l_Lean_Meta_getLevel(x_27, x_2, x_9);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Meta_mkEqSymm___closed__2;
x_41 = l_Lean_mkConst(x_40, x_39);
x_42 = l_Lean_mkApp4(x_41, x_27, x_30, x_34, x_1);
lean_ctor_set(x_35, 0, x_42);
return x_35;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_ctor_get(x_35, 0);
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_35);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_Meta_mkEqSymm___closed__2;
x_48 = l_Lean_mkConst(x_47, x_46);
x_49 = l_Lean_mkApp4(x_48, x_27, x_30, x_34, x_1);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_44);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_35);
if (x_51 == 0)
{
return x_35;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_35, 0);
x_53 = lean_ctor_get(x_35, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_35);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = lean_ctor_get(x_6, 0);
x_56 = lean_ctor_get(x_6, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_6);
x_57 = l_Lean_Expr_eq_x3f___closed__2;
x_58 = lean_unsigned_to_nat(3u);
x_59 = l_Lean_Expr_isAppOfArity___main(x_55, x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_55);
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_2, 1);
lean_inc(x_62);
lean_dec(x_2);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_62);
x_64 = l_Lean_FileMap_ofString___closed__1;
x_65 = lean_array_push(x_64, x_1);
x_66 = l_Lean_Meta_mkEqSymm___closed__2;
x_67 = l_Lean_Meta_mkEqSymm___closed__3;
x_68 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_65);
lean_ctor_set(x_68, 3, x_63);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_56);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_70 = lean_unsigned_to_nat(0u);
x_71 = l_Lean_Expr_getAppNumArgsAux___main(x_55, x_70);
x_72 = lean_nat_sub(x_71, x_70);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_nat_sub(x_72, x_73);
lean_dec(x_72);
x_75 = l_Lean_Expr_getRevArg_x21___main(x_55, x_74);
x_76 = lean_nat_sub(x_71, x_73);
x_77 = lean_nat_sub(x_76, x_73);
lean_dec(x_76);
x_78 = l_Lean_Expr_getRevArg_x21___main(x_55, x_77);
x_79 = lean_unsigned_to_nat(2u);
x_80 = lean_nat_sub(x_71, x_79);
lean_dec(x_71);
x_81 = lean_nat_sub(x_80, x_73);
lean_dec(x_80);
x_82 = l_Lean_Expr_getRevArg_x21___main(x_55, x_81);
lean_dec(x_55);
lean_inc(x_75);
x_83 = l_Lean_Meta_getLevel(x_75, x_2, x_56);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_87);
x_89 = l_Lean_Meta_mkEqSymm___closed__2;
x_90 = l_Lean_mkConst(x_89, x_88);
x_91 = l_Lean_mkApp4(x_90, x_75, x_78, x_82, x_1);
if (lean_is_scalar(x_86)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_86;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_85);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_82);
lean_dec(x_78);
lean_dec(x_75);
lean_dec(x_1);
x_93 = lean_ctor_get(x_83, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_83, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_95 = x_83;
} else {
 lean_dec_ref(x_83);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_2);
lean_dec(x_1);
x_97 = !lean_is_exclusive(x_6);
if (x_97 == 0)
{
return x_6;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_6, 0);
x_99 = lean_ctor_get(x_6, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_6);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; 
lean_dec(x_2);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_1);
lean_ctor_set(x_101, 1, x_3);
return x_101;
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
lean_object* _init_l_Lean_Meta_mkEqTrans___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_mkEqTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Meta_mkEqRefl___closed__2;
x_6 = l_Lean_Expr_isAppOf(x_1, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_Lean_Expr_isAppOf(x_2, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_inc(x_3);
lean_inc(x_1);
x_8 = l___private_Init_Lean_Meta_AppBuilder_1__infer(x_1, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
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
lean_inc(x_3);
lean_inc(x_2);
x_12 = l___private_Init_Lean_Meta_AppBuilder_1__infer(x_2, x_3, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_57; lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_107; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_104 = l_Lean_Expr_eq_x3f___closed__2;
x_105 = lean_unsigned_to_nat(3u);
x_106 = l_Lean_Expr_isAppOfArity___main(x_9, x_104, x_105);
x_107 = l_Lean_Expr_isAppOfArity___main(x_13, x_104, x_105);
if (x_106 == 0)
{
lean_dec(x_9);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
x_108 = lean_ctor_get(x_14, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_14, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_3, 1);
lean_inc(x_110);
lean_dec(x_3);
x_111 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_109);
lean_ctor_set(x_111, 2, x_110);
x_112 = l_Lean_Meta_mkEqTrans___closed__3;
x_113 = lean_array_push(x_112, x_1);
x_114 = lean_array_push(x_113, x_2);
x_115 = l_Lean_Meta_mkEqTrans___closed__2;
x_116 = l_Lean_Meta_mkEqSymm___closed__3;
x_117 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
lean_ctor_set(x_117, 2, x_114);
lean_ctor_set(x_117, 3, x_111);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_14);
return x_118;
}
else
{
lean_object* x_119; 
x_119 = lean_box(0);
x_57 = x_119;
goto block_103;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_120 = lean_unsigned_to_nat(0u);
x_121 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_120);
x_122 = lean_nat_sub(x_121, x_120);
x_123 = lean_unsigned_to_nat(1u);
x_124 = lean_nat_sub(x_122, x_123);
lean_dec(x_122);
x_125 = l_Lean_Expr_getRevArg_x21___main(x_9, x_124);
x_126 = lean_nat_sub(x_121, x_123);
x_127 = lean_nat_sub(x_126, x_123);
lean_dec(x_126);
x_128 = l_Lean_Expr_getRevArg_x21___main(x_9, x_127);
x_129 = lean_unsigned_to_nat(2u);
x_130 = lean_nat_sub(x_121, x_129);
lean_dec(x_121);
x_131 = lean_nat_sub(x_130, x_123);
lean_dec(x_130);
x_132 = l_Lean_Expr_getRevArg_x21___main(x_9, x_131);
lean_dec(x_9);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_128);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_133);
if (x_107 == 0)
{
lean_object* x_135; 
lean_dec(x_13);
lean_dec(x_11);
x_135 = lean_box(0);
x_16 = x_135;
x_17 = x_134;
goto block_56;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_134);
x_57 = x_136;
goto block_103;
}
}
block_56:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_18);
lean_dec(x_17);
x_19 = lean_ctor_get(x_14, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
x_23 = l_Lean_Meta_mkEqTrans___closed__3;
x_24 = lean_array_push(x_23, x_1);
x_25 = lean_array_push(x_24, x_2);
x_26 = l_Lean_Meta_mkEqTrans___closed__2;
x_27 = l_Lean_Meta_mkEqSymm___closed__3;
x_28 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
lean_ctor_set(x_28, 2, x_25);
lean_ctor_set(x_28, 3, x_22);
if (lean_is_scalar(x_15)) {
 x_29 = lean_alloc_ctor(1, 2, 0);
} else {
 x_29 = x_15;
 lean_ctor_set_tag(x_29, 1);
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_14);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_15);
x_30 = lean_ctor_get(x_16, 0);
lean_inc(x_30);
lean_dec(x_16);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_ctor_get(x_18, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_dec(x_18);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
lean_inc(x_32);
x_36 = l_Lean_Meta_getLevel(x_32, x_3, x_14);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Meta_mkEqTrans___closed__2;
x_42 = l_Lean_mkConst(x_41, x_40);
x_43 = l_Lean_mkApp6(x_42, x_32, x_33, x_34, x_35, x_1, x_2);
lean_ctor_set(x_36, 0, x_43);
return x_36;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_44 = lean_ctor_get(x_36, 0);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_36);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Meta_mkEqTrans___closed__2;
x_49 = l_Lean_mkConst(x_48, x_47);
x_50 = l_Lean_mkApp6(x_49, x_32, x_33, x_34, x_35, x_1, x_2);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
return x_51;
}
}
else
{
uint8_t x_52; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_36);
if (x_52 == 0)
{
return x_36;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_36, 0);
x_54 = lean_ctor_get(x_36, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_36);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
block_103:
{
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_15);
lean_dec(x_13);
x_58 = lean_ctor_get(x_14, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_14, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_3, 1);
lean_inc(x_60);
lean_dec(x_3);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_61, 2, x_60);
x_62 = l_Lean_Meta_mkEqTrans___closed__3;
x_63 = lean_array_push(x_62, x_1);
x_64 = lean_array_push(x_63, x_2);
x_65 = l_Lean_Meta_mkEqTrans___closed__2;
x_66 = l_Lean_Meta_mkEqSymm___closed__3;
x_67 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_67, 2, x_64);
lean_ctor_set(x_67, 3, x_61);
if (lean_is_scalar(x_11)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_11;
 lean_ctor_set_tag(x_68, 1);
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_14);
return x_68;
}
else
{
uint8_t x_69; 
lean_dec(x_11);
x_69 = !lean_is_exclusive(x_57);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_70 = lean_ctor_get(x_57, 0);
x_71 = lean_unsigned_to_nat(0u);
x_72 = l_Lean_Expr_getAppNumArgsAux___main(x_13, x_71);
x_73 = lean_nat_sub(x_72, x_71);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_nat_sub(x_73, x_74);
lean_dec(x_73);
x_76 = l_Lean_Expr_getRevArg_x21___main(x_13, x_75);
x_77 = lean_nat_sub(x_72, x_74);
x_78 = lean_nat_sub(x_77, x_74);
lean_dec(x_77);
x_79 = l_Lean_Expr_getRevArg_x21___main(x_13, x_78);
x_80 = lean_unsigned_to_nat(2u);
x_81 = lean_nat_sub(x_72, x_80);
lean_dec(x_72);
x_82 = lean_nat_sub(x_81, x_74);
lean_dec(x_81);
x_83 = l_Lean_Expr_getRevArg_x21___main(x_13, x_82);
lean_dec(x_13);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_79);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_76);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_57, 0, x_85);
x_16 = x_57;
x_17 = x_70;
goto block_56;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_86 = lean_ctor_get(x_57, 0);
lean_inc(x_86);
lean_dec(x_57);
x_87 = lean_unsigned_to_nat(0u);
x_88 = l_Lean_Expr_getAppNumArgsAux___main(x_13, x_87);
x_89 = lean_nat_sub(x_88, x_87);
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_nat_sub(x_89, x_90);
lean_dec(x_89);
x_92 = l_Lean_Expr_getRevArg_x21___main(x_13, x_91);
x_93 = lean_nat_sub(x_88, x_90);
x_94 = lean_nat_sub(x_93, x_90);
lean_dec(x_93);
x_95 = l_Lean_Expr_getRevArg_x21___main(x_13, x_94);
x_96 = lean_unsigned_to_nat(2u);
x_97 = lean_nat_sub(x_88, x_96);
lean_dec(x_88);
x_98 = lean_nat_sub(x_97, x_90);
lean_dec(x_97);
x_99 = l_Lean_Expr_getRevArg_x21___main(x_13, x_98);
lean_dec(x_13);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_95);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_92);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_16 = x_102;
x_17 = x_86;
goto block_56;
}
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_12);
if (x_137 == 0)
{
return x_12;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_12, 0);
x_139 = lean_ctor_get(x_12, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_12);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = !lean_is_exclusive(x_8);
if (x_141 == 0)
{
return x_8;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_8, 0);
x_143 = lean_ctor_get(x_8, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_8);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
lean_object* x_145; 
lean_dec(x_3);
lean_dec(x_2);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_1);
lean_ctor_set(x_145, 1, x_4);
return x_145;
}
}
else
{
lean_object* x_146; 
lean_dec(x_3);
lean_dec(x_1);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_2);
lean_ctor_set(x_146, 1, x_4);
return x_146;
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
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Meta_mkHEqRefl___closed__1;
x_5 = l_Lean_Expr_isAppOf(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_inc(x_2);
lean_inc(x_1);
x_6 = l___private_Init_Lean_Meta_AppBuilder_1__infer(x_1, x_2, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = l_Lean_Expr_heq_x3f___closed__2;
x_11 = lean_unsigned_to_nat(4u);
x_12 = l_Lean_Expr_isAppOfArity___main(x_8, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_8);
x_13 = lean_ctor_get(x_9, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = l_Lean_FileMap_ofString___closed__1;
x_18 = lean_array_push(x_17, x_1);
x_19 = l_Lean_Meta_mkHEqSymm___closed__1;
x_20 = l_Lean_Meta_mkHEqSymm___closed__2;
x_21 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_16);
lean_ctor_set_tag(x_6, 1);
lean_ctor_set(x_6, 0, x_21);
return x_6;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_free_object(x_6);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Expr_getAppNumArgsAux___main(x_8, x_22);
x_24 = lean_nat_sub(x_23, x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_24, x_25);
lean_dec(x_24);
x_27 = l_Lean_Expr_getRevArg_x21___main(x_8, x_26);
x_28 = lean_nat_sub(x_23, x_25);
x_29 = lean_nat_sub(x_28, x_25);
lean_dec(x_28);
x_30 = l_Lean_Expr_getRevArg_x21___main(x_8, x_29);
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_nat_sub(x_23, x_31);
x_33 = lean_nat_sub(x_32, x_25);
lean_dec(x_32);
x_34 = l_Lean_Expr_getRevArg_x21___main(x_8, x_33);
x_35 = lean_nat_sub(x_23, x_11);
lean_dec(x_23);
x_36 = lean_nat_sub(x_35, x_25);
lean_dec(x_35);
x_37 = l_Lean_Expr_getRevArg_x21___main(x_8, x_36);
lean_dec(x_8);
lean_inc(x_27);
x_38 = l_Lean_Meta_getLevel(x_27, x_2, x_9);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Meta_mkHEqSymm___closed__1;
x_44 = l_Lean_mkConst(x_43, x_42);
x_45 = l_Lean_mkApp5(x_44, x_27, x_34, x_30, x_37, x_1);
lean_ctor_set(x_38, 0, x_45);
return x_38;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_38, 0);
x_47 = lean_ctor_get(x_38, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_38);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Meta_mkHEqSymm___closed__1;
x_51 = l_Lean_mkConst(x_50, x_49);
x_52 = l_Lean_mkApp5(x_51, x_27, x_34, x_30, x_37, x_1);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_38);
if (x_54 == 0)
{
return x_38;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_38, 0);
x_56 = lean_ctor_get(x_38, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_38);
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
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_58 = lean_ctor_get(x_6, 0);
x_59 = lean_ctor_get(x_6, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_6);
x_60 = l_Lean_Expr_heq_x3f___closed__2;
x_61 = lean_unsigned_to_nat(4u);
x_62 = l_Lean_Expr_isAppOfArity___main(x_58, x_60, x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_58);
x_63 = lean_ctor_get(x_59, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 1);
lean_inc(x_65);
lean_dec(x_2);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_66, 2, x_65);
x_67 = l_Lean_FileMap_ofString___closed__1;
x_68 = lean_array_push(x_67, x_1);
x_69 = l_Lean_Meta_mkHEqSymm___closed__1;
x_70 = l_Lean_Meta_mkHEqSymm___closed__2;
x_71 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_68);
lean_ctor_set(x_71, 3, x_66);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_59);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_73 = lean_unsigned_to_nat(0u);
x_74 = l_Lean_Expr_getAppNumArgsAux___main(x_58, x_73);
x_75 = lean_nat_sub(x_74, x_73);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_nat_sub(x_75, x_76);
lean_dec(x_75);
x_78 = l_Lean_Expr_getRevArg_x21___main(x_58, x_77);
x_79 = lean_nat_sub(x_74, x_76);
x_80 = lean_nat_sub(x_79, x_76);
lean_dec(x_79);
x_81 = l_Lean_Expr_getRevArg_x21___main(x_58, x_80);
x_82 = lean_unsigned_to_nat(2u);
x_83 = lean_nat_sub(x_74, x_82);
x_84 = lean_nat_sub(x_83, x_76);
lean_dec(x_83);
x_85 = l_Lean_Expr_getRevArg_x21___main(x_58, x_84);
x_86 = lean_nat_sub(x_74, x_61);
lean_dec(x_74);
x_87 = lean_nat_sub(x_86, x_76);
lean_dec(x_86);
x_88 = l_Lean_Expr_getRevArg_x21___main(x_58, x_87);
lean_dec(x_58);
lean_inc(x_78);
x_89 = l_Lean_Meta_getLevel(x_78, x_2, x_59);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_92 = x_89;
} else {
 lean_dec_ref(x_89);
 x_92 = lean_box(0);
}
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_90);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_Meta_mkHEqSymm___closed__1;
x_96 = l_Lean_mkConst(x_95, x_94);
x_97 = l_Lean_mkApp5(x_96, x_78, x_85, x_81, x_88, x_1);
if (lean_is_scalar(x_92)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_92;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_91);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_88);
lean_dec(x_85);
lean_dec(x_81);
lean_dec(x_78);
lean_dec(x_1);
x_99 = lean_ctor_get(x_89, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_89, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_101 = x_89;
} else {
 lean_dec_ref(x_89);
 x_101 = lean_box(0);
}
if (lean_is_scalar(x_101)) {
 x_102 = lean_alloc_ctor(1, 2, 0);
} else {
 x_102 = x_101;
}
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_2);
lean_dec(x_1);
x_103 = !lean_is_exclusive(x_6);
if (x_103 == 0)
{
return x_6;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_6, 0);
x_105 = lean_ctor_get(x_6, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_6);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
lean_object* x_107; 
lean_dec(x_2);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_1);
lean_ctor_set(x_107, 1, x_3);
return x_107;
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
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Meta_mkHEqRefl___closed__1;
x_6 = l_Lean_Expr_isAppOf(x_1, x_5);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = l_Lean_Expr_isAppOf(x_2, x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_inc(x_3);
lean_inc(x_1);
x_8 = l___private_Init_Lean_Meta_AppBuilder_1__infer(x_1, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
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
lean_inc(x_3);
lean_inc(x_2);
x_12 = l___private_Init_Lean_Meta_AppBuilder_1__infer(x_2, x_3, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_61; lean_object* x_118; lean_object* x_119; uint8_t x_120; uint8_t x_121; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
x_118 = l_Lean_Expr_heq_x3f___closed__2;
x_119 = lean_unsigned_to_nat(4u);
x_120 = l_Lean_Expr_isAppOfArity___main(x_9, x_118, x_119);
x_121 = l_Lean_Expr_isAppOfArity___main(x_13, x_118, x_119);
if (x_120 == 0)
{
lean_dec(x_9);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
x_122 = lean_ctor_get(x_14, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_14, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_3, 1);
lean_inc(x_124);
lean_dec(x_3);
x_125 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
lean_ctor_set(x_125, 2, x_124);
x_126 = l_Lean_Meta_mkEqTrans___closed__3;
x_127 = lean_array_push(x_126, x_1);
x_128 = lean_array_push(x_127, x_2);
x_129 = l_Lean_Meta_mkHEqTrans___closed__1;
x_130 = l_Lean_Meta_mkHEqSymm___closed__2;
x_131 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
lean_ctor_set(x_131, 2, x_128);
lean_ctor_set(x_131, 3, x_125);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_14);
return x_132;
}
else
{
lean_object* x_133; 
x_133 = lean_box(0);
x_61 = x_133;
goto block_117;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_134 = lean_unsigned_to_nat(0u);
x_135 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_134);
x_136 = lean_nat_sub(x_135, x_134);
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_nat_sub(x_136, x_137);
lean_dec(x_136);
x_139 = l_Lean_Expr_getRevArg_x21___main(x_9, x_138);
x_140 = lean_nat_sub(x_135, x_137);
x_141 = lean_nat_sub(x_140, x_137);
lean_dec(x_140);
x_142 = l_Lean_Expr_getRevArg_x21___main(x_9, x_141);
x_143 = lean_unsigned_to_nat(2u);
x_144 = lean_nat_sub(x_135, x_143);
x_145 = lean_nat_sub(x_144, x_137);
lean_dec(x_144);
x_146 = l_Lean_Expr_getRevArg_x21___main(x_9, x_145);
x_147 = lean_nat_sub(x_135, x_119);
lean_dec(x_135);
x_148 = lean_nat_sub(x_147, x_137);
lean_dec(x_147);
x_149 = l_Lean_Expr_getRevArg_x21___main(x_9, x_148);
lean_dec(x_9);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_146);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_142);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_139);
lean_ctor_set(x_152, 1, x_151);
if (x_121 == 0)
{
lean_object* x_153; 
lean_dec(x_13);
lean_dec(x_11);
x_153 = lean_box(0);
x_16 = x_153;
x_17 = x_152;
goto block_60;
}
else
{
lean_object* x_154; 
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_152);
x_61 = x_154;
goto block_117;
}
}
block_60:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
x_24 = l_Lean_Meta_mkEqTrans___closed__3;
x_25 = lean_array_push(x_24, x_1);
x_26 = lean_array_push(x_25, x_2);
x_27 = l_Lean_Meta_mkHEqTrans___closed__1;
x_28 = l_Lean_Meta_mkHEqSymm___closed__2;
x_29 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_23);
if (lean_is_scalar(x_15)) {
 x_30 = lean_alloc_ctor(1, 2, 0);
} else {
 x_30 = x_15;
 lean_ctor_set_tag(x_30, 1);
}
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_14);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_15);
x_31 = lean_ctor_get(x_16, 0);
lean_inc(x_31);
lean_dec(x_16);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_17, 0);
lean_inc(x_34);
lean_dec(x_17);
x_35 = lean_ctor_get(x_18, 0);
lean_inc(x_35);
lean_dec(x_18);
x_36 = lean_ctor_get(x_19, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_19, 1);
lean_inc(x_37);
lean_dec(x_19);
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
lean_inc(x_34);
x_40 = l_Lean_Meta_getLevel(x_34, x_3, x_14);
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
x_45 = l_Lean_Meta_mkHEqTrans___closed__1;
x_46 = l_Lean_mkConst(x_45, x_44);
x_47 = l_Lean_mkApp8(x_46, x_34, x_36, x_38, x_35, x_37, x_39, x_1, x_2);
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
x_52 = l_Lean_Meta_mkHEqTrans___closed__1;
x_53 = l_Lean_mkConst(x_52, x_51);
x_54 = l_Lean_mkApp8(x_53, x_34, x_36, x_38, x_35, x_37, x_39, x_1, x_2);
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
lean_dec(x_35);
lean_dec(x_34);
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
block_117:
{
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_15);
lean_dec(x_13);
x_62 = lean_ctor_get(x_14, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_14, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_3, 1);
lean_inc(x_64);
lean_dec(x_3);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set(x_65, 2, x_64);
x_66 = l_Lean_Meta_mkEqTrans___closed__3;
x_67 = lean_array_push(x_66, x_1);
x_68 = lean_array_push(x_67, x_2);
x_69 = l_Lean_Meta_mkHEqTrans___closed__1;
x_70 = l_Lean_Meta_mkHEqSymm___closed__2;
x_71 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_71, 2, x_68);
lean_ctor_set(x_71, 3, x_65);
if (lean_is_scalar(x_11)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_11;
 lean_ctor_set_tag(x_72, 1);
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_14);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec(x_11);
x_73 = !lean_is_exclusive(x_61);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_74 = lean_ctor_get(x_61, 0);
x_75 = lean_unsigned_to_nat(0u);
x_76 = l_Lean_Expr_getAppNumArgsAux___main(x_13, x_75);
x_77 = lean_nat_sub(x_76, x_75);
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_nat_sub(x_77, x_78);
lean_dec(x_77);
x_80 = l_Lean_Expr_getRevArg_x21___main(x_13, x_79);
x_81 = lean_nat_sub(x_76, x_78);
x_82 = lean_nat_sub(x_81, x_78);
lean_dec(x_81);
x_83 = l_Lean_Expr_getRevArg_x21___main(x_13, x_82);
x_84 = lean_unsigned_to_nat(2u);
x_85 = lean_nat_sub(x_76, x_84);
x_86 = lean_nat_sub(x_85, x_78);
lean_dec(x_85);
x_87 = l_Lean_Expr_getRevArg_x21___main(x_13, x_86);
x_88 = lean_unsigned_to_nat(4u);
x_89 = lean_nat_sub(x_76, x_88);
lean_dec(x_76);
x_90 = lean_nat_sub(x_89, x_78);
lean_dec(x_89);
x_91 = l_Lean_Expr_getRevArg_x21___main(x_13, x_90);
lean_dec(x_13);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_83);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_80);
lean_ctor_set(x_94, 1, x_93);
lean_ctor_set(x_61, 0, x_94);
x_16 = x_61;
x_17 = x_74;
goto block_60;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_95 = lean_ctor_get(x_61, 0);
lean_inc(x_95);
lean_dec(x_61);
x_96 = lean_unsigned_to_nat(0u);
x_97 = l_Lean_Expr_getAppNumArgsAux___main(x_13, x_96);
x_98 = lean_nat_sub(x_97, x_96);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_nat_sub(x_98, x_99);
lean_dec(x_98);
x_101 = l_Lean_Expr_getRevArg_x21___main(x_13, x_100);
x_102 = lean_nat_sub(x_97, x_99);
x_103 = lean_nat_sub(x_102, x_99);
lean_dec(x_102);
x_104 = l_Lean_Expr_getRevArg_x21___main(x_13, x_103);
x_105 = lean_unsigned_to_nat(2u);
x_106 = lean_nat_sub(x_97, x_105);
x_107 = lean_nat_sub(x_106, x_99);
lean_dec(x_106);
x_108 = l_Lean_Expr_getRevArg_x21___main(x_13, x_107);
x_109 = lean_unsigned_to_nat(4u);
x_110 = lean_nat_sub(x_97, x_109);
lean_dec(x_97);
x_111 = lean_nat_sub(x_110, x_99);
lean_dec(x_110);
x_112 = l_Lean_Expr_getRevArg_x21___main(x_13, x_111);
lean_dec(x_13);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_104);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_101);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_16 = x_116;
x_17 = x_95;
goto block_60;
}
}
}
}
else
{
uint8_t x_155; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_155 = !lean_is_exclusive(x_12);
if (x_155 == 0)
{
return x_12;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_12, 0);
x_157 = lean_ctor_get(x_12, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_12);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_8);
if (x_159 == 0)
{
return x_8;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_8, 0);
x_161 = lean_ctor_get(x_8, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_8);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
else
{
lean_object* x_163; 
lean_dec(x_3);
lean_dec(x_2);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_1);
lean_ctor_set(x_163, 1, x_4);
return x_163;
}
}
else
{
lean_object* x_164; 
lean_dec(x_3);
lean_dec(x_1);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_2);
lean_ctor_set(x_164, 1, x_4);
return x_164;
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_62; lean_object* x_77; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
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
x_124 = l_Lean_Expr_eq_x3f___closed__2;
x_125 = lean_unsigned_to_nat(3u);
x_126 = l_Lean_Expr_isAppOfArity___main(x_6, x_124, x_125);
if (lean_obj_tag(x_10) == 7)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = lean_ctor_get(x_10, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_10, 2);
lean_inc(x_128);
lean_dec(x_10);
x_129 = l_Lean_Expr_hasLooseBVars(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
if (x_126 == 0)
{
lean_dec(x_6);
x_62 = x_131;
goto block_76;
}
else
{
lean_dec(x_8);
x_77 = x_131;
goto block_123;
}
}
else
{
lean_object* x_132; 
lean_dec(x_128);
lean_dec(x_127);
x_132 = lean_box(0);
if (x_126 == 0)
{
lean_dec(x_6);
x_62 = x_132;
goto block_76;
}
else
{
lean_dec(x_8);
x_77 = x_132;
goto block_123;
}
}
}
else
{
lean_object* x_133; 
lean_dec(x_10);
x_133 = lean_box(0);
if (x_126 == 0)
{
lean_dec(x_6);
x_62 = x_133;
goto block_76;
}
else
{
lean_dec(x_8);
x_77 = x_133;
goto block_123;
}
}
block_61:
{
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
x_19 = l_Lean_Meta_mkEqTrans___closed__3;
x_20 = lean_array_push(x_19, x_1);
x_21 = lean_array_push(x_20, x_2);
x_22 = l_Lean_Meta_mkCongrArg___closed__2;
x_23 = l_Lean_Meta_mkEqSymm___closed__3;
x_24 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_18);
if (lean_is_scalar(x_12)) {
 x_25 = lean_alloc_ctor(1, 2, 0);
} else {
 x_25 = x_12;
 lean_ctor_set_tag(x_25, 1);
}
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_11);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_12);
x_26 = lean_ctor_get(x_13, 0);
lean_inc(x_26);
lean_dec(x_13);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_dec(x_14);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
lean_dec(x_27);
lean_inc(x_3);
lean_inc(x_28);
x_32 = l_Lean_Meta_getLevel(x_28, x_3, x_11);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_29);
x_35 = l_Lean_Meta_getLevel(x_29, x_3, x_34);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Meta_mkCongrArg___closed__2;
x_42 = l_Lean_mkConst(x_41, x_40);
x_43 = l_Lean_mkApp6(x_42, x_28, x_29, x_30, x_31, x_1, x_2);
lean_ctor_set(x_35, 0, x_43);
return x_35;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_44 = lean_ctor_get(x_35, 0);
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_35);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_33);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Meta_mkCongrArg___closed__2;
x_50 = l_Lean_mkConst(x_49, x_48);
x_51 = l_Lean_mkApp6(x_50, x_28, x_29, x_30, x_31, x_1, x_2);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_45);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_35);
if (x_53 == 0)
{
return x_35;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_35, 0);
x_55 = lean_ctor_get(x_35, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_35);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_32);
if (x_57 == 0)
{
return x_32;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_32, 0);
x_59 = lean_ctor_get(x_32, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_32);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
}
block_76:
{
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_12);
x_63 = lean_ctor_get(x_11, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_11, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_3, 1);
lean_inc(x_65);
lean_dec(x_3);
x_66 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_64);
lean_ctor_set(x_66, 2, x_65);
x_67 = l_Lean_Meta_mkEqTrans___closed__3;
x_68 = lean_array_push(x_67, x_1);
x_69 = lean_array_push(x_68, x_2);
x_70 = l_Lean_Meta_mkCongrArg___closed__2;
x_71 = l_Lean_Meta_mkCongrArg___closed__3;
x_72 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_69);
lean_ctor_set(x_72, 3, x_66);
if (lean_is_scalar(x_8)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_8;
 lean_ctor_set_tag(x_73, 1);
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_11);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_8);
x_74 = lean_ctor_get(x_62, 0);
lean_inc(x_74);
lean_dec(x_62);
x_75 = lean_box(0);
x_13 = x_75;
x_14 = x_74;
goto block_61;
}
}
block_123:
{
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_12);
lean_dec(x_6);
x_78 = lean_ctor_get(x_11, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_11, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_3, 1);
lean_inc(x_80);
lean_dec(x_3);
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
lean_ctor_set(x_81, 2, x_80);
x_82 = l_Lean_Meta_mkEqTrans___closed__3;
x_83 = lean_array_push(x_82, x_1);
x_84 = lean_array_push(x_83, x_2);
x_85 = l_Lean_Meta_mkCongrArg___closed__2;
x_86 = l_Lean_Meta_mkCongrArg___closed__3;
x_87 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_87, 2, x_84);
lean_ctor_set(x_87, 3, x_81);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_11);
return x_88;
}
else
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_77);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_90 = lean_ctor_get(x_77, 0);
x_91 = lean_unsigned_to_nat(0u);
x_92 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_91);
x_93 = lean_nat_sub(x_92, x_91);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_sub(x_93, x_94);
lean_dec(x_93);
x_96 = l_Lean_Expr_getRevArg_x21___main(x_6, x_95);
x_97 = lean_nat_sub(x_92, x_94);
x_98 = lean_nat_sub(x_97, x_94);
lean_dec(x_97);
x_99 = l_Lean_Expr_getRevArg_x21___main(x_6, x_98);
x_100 = lean_unsigned_to_nat(2u);
x_101 = lean_nat_sub(x_92, x_100);
lean_dec(x_92);
x_102 = lean_nat_sub(x_101, x_94);
lean_dec(x_101);
x_103 = l_Lean_Expr_getRevArg_x21___main(x_6, x_102);
lean_dec(x_6);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_96);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_77, 0, x_105);
x_13 = x_77;
x_14 = x_90;
goto block_61;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_106 = lean_ctor_get(x_77, 0);
lean_inc(x_106);
lean_dec(x_77);
x_107 = lean_unsigned_to_nat(0u);
x_108 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_107);
x_109 = lean_nat_sub(x_108, x_107);
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_nat_sub(x_109, x_110);
lean_dec(x_109);
x_112 = l_Lean_Expr_getRevArg_x21___main(x_6, x_111);
x_113 = lean_nat_sub(x_108, x_110);
x_114 = lean_nat_sub(x_113, x_110);
lean_dec(x_113);
x_115 = l_Lean_Expr_getRevArg_x21___main(x_6, x_114);
x_116 = lean_unsigned_to_nat(2u);
x_117 = lean_nat_sub(x_108, x_116);
lean_dec(x_108);
x_118 = lean_nat_sub(x_117, x_110);
lean_dec(x_117);
x_119 = l_Lean_Expr_getRevArg_x21___main(x_6, x_118);
lean_dec(x_6);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_115);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_112);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_121);
x_13 = x_122;
x_14 = x_106;
goto block_61;
}
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_134 = !lean_is_exclusive(x_9);
if (x_134 == 0)
{
return x_9;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_9, 0);
x_136 = lean_ctor_get(x_9, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_9);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
uint8_t x_138; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_138 = !lean_is_exclusive(x_5);
if (x_138 == 0)
{
return x_5;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_5, 0);
x_140 = lean_ctor_get(x_5, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_5);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lean_Expr_eq_x3f___closed__2;
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Expr_isAppOfArity___main(x_7, x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_7);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = l_Lean_Meta_mkEqTrans___closed__3;
x_17 = lean_array_push(x_16, x_1);
x_18 = lean_array_push(x_17, x_2);
x_19 = l_Lean_Meta_mkCongrFun___closed__2;
x_20 = l_Lean_Meta_mkEqSymm___closed__3;
x_21 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_15);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_21);
return x_5;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_5);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Expr_getAppNumArgsAux___main(x_7, x_22);
x_24 = lean_nat_sub(x_23, x_22);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_24, x_25);
lean_dec(x_24);
x_27 = l_Lean_Expr_getRevArg_x21___main(x_7, x_26);
x_28 = lean_nat_sub(x_23, x_25);
x_29 = lean_nat_sub(x_28, x_25);
lean_dec(x_28);
x_30 = l_Lean_Expr_getRevArg_x21___main(x_7, x_29);
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_nat_sub(x_23, x_31);
lean_dec(x_23);
x_33 = lean_nat_sub(x_32, x_25);
lean_dec(x_32);
x_34 = l_Lean_Expr_getRevArg_x21___main(x_7, x_33);
lean_dec(x_7);
lean_inc(x_3);
x_35 = l_Lean_Meta_whnfD(x_27, x_3, x_8);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
if (lean_obj_tag(x_36) == 7)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_38);
x_52 = lean_ctor_get(x_36, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_36, 1);
lean_inc(x_53);
x_54 = lean_ctor_get(x_36, 2);
lean_inc(x_54);
lean_dec(x_36);
x_55 = 0;
lean_inc(x_53);
x_56 = l_Lean_mkLambda(x_52, x_55, x_53, x_54);
lean_inc(x_3);
lean_inc(x_53);
x_57 = l_Lean_Meta_getLevel(x_53, x_3, x_37);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
lean_inc(x_2);
lean_inc(x_56);
x_60 = l_Lean_mkApp(x_56, x_2);
x_61 = l_Lean_Meta_getLevel(x_60, x_3, x_59);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_58);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_Meta_mkCongrFun___closed__2;
x_68 = l_Lean_mkConst(x_67, x_66);
x_69 = l_Lean_mkApp6(x_68, x_53, x_56, x_30, x_34, x_1, x_2);
lean_ctor_set(x_61, 0, x_69);
return x_61;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_70 = lean_ctor_get(x_61, 0);
x_71 = lean_ctor_get(x_61, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_61);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_58);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_Meta_mkCongrFun___closed__2;
x_76 = l_Lean_mkConst(x_75, x_74);
x_77 = l_Lean_mkApp6(x_76, x_53, x_56, x_30, x_34, x_1, x_2);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_71);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec(x_58);
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_61);
if (x_79 == 0)
{
return x_61;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_61, 0);
x_81 = lean_ctor_get(x_61, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_61);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_57);
if (x_83 == 0)
{
return x_57;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_57, 0);
x_85 = lean_ctor_get(x_57, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_57);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; 
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_30);
x_87 = lean_box(0);
x_39 = x_87;
goto block_51;
}
block_51:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_39);
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_3, 1);
lean_inc(x_42);
lean_dec(x_3);
x_43 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_43, 0, x_40);
lean_ctor_set(x_43, 1, x_41);
lean_ctor_set(x_43, 2, x_42);
x_44 = l_Lean_Meta_mkEqTrans___closed__3;
x_45 = lean_array_push(x_44, x_1);
x_46 = lean_array_push(x_45, x_2);
x_47 = l_Lean_Meta_mkCongrFun___closed__2;
x_48 = l_Lean_Meta_mkCongrFun___closed__3;
x_49 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_46);
lean_ctor_set(x_49, 3, x_43);
if (lean_is_scalar(x_38)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_38;
 lean_ctor_set_tag(x_50, 1);
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_37);
return x_50;
}
}
else
{
uint8_t x_88; 
lean_dec(x_34);
lean_dec(x_30);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_35);
if (x_88 == 0)
{
return x_35;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_35, 0);
x_90 = lean_ctor_get(x_35, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_35);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_92 = lean_ctor_get(x_5, 0);
x_93 = lean_ctor_get(x_5, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_5);
x_94 = l_Lean_Expr_eq_x3f___closed__2;
x_95 = lean_unsigned_to_nat(3u);
x_96 = l_Lean_Expr_isAppOfArity___main(x_92, x_94, x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_92);
x_97 = lean_ctor_get(x_93, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_3, 1);
lean_inc(x_99);
lean_dec(x_3);
x_100 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_98);
lean_ctor_set(x_100, 2, x_99);
x_101 = l_Lean_Meta_mkEqTrans___closed__3;
x_102 = lean_array_push(x_101, x_1);
x_103 = lean_array_push(x_102, x_2);
x_104 = l_Lean_Meta_mkCongrFun___closed__2;
x_105 = l_Lean_Meta_mkEqSymm___closed__3;
x_106 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
lean_ctor_set(x_106, 2, x_103);
lean_ctor_set(x_106, 3, x_100);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_93);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_108 = lean_unsigned_to_nat(0u);
x_109 = l_Lean_Expr_getAppNumArgsAux___main(x_92, x_108);
x_110 = lean_nat_sub(x_109, x_108);
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_nat_sub(x_110, x_111);
lean_dec(x_110);
x_113 = l_Lean_Expr_getRevArg_x21___main(x_92, x_112);
x_114 = lean_nat_sub(x_109, x_111);
x_115 = lean_nat_sub(x_114, x_111);
lean_dec(x_114);
x_116 = l_Lean_Expr_getRevArg_x21___main(x_92, x_115);
x_117 = lean_unsigned_to_nat(2u);
x_118 = lean_nat_sub(x_109, x_117);
lean_dec(x_109);
x_119 = lean_nat_sub(x_118, x_111);
lean_dec(x_118);
x_120 = l_Lean_Expr_getRevArg_x21___main(x_92, x_119);
lean_dec(x_92);
lean_inc(x_3);
x_121 = l_Lean_Meta_whnfD(x_113, x_3, x_93);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_124 = x_121;
} else {
 lean_dec_ref(x_121);
 x_124 = lean_box(0);
}
if (lean_obj_tag(x_122) == 7)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_124);
x_138 = lean_ctor_get(x_122, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_122, 1);
lean_inc(x_139);
x_140 = lean_ctor_get(x_122, 2);
lean_inc(x_140);
lean_dec(x_122);
x_141 = 0;
lean_inc(x_139);
x_142 = l_Lean_mkLambda(x_138, x_141, x_139, x_140);
lean_inc(x_3);
lean_inc(x_139);
x_143 = l_Lean_Meta_getLevel(x_139, x_3, x_123);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
lean_inc(x_2);
lean_inc(x_142);
x_146 = l_Lean_mkApp(x_142, x_2);
x_147 = l_Lean_Meta_getLevel(x_146, x_3, x_145);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_151 = lean_box(0);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_148);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_144);
lean_ctor_set(x_153, 1, x_152);
x_154 = l_Lean_Meta_mkCongrFun___closed__2;
x_155 = l_Lean_mkConst(x_154, x_153);
x_156 = l_Lean_mkApp6(x_155, x_139, x_142, x_116, x_120, x_1, x_2);
if (lean_is_scalar(x_150)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_150;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_149);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_144);
lean_dec(x_142);
lean_dec(x_139);
lean_dec(x_120);
lean_dec(x_116);
lean_dec(x_2);
lean_dec(x_1);
x_158 = lean_ctor_get(x_147, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_147, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_160 = x_147;
} else {
 lean_dec_ref(x_147);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_142);
lean_dec(x_139);
lean_dec(x_120);
lean_dec(x_116);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_162 = lean_ctor_get(x_143, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_143, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_164 = x_143;
} else {
 lean_dec_ref(x_143);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
else
{
lean_object* x_166; 
lean_dec(x_122);
lean_dec(x_120);
lean_dec(x_116);
x_166 = lean_box(0);
x_125 = x_166;
goto block_137;
}
block_137:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_125);
x_126 = lean_ctor_get(x_123, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_3, 1);
lean_inc(x_128);
lean_dec(x_3);
x_129 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
lean_ctor_set(x_129, 2, x_128);
x_130 = l_Lean_Meta_mkEqTrans___closed__3;
x_131 = lean_array_push(x_130, x_1);
x_132 = lean_array_push(x_131, x_2);
x_133 = l_Lean_Meta_mkCongrFun___closed__2;
x_134 = l_Lean_Meta_mkCongrFun___closed__3;
x_135 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
lean_ctor_set(x_135, 2, x_132);
lean_ctor_set(x_135, 3, x_129);
if (lean_is_scalar(x_124)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_124;
 lean_ctor_set_tag(x_136, 1);
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_123);
return x_136;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_120);
lean_dec(x_116);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_167 = lean_ctor_get(x_121, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_121, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_169 = x_121;
} else {
 lean_dec_ref(x_121);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_171 = !lean_is_exclusive(x_5);
if (x_171 == 0)
{
return x_5;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_5, 0);
x_173 = lean_ctor_get(x_5, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_5);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_25; lean_object* x_26; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
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
x_92 = l_Lean_Expr_eq_x3f___closed__2;
x_93 = lean_unsigned_to_nat(3u);
x_94 = l_Lean_Expr_isAppOfArity___main(x_6, x_92, x_93);
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_9);
lean_dec(x_6);
x_95 = lean_box(0);
x_12 = x_95;
goto block_24;
}
else
{
uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_96 = l_Lean_Expr_isAppOfArity___main(x_9, x_92, x_93);
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
if (x_96 == 0)
{
lean_object* x_112; 
lean_dec(x_9);
x_112 = lean_box(0);
x_25 = x_112;
x_26 = x_111;
goto block_91;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_113 = l_Lean_Expr_getAppNumArgsAux___main(x_9, x_97);
x_114 = lean_nat_sub(x_113, x_97);
x_115 = lean_nat_sub(x_114, x_100);
lean_dec(x_114);
x_116 = l_Lean_Expr_getRevArg_x21___main(x_9, x_115);
x_117 = lean_nat_sub(x_113, x_100);
x_118 = lean_nat_sub(x_117, x_100);
lean_dec(x_117);
x_119 = l_Lean_Expr_getRevArg_x21___main(x_9, x_118);
x_120 = lean_nat_sub(x_113, x_106);
lean_dec(x_113);
x_121 = lean_nat_sub(x_120, x_100);
lean_dec(x_120);
x_122 = l_Lean_Expr_getRevArg_x21___main(x_9, x_121);
lean_dec(x_9);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_116);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
x_25 = x_125;
x_26 = x_111;
goto block_91;
}
}
block_24:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = l_Lean_Meta_mkEqTrans___closed__3;
x_18 = lean_array_push(x_17, x_1);
x_19 = lean_array_push(x_18, x_2);
x_20 = l_Lean_Meta_mkCongr___closed__2;
x_21 = l_Lean_Meta_mkEqSymm___closed__3;
x_22 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_19);
lean_ctor_set(x_22, 3, x_16);
if (lean_is_scalar(x_11)) {
 x_23 = lean_alloc_ctor(1, 2, 0);
} else {
 x_23 = x_11;
 lean_ctor_set_tag(x_23, 1);
}
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_10);
return x_23;
}
block_91:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_28; 
lean_dec(x_27);
lean_dec(x_26);
x_28 = lean_box(0);
x_12 = x_28;
goto block_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_11);
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_26, 0);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_ctor_get(x_27, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_29, 0);
lean_inc(x_34);
lean_dec(x_29);
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
lean_inc(x_3);
x_37 = l_Lean_Meta_whnfD(x_31, x_3, x_10);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
if (lean_obj_tag(x_38) == 7)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_38, 2);
lean_inc(x_54);
lean_dec(x_38);
x_55 = l_Lean_Expr_hasLooseBVars(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_40);
lean_inc(x_3);
lean_inc(x_34);
x_56 = l_Lean_Meta_getLevel(x_34, x_3, x_39);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_54);
x_59 = l_Lean_Meta_getLevel(x_54, x_3, x_58);
if (lean_obj_tag(x_59) == 0)
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_Meta_mkCongr___closed__2;
x_66 = l_Lean_mkConst(x_65, x_64);
x_67 = l_Lean_mkApp8(x_66, x_34, x_54, x_32, x_33, x_35, x_36, x_1, x_2);
lean_ctor_set(x_59, 0, x_67);
return x_59;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_68 = lean_ctor_get(x_59, 0);
x_69 = lean_ctor_get(x_59, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_59);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_57);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_Meta_mkCongr___closed__2;
x_74 = l_Lean_mkConst(x_73, x_72);
x_75 = l_Lean_mkApp8(x_74, x_34, x_54, x_32, x_33, x_35, x_36, x_1, x_2);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_69);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_57);
lean_dec(x_54);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_59);
if (x_77 == 0)
{
return x_59;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_59, 0);
x_79 = lean_ctor_get(x_59, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_59);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_54);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_56);
if (x_81 == 0)
{
return x_56;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_56, 0);
x_83 = lean_ctor_get(x_56, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_56);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; 
lean_dec(x_54);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
x_85 = lean_box(0);
x_41 = x_85;
goto block_53;
}
}
else
{
lean_object* x_86; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
x_86 = lean_box(0);
x_41 = x_86;
goto block_53;
}
block_53:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_41);
x_42 = lean_ctor_get(x_39, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 1);
lean_inc(x_44);
lean_dec(x_3);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_44);
x_46 = l_Lean_Meta_mkEqTrans___closed__3;
x_47 = lean_array_push(x_46, x_1);
x_48 = lean_array_push(x_47, x_2);
x_49 = l_Lean_Meta_mkCongr___closed__2;
x_50 = l_Lean_Meta_mkCongrArg___closed__3;
x_51 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
lean_ctor_set(x_51, 2, x_48);
lean_ctor_set(x_51, 3, x_45);
if (lean_is_scalar(x_40)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_40;
 lean_ctor_set_tag(x_52, 1);
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_39);
return x_52;
}
}
else
{
uint8_t x_87; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_37);
if (x_87 == 0)
{
return x_37;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_37, 0);
x_89 = lean_ctor_get(x_37, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_37);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
}
else
{
uint8_t x_126; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_8);
if (x_126 == 0)
{
return x_8;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_8, 0);
x_128 = lean_ctor_get(x_8, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_8);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_5);
if (x_130 == 0)
{
return x_5;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_5, 0);
x_132 = lean_ctor_get(x_5, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_5);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
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
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_fget(x_1, x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_2, x_10);
lean_dec(x_2);
lean_inc(x_9);
x_12 = l_Lean_Meta_getMVarDecl(x_9, x_3, x_4);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(10000u);
lean_inc(x_3);
x_17 = l_Lean_Meta_synthInstance(x_15, x_16, x_3, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_assignExprMVar(x_9, x_18, x_3, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_2 = x_11;
x_4 = x_21;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_11);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_20);
if (x_23 == 0)
{
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
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
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_17;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
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
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
return x_12;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_12, 0);
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_12);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_13, 1);
x_22 = lean_ctor_get(x_13, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_4, 1);
lean_inc(x_25);
lean_dec(x_4);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = l_Lean_FileMap_ofString___closed__1;
x_28 = lean_array_push(x_27, x_11);
x_29 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__2;
x_30 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__3;
x_31 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_31, 2, x_28);
lean_ctor_set(x_31, 3, x_26);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_31);
return x_13;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_ctor_get(x_13, 1);
lean_inc(x_32);
lean_dec(x_13);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_35);
lean_dec(x_4);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_35);
x_37 = l_Lean_FileMap_ofString___closed__1;
x_38 = lean_array_push(x_37, x_11);
x_39 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__2;
x_40 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__3;
x_41 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_ctor_set(x_41, 2, x_38);
lean_ctor_set(x_41, 3, x_36);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_32);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_4);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_7);
if (x_43 == 0)
{
return x_7;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_7, 0);
x_45 = lean_ctor_get(x_7, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_7);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
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
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint64_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_107; lean_object* x_108; 
x_57 = lean_ctor_get(x_7, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_7, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_7, 2);
lean_inc(x_59);
x_60 = lean_ctor_get_uint64(x_7, sizeof(void*)*3);
lean_dec(x_7);
x_61 = lean_array_get_size(x_4);
lean_inc(x_4);
x_62 = lean_expr_instantiate_rev_range(x_58, x_5, x_61, x_4);
lean_dec(x_61);
lean_dec(x_58);
x_107 = (uint8_t)((x_60 << 24) >> 61);
x_108 = lean_box(x_107);
switch (lean_obj_tag(x_108)) {
case 1:
{
uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = 0;
lean_inc(x_8);
x_110 = l_Lean_Meta_mkFreshExprMVar(x_62, x_57, x_109, x_8, x_9);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_array_push(x_4, x_111);
x_4 = x_113;
x_7 = x_59;
x_9 = x_112;
goto _start;
}
case 3:
{
uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_115 = 1;
lean_inc(x_8);
x_116 = l_Lean_Meta_mkFreshExprMVar(x_62, x_57, x_115, x_8, x_9);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_117);
x_119 = lean_array_push(x_4, x_117);
x_120 = l_Lean_Expr_mvarId_x21(x_117);
lean_dec(x_117);
x_121 = lean_array_push(x_6, x_120);
x_4 = x_119;
x_6 = x_121;
x_7 = x_59;
x_9 = x_118;
goto _start;
}
default: 
{
lean_object* x_123; 
lean_dec(x_108);
lean_dec(x_57);
x_123 = lean_box(0);
x_63 = x_123;
goto block_106;
}
}
block_106:
{
lean_object* x_64; uint8_t x_65; 
lean_dec(x_63);
x_64 = lean_array_get_size(x_2);
x_65 = lean_nat_dec_lt(x_3, x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_5);
lean_dec(x_3);
x_66 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal(x_1, x_4, x_6, x_8, x_9);
lean_dec(x_6);
lean_dec(x_4);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_array_fget(x_2, x_3);
lean_inc(x_8);
lean_inc(x_67);
x_68 = l_Lean_Meta_inferType(x_67, x_8, x_9);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_8);
x_71 = l_Lean_Meta_isExprDefEq(x_62, x_69, x_8, x_70);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
uint8_t x_74; 
lean_dec(x_59);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_71);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_75 = lean_ctor_get(x_71, 1);
x_76 = lean_ctor_get(x_71, 0);
lean_dec(x_76);
x_77 = lean_ctor_get(x_75, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_75, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_8, 1);
lean_inc(x_79);
lean_dec(x_8);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
lean_ctor_set(x_80, 2, x_79);
x_81 = lean_unsigned_to_nat(0u);
x_82 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_4, x_4, x_81, x_1);
lean_dec(x_4);
x_83 = lean_alloc_ctor(14, 3, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_67);
lean_ctor_set(x_83, 2, x_80);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 0, x_83);
return x_71;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_84 = lean_ctor_get(x_71, 1);
lean_inc(x_84);
lean_dec(x_71);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_8, 1);
lean_inc(x_87);
lean_dec(x_8);
x_88 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
lean_ctor_set(x_88, 2, x_87);
x_89 = lean_unsigned_to_nat(0u);
x_90 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_4, x_4, x_89, x_1);
lean_dec(x_4);
x_91 = lean_alloc_ctor(14, 3, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_67);
lean_ctor_set(x_91, 2, x_88);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_84);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_71, 1);
lean_inc(x_93);
lean_dec(x_71);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_add(x_3, x_94);
lean_dec(x_3);
x_96 = lean_array_push(x_4, x_67);
x_3 = x_95;
x_4 = x_96;
x_7 = x_59;
x_9 = x_93;
goto _start;
}
}
else
{
uint8_t x_98; 
lean_dec(x_67);
lean_dec(x_59);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_71);
if (x_98 == 0)
{
return x_71;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_71, 0);
x_100 = lean_ctor_get(x_71, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_71);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_67);
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_68);
if (x_102 == 0)
{
return x_68;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_68, 0);
x_104 = lean_ctor_get(x_68, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_68);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
}
}
else
{
lean_object* x_124; 
x_124 = lean_box(0);
x_10 = x_124;
goto block_56;
}
block_56:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
x_11 = lean_array_get_size(x_4);
lean_inc(x_4);
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
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = l_Lean_Expr_isForall(x_15);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_11);
x_18 = lean_array_get_size(x_2);
x_19 = lean_nat_dec_eq(x_3, x_18);
lean_dec(x_18);
lean_dec(x_3);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_6);
lean_dec(x_4);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_dec(x_8);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
x_24 = l_Lean_FileMap_ofString___closed__1;
x_25 = lean_array_push(x_24, x_1);
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2, x_2, x_26, x_25);
x_28 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__2;
x_29 = l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main___closed__1;
x_30 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_30, 2, x_27);
lean_ctor_set(x_30, 3, x_23);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_30);
return x_13;
}
else
{
lean_object* x_31; 
lean_free_object(x_13);
x_31 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal(x_1, x_4, x_6, x_8, x_16);
lean_dec(x_6);
lean_dec(x_4);
return x_31;
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
lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = l_Lean_Expr_isForall(x_33);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
lean_dec(x_33);
lean_dec(x_11);
x_36 = lean_array_get_size(x_2);
x_37 = lean_nat_dec_eq(x_3, x_36);
lean_dec(x_36);
lean_dec(x_3);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_6);
lean_dec(x_4);
x_38 = lean_ctor_get(x_34, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_8, 1);
lean_inc(x_40);
lean_dec(x_8);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
lean_ctor_set(x_41, 2, x_40);
x_42 = l_Lean_FileMap_ofString___closed__1;
x_43 = lean_array_push(x_42, x_1);
x_44 = lean_unsigned_to_nat(0u);
x_45 = l_Array_iterateMAux___main___at_Array_append___spec__1___rarg(x_2, x_2, x_44, x_43);
x_46 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal___closed__2;
x_47 = l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main___closed__1;
x_48 = lean_alloc_ctor(16, 4, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
lean_ctor_set(x_48, 2, x_45);
lean_ctor_set(x_48, 3, x_41);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_34);
return x_49;
}
else
{
lean_object* x_50; 
x_50 = l___private_Init_Lean_Meta_AppBuilder_2__mkAppMFinal(x_1, x_4, x_6, x_8, x_34);
lean_dec(x_6);
lean_dec(x_4);
return x_50;
}
}
else
{
x_5 = x_11;
x_7 = x_33;
x_9 = x_34;
goto _start;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_13);
if (x_52 == 0)
{
return x_13;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_13, 0);
x_54 = lean_ctor_get(x_13, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_13);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
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
x_1 = l___private_Init_Lean_Meta_Basic_11__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_Exception_toTraceMessageData___closed__68;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_mkAppM___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_SimpleMonadTracerAdapter_isTracingEnabledFor___rarg___lambda__1___closed__2;
x_2 = l_Lean_Meta_mkAppM___closed__1;
x_3 = l_Lean_Name_append___main(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_mkAppM(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_384; uint8_t x_385; 
x_384 = lean_ctor_get(x_4, 4);
lean_inc(x_384);
x_385 = lean_ctor_get_uint8(x_384, sizeof(void*)*1);
lean_dec(x_384);
if (x_385 == 0)
{
uint8_t x_386; 
x_386 = 0;
x_5 = x_386;
x_6 = x_4;
goto block_383;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; 
x_387 = l_Lean_Meta_mkAppM___closed__2;
x_388 = l___private_Init_Lean_Util_Trace_4__checkTraceOption___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_387, x_3, x_4);
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
x_391 = lean_unbox(x_389);
lean_dec(x_389);
x_5 = x_391;
x_6 = x_390;
goto block_383;
}
block_383:
{
if (x_5 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_6, 4);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_12 = 0;
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_12);
lean_inc(x_10);
x_13 = l_Lean_MetavarContext_incDepth(x_10);
lean_ctor_set(x_6, 1, x_13);
lean_inc(x_1);
x_14 = l_Lean_Meta_getConstInfo(x_1, x_3, x_6);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_ConstantInfo_lparams(x_15);
x_18 = l_List_mapM___main___at_Lean_Meta_mkAppM___spec__1(x_17, x_3, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_19);
x_21 = l_Lean_mkConst(x_1, x_19);
x_22 = lean_instantiate_type_lparams(x_15, x_19);
x_23 = lean_unsigned_to_nat(0u);
x_24 = l_Array_empty___closed__1;
x_25 = l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main(x_21, x_2, x_23, x_24, x_23, x_24, x_22, x_3, x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 4);
lean_inc(x_27);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_25, 1);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_26);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_26, 4);
lean_dec(x_31);
x_32 = lean_ctor_get(x_26, 1);
lean_dec(x_32);
x_33 = !lean_is_exclusive(x_27);
if (x_33 == 0)
{
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_11);
lean_ctor_set(x_26, 1, x_10);
return x_25;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_27, 0);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_11);
lean_ctor_set(x_26, 4, x_35);
lean_ctor_set(x_26, 1, x_10);
return x_25;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_26, 0);
x_37 = lean_ctor_get(x_26, 2);
x_38 = lean_ctor_get(x_26, 3);
x_39 = lean_ctor_get(x_26, 5);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_26);
x_40 = lean_ctor_get(x_27, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_41 = x_27;
} else {
 lean_dec_ref(x_27);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(0, 1, 1);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_11);
x_43 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_10);
lean_ctor_set(x_43, 2, x_37);
lean_ctor_set(x_43, 3, x_38);
lean_ctor_set(x_43, 4, x_42);
lean_ctor_set(x_43, 5, x_39);
lean_ctor_set(x_25, 1, x_43);
return x_25;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_44 = lean_ctor_get(x_25, 0);
lean_inc(x_44);
lean_dec(x_25);
x_45 = lean_ctor_get(x_26, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_26, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_26, 3);
lean_inc(x_47);
x_48 = lean_ctor_get(x_26, 5);
lean_inc(x_48);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 lean_ctor_release(x_26, 2);
 lean_ctor_release(x_26, 3);
 lean_ctor_release(x_26, 4);
 lean_ctor_release(x_26, 5);
 x_49 = x_26;
} else {
 lean_dec_ref(x_26);
 x_49 = lean_box(0);
}
x_50 = lean_ctor_get(x_27, 0);
lean_inc(x_50);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_51 = x_27;
} else {
 lean_dec_ref(x_27);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(0, 1, 1);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_11);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(0, 6, 0);
} else {
 x_53 = x_49;
}
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_53, 1, x_10);
lean_ctor_set(x_53, 2, x_46);
lean_ctor_set(x_53, 3, x_47);
lean_ctor_set(x_53, 4, x_52);
lean_ctor_set(x_53, 5, x_48);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_44);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_55 = lean_ctor_get(x_25, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 4);
lean_inc(x_56);
x_57 = !lean_is_exclusive(x_25);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_25, 1);
lean_dec(x_58);
x_59 = !lean_is_exclusive(x_55);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_55, 4);
lean_dec(x_60);
x_61 = lean_ctor_get(x_55, 1);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_56);
if (x_62 == 0)
{
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_11);
lean_ctor_set(x_55, 1, x_10);
return x_25;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_56, 0);
lean_inc(x_63);
lean_dec(x_56);
x_64 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_11);
lean_ctor_set(x_55, 4, x_64);
lean_ctor_set(x_55, 1, x_10);
return x_25;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_55, 0);
x_66 = lean_ctor_get(x_55, 2);
x_67 = lean_ctor_get(x_55, 3);
x_68 = lean_ctor_get(x_55, 5);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_55);
x_69 = lean_ctor_get(x_56, 0);
lean_inc(x_69);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_70 = x_56;
} else {
 lean_dec_ref(x_56);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(0, 1, 1);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_11);
x_72 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_72, 0, x_65);
lean_ctor_set(x_72, 1, x_10);
lean_ctor_set(x_72, 2, x_66);
lean_ctor_set(x_72, 3, x_67);
lean_ctor_set(x_72, 4, x_71);
lean_ctor_set(x_72, 5, x_68);
lean_ctor_set(x_25, 1, x_72);
return x_25;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_73 = lean_ctor_get(x_25, 0);
lean_inc(x_73);
lean_dec(x_25);
x_74 = lean_ctor_get(x_55, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_55, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_55, 3);
lean_inc(x_76);
x_77 = lean_ctor_get(x_55, 5);
lean_inc(x_77);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 lean_ctor_release(x_55, 2);
 lean_ctor_release(x_55, 3);
 lean_ctor_release(x_55, 4);
 lean_ctor_release(x_55, 5);
 x_78 = x_55;
} else {
 lean_dec_ref(x_55);
 x_78 = lean_box(0);
}
x_79 = lean_ctor_get(x_56, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 x_80 = x_56;
} else {
 lean_dec_ref(x_56);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 1, 1);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set_uint8(x_81, sizeof(void*)*1, x_11);
if (lean_is_scalar(x_78)) {
 x_82 = lean_alloc_ctor(0, 6, 0);
} else {
 x_82 = x_78;
}
lean_ctor_set(x_82, 0, x_74);
lean_ctor_set(x_82, 1, x_10);
lean_ctor_set(x_82, 2, x_75);
lean_ctor_set(x_82, 3, x_76);
lean_ctor_set(x_82, 4, x_81);
lean_ctor_set(x_82, 5, x_77);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_73);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_dec(x_3);
lean_dec(x_1);
x_84 = lean_ctor_get(x_14, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 4);
lean_inc(x_85);
x_86 = !lean_is_exclusive(x_14);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_14, 1);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_84);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_ctor_get(x_84, 4);
lean_dec(x_89);
x_90 = lean_ctor_get(x_84, 1);
lean_dec(x_90);
x_91 = !lean_is_exclusive(x_85);
if (x_91 == 0)
{
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_11);
lean_ctor_set(x_84, 1, x_10);
return x_14;
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_85, 0);
lean_inc(x_92);
lean_dec(x_85);
x_93 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set_uint8(x_93, sizeof(void*)*1, x_11);
lean_ctor_set(x_84, 4, x_93);
lean_ctor_set(x_84, 1, x_10);
return x_14;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_94 = lean_ctor_get(x_84, 0);
x_95 = lean_ctor_get(x_84, 2);
x_96 = lean_ctor_get(x_84, 3);
x_97 = lean_ctor_get(x_84, 5);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_84);
x_98 = lean_ctor_get(x_85, 0);
lean_inc(x_98);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_99 = x_85;
} else {
 lean_dec_ref(x_85);
 x_99 = lean_box(0);
}
if (lean_is_scalar(x_99)) {
 x_100 = lean_alloc_ctor(0, 1, 1);
} else {
 x_100 = x_99;
}
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_11);
x_101 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_101, 0, x_94);
lean_ctor_set(x_101, 1, x_10);
lean_ctor_set(x_101, 2, x_95);
lean_ctor_set(x_101, 3, x_96);
lean_ctor_set(x_101, 4, x_100);
lean_ctor_set(x_101, 5, x_97);
lean_ctor_set(x_14, 1, x_101);
return x_14;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_102 = lean_ctor_get(x_14, 0);
lean_inc(x_102);
lean_dec(x_14);
x_103 = lean_ctor_get(x_84, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_84, 2);
lean_inc(x_104);
x_105 = lean_ctor_get(x_84, 3);
lean_inc(x_105);
x_106 = lean_ctor_get(x_84, 5);
lean_inc(x_106);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 lean_ctor_release(x_84, 2);
 lean_ctor_release(x_84, 3);
 lean_ctor_release(x_84, 4);
 lean_ctor_release(x_84, 5);
 x_107 = x_84;
} else {
 lean_dec_ref(x_84);
 x_107 = lean_box(0);
}
x_108 = lean_ctor_get(x_85, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 x_109 = x_85;
} else {
 lean_dec_ref(x_85);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(0, 1, 1);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_11);
if (lean_is_scalar(x_107)) {
 x_111 = lean_alloc_ctor(0, 6, 0);
} else {
 x_111 = x_107;
}
lean_ctor_set(x_111, 0, x_103);
lean_ctor_set(x_111, 1, x_10);
lean_ctor_set(x_111, 2, x_104);
lean_ctor_set(x_111, 3, x_105);
lean_ctor_set(x_111, 4, x_110);
lean_ctor_set(x_111, 5, x_106);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_102);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; uint8_t x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_113 = lean_ctor_get(x_6, 1);
x_114 = lean_ctor_get_uint8(x_8, sizeof(void*)*1);
x_115 = lean_ctor_get(x_8, 0);
lean_inc(x_115);
lean_dec(x_8);
x_116 = 0;
x_117 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set_uint8(x_117, sizeof(void*)*1, x_116);
lean_inc(x_113);
x_118 = l_Lean_MetavarContext_incDepth(x_113);
lean_ctor_set(x_6, 4, x_117);
lean_ctor_set(x_6, 1, x_118);
lean_inc(x_1);
x_119 = l_Lean_Meta_getConstInfo(x_1, x_3, x_6);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = l_Lean_ConstantInfo_lparams(x_120);
x_123 = l_List_mapM___main___at_Lean_Meta_mkAppM___spec__1(x_122, x_3, x_121);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
lean_inc(x_124);
x_126 = l_Lean_mkConst(x_1, x_124);
x_127 = lean_instantiate_type_lparams(x_120, x_124);
x_128 = lean_unsigned_to_nat(0u);
x_129 = l_Array_empty___closed__1;
x_130 = l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main(x_126, x_2, x_128, x_129, x_128, x_129, x_127, x_3, x_125);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_131 = lean_ctor_get(x_130, 1);
lean_inc(x_131);
x_132 = lean_ctor_get(x_131, 4);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_134 = x_130;
} else {
 lean_dec_ref(x_130);
 x_134 = lean_box(0);
}
x_135 = lean_ctor_get(x_131, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_131, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_131, 3);
lean_inc(x_137);
x_138 = lean_ctor_get(x_131, 5);
lean_inc(x_138);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 lean_ctor_release(x_131, 2);
 lean_ctor_release(x_131, 3);
 lean_ctor_release(x_131, 4);
 lean_ctor_release(x_131, 5);
 x_139 = x_131;
} else {
 lean_dec_ref(x_131);
 x_139 = lean_box(0);
}
x_140 = lean_ctor_get(x_132, 0);
lean_inc(x_140);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 x_141 = x_132;
} else {
 lean_dec_ref(x_132);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(0, 1, 1);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_114);
if (lean_is_scalar(x_139)) {
 x_143 = lean_alloc_ctor(0, 6, 0);
} else {
 x_143 = x_139;
}
lean_ctor_set(x_143, 0, x_135);
lean_ctor_set(x_143, 1, x_113);
lean_ctor_set(x_143, 2, x_136);
lean_ctor_set(x_143, 3, x_137);
lean_ctor_set(x_143, 4, x_142);
lean_ctor_set(x_143, 5, x_138);
if (lean_is_scalar(x_134)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_134;
}
lean_ctor_set(x_144, 0, x_133);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_145 = lean_ctor_get(x_130, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_145, 4);
lean_inc(x_146);
x_147 = lean_ctor_get(x_130, 0);
lean_inc(x_147);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_148 = x_130;
} else {
 lean_dec_ref(x_130);
 x_148 = lean_box(0);
}
x_149 = lean_ctor_get(x_145, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_145, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_145, 3);
lean_inc(x_151);
x_152 = lean_ctor_get(x_145, 5);
lean_inc(x_152);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 lean_ctor_release(x_145, 2);
 lean_ctor_release(x_145, 3);
 lean_ctor_release(x_145, 4);
 lean_ctor_release(x_145, 5);
 x_153 = x_145;
} else {
 lean_dec_ref(x_145);
 x_153 = lean_box(0);
}
x_154 = lean_ctor_get(x_146, 0);
lean_inc(x_154);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 x_155 = x_146;
} else {
 lean_dec_ref(x_146);
 x_155 = lean_box(0);
}
if (lean_is_scalar(x_155)) {
 x_156 = lean_alloc_ctor(0, 1, 1);
} else {
 x_156 = x_155;
}
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set_uint8(x_156, sizeof(void*)*1, x_114);
if (lean_is_scalar(x_153)) {
 x_157 = lean_alloc_ctor(0, 6, 0);
} else {
 x_157 = x_153;
}
lean_ctor_set(x_157, 0, x_149);
lean_ctor_set(x_157, 1, x_113);
lean_ctor_set(x_157, 2, x_150);
lean_ctor_set(x_157, 3, x_151);
lean_ctor_set(x_157, 4, x_156);
lean_ctor_set(x_157, 5, x_152);
if (lean_is_scalar(x_148)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_148;
}
lean_ctor_set(x_158, 0, x_147);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
lean_dec(x_3);
lean_dec(x_1);
x_159 = lean_ctor_get(x_119, 1);
lean_inc(x_159);
x_160 = lean_ctor_get(x_159, 4);
lean_inc(x_160);
x_161 = lean_ctor_get(x_119, 0);
lean_inc(x_161);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_162 = x_119;
} else {
 lean_dec_ref(x_119);
 x_162 = lean_box(0);
}
x_163 = lean_ctor_get(x_159, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_159, 2);
lean_inc(x_164);
x_165 = lean_ctor_get(x_159, 3);
lean_inc(x_165);
x_166 = lean_ctor_get(x_159, 5);
lean_inc(x_166);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 lean_ctor_release(x_159, 2);
 lean_ctor_release(x_159, 3);
 lean_ctor_release(x_159, 4);
 lean_ctor_release(x_159, 5);
 x_167 = x_159;
} else {
 lean_dec_ref(x_159);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_160, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 x_169 = x_160;
} else {
 lean_dec_ref(x_160);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(0, 1, 1);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set_uint8(x_170, sizeof(void*)*1, x_114);
if (lean_is_scalar(x_167)) {
 x_171 = lean_alloc_ctor(0, 6, 0);
} else {
 x_171 = x_167;
}
lean_ctor_set(x_171, 0, x_163);
lean_ctor_set(x_171, 1, x_113);
lean_ctor_set(x_171, 2, x_164);
lean_ctor_set(x_171, 3, x_165);
lean_ctor_set(x_171, 4, x_170);
lean_ctor_set(x_171, 5, x_166);
if (lean_is_scalar(x_162)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_162;
}
lean_ctor_set(x_172, 0, x_161);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_173 = lean_ctor_get(x_6, 4);
x_174 = lean_ctor_get(x_6, 0);
x_175 = lean_ctor_get(x_6, 1);
x_176 = lean_ctor_get(x_6, 2);
x_177 = lean_ctor_get(x_6, 3);
x_178 = lean_ctor_get(x_6, 5);
lean_inc(x_178);
lean_inc(x_173);
lean_inc(x_177);
lean_inc(x_176);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_6);
x_179 = lean_ctor_get_uint8(x_173, sizeof(void*)*1);
x_180 = lean_ctor_get(x_173, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_173)) {
 lean_ctor_release(x_173, 0);
 x_181 = x_173;
} else {
 lean_dec_ref(x_173);
 x_181 = lean_box(0);
}
x_182 = 0;
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(0, 1, 1);
} else {
 x_183 = x_181;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set_uint8(x_183, sizeof(void*)*1, x_182);
lean_inc(x_175);
x_184 = l_Lean_MetavarContext_incDepth(x_175);
x_185 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_185, 0, x_174);
lean_ctor_set(x_185, 1, x_184);
lean_ctor_set(x_185, 2, x_176);
lean_ctor_set(x_185, 3, x_177);
lean_ctor_set(x_185, 4, x_183);
lean_ctor_set(x_185, 5, x_178);
lean_inc(x_1);
x_186 = l_Lean_Meta_getConstInfo(x_1, x_3, x_185);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_186, 1);
lean_inc(x_188);
lean_dec(x_186);
x_189 = l_Lean_ConstantInfo_lparams(x_187);
x_190 = l_List_mapM___main___at_Lean_Meta_mkAppM___spec__1(x_189, x_3, x_188);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
lean_inc(x_191);
x_193 = l_Lean_mkConst(x_1, x_191);
x_194 = lean_instantiate_type_lparams(x_187, x_191);
x_195 = lean_unsigned_to_nat(0u);
x_196 = l_Array_empty___closed__1;
x_197 = l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main(x_193, x_2, x_195, x_196, x_195, x_196, x_194, x_3, x_192);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_198 = lean_ctor_get(x_197, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_198, 4);
lean_inc(x_199);
x_200 = lean_ctor_get(x_197, 0);
lean_inc(x_200);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_201 = x_197;
} else {
 lean_dec_ref(x_197);
 x_201 = lean_box(0);
}
x_202 = lean_ctor_get(x_198, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_198, 2);
lean_inc(x_203);
x_204 = lean_ctor_get(x_198, 3);
lean_inc(x_204);
x_205 = lean_ctor_get(x_198, 5);
lean_inc(x_205);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 lean_ctor_release(x_198, 2);
 lean_ctor_release(x_198, 3);
 lean_ctor_release(x_198, 4);
 lean_ctor_release(x_198, 5);
 x_206 = x_198;
} else {
 lean_dec_ref(x_198);
 x_206 = lean_box(0);
}
x_207 = lean_ctor_get(x_199, 0);
lean_inc(x_207);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 x_208 = x_199;
} else {
 lean_dec_ref(x_199);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(0, 1, 1);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set_uint8(x_209, sizeof(void*)*1, x_179);
if (lean_is_scalar(x_206)) {
 x_210 = lean_alloc_ctor(0, 6, 0);
} else {
 x_210 = x_206;
}
lean_ctor_set(x_210, 0, x_202);
lean_ctor_set(x_210, 1, x_175);
lean_ctor_set(x_210, 2, x_203);
lean_ctor_set(x_210, 3, x_204);
lean_ctor_set(x_210, 4, x_209);
lean_ctor_set(x_210, 5, x_205);
if (lean_is_scalar(x_201)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_201;
}
lean_ctor_set(x_211, 0, x_200);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_212 = lean_ctor_get(x_197, 1);
lean_inc(x_212);
x_213 = lean_ctor_get(x_212, 4);
lean_inc(x_213);
x_214 = lean_ctor_get(x_197, 0);
lean_inc(x_214);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_215 = x_197;
} else {
 lean_dec_ref(x_197);
 x_215 = lean_box(0);
}
x_216 = lean_ctor_get(x_212, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_212, 2);
lean_inc(x_217);
x_218 = lean_ctor_get(x_212, 3);
lean_inc(x_218);
x_219 = lean_ctor_get(x_212, 5);
lean_inc(x_219);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 lean_ctor_release(x_212, 2);
 lean_ctor_release(x_212, 3);
 lean_ctor_release(x_212, 4);
 lean_ctor_release(x_212, 5);
 x_220 = x_212;
} else {
 lean_dec_ref(x_212);
 x_220 = lean_box(0);
}
x_221 = lean_ctor_get(x_213, 0);
lean_inc(x_221);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 x_222 = x_213;
} else {
 lean_dec_ref(x_213);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(0, 1, 1);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set_uint8(x_223, sizeof(void*)*1, x_179);
if (lean_is_scalar(x_220)) {
 x_224 = lean_alloc_ctor(0, 6, 0);
} else {
 x_224 = x_220;
}
lean_ctor_set(x_224, 0, x_216);
lean_ctor_set(x_224, 1, x_175);
lean_ctor_set(x_224, 2, x_217);
lean_ctor_set(x_224, 3, x_218);
lean_ctor_set(x_224, 4, x_223);
lean_ctor_set(x_224, 5, x_219);
if (lean_is_scalar(x_215)) {
 x_225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_225 = x_215;
}
lean_ctor_set(x_225, 0, x_214);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; 
lean_dec(x_3);
lean_dec(x_1);
x_226 = lean_ctor_get(x_186, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_226, 4);
lean_inc(x_227);
x_228 = lean_ctor_get(x_186, 0);
lean_inc(x_228);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_229 = x_186;
} else {
 lean_dec_ref(x_186);
 x_229 = lean_box(0);
}
x_230 = lean_ctor_get(x_226, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_226, 2);
lean_inc(x_231);
x_232 = lean_ctor_get(x_226, 3);
lean_inc(x_232);
x_233 = lean_ctor_get(x_226, 5);
lean_inc(x_233);
if (lean_is_exclusive(x_226)) {
 lean_ctor_release(x_226, 0);
 lean_ctor_release(x_226, 1);
 lean_ctor_release(x_226, 2);
 lean_ctor_release(x_226, 3);
 lean_ctor_release(x_226, 4);
 lean_ctor_release(x_226, 5);
 x_234 = x_226;
} else {
 lean_dec_ref(x_226);
 x_234 = lean_box(0);
}
x_235 = lean_ctor_get(x_227, 0);
lean_inc(x_235);
if (lean_is_exclusive(x_227)) {
 lean_ctor_release(x_227, 0);
 x_236 = x_227;
} else {
 lean_dec_ref(x_227);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(0, 1, 1);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set_uint8(x_237, sizeof(void*)*1, x_179);
if (lean_is_scalar(x_234)) {
 x_238 = lean_alloc_ctor(0, 6, 0);
} else {
 x_238 = x_234;
}
lean_ctor_set(x_238, 0, x_230);
lean_ctor_set(x_238, 1, x_175);
lean_ctor_set(x_238, 2, x_231);
lean_ctor_set(x_238, 3, x_232);
lean_ctor_set(x_238, 4, x_237);
lean_ctor_set(x_238, 5, x_233);
if (lean_is_scalar(x_229)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_229;
}
lean_ctor_set(x_239, 0, x_228);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_240 = l___private_Init_Lean_Util_Trace_2__getResetTraces___at___private_Init_Lean_Meta_LevelDefEq_9__processPostponedStep___spec__6___rarg(x_6);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 0);
lean_inc(x_242);
lean_dec(x_240);
x_243 = !lean_is_exclusive(x_241);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_241, 1);
lean_inc(x_244);
x_245 = l_Lean_MetavarContext_incDepth(x_244);
lean_ctor_set(x_241, 1, x_245);
lean_inc(x_1);
x_246 = l_Lean_Meta_getConstInfo(x_1, x_3, x_241);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = l_Lean_ConstantInfo_lparams(x_247);
x_250 = l_List_mapM___main___at_Lean_Meta_mkAppM___spec__1(x_249, x_3, x_248);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
lean_dec(x_250);
lean_inc(x_251);
x_253 = l_Lean_mkConst(x_1, x_251);
x_254 = lean_instantiate_type_lparams(x_247, x_251);
x_255 = lean_unsigned_to_nat(0u);
x_256 = l_Array_empty___closed__1;
lean_inc(x_3);
x_257 = l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main(x_253, x_2, x_255, x_256, x_255, x_256, x_254, x_3, x_252);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
x_259 = lean_ctor_get(x_257, 0);
lean_inc(x_259);
lean_dec(x_257);
x_260 = !lean_is_exclusive(x_258);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; 
x_261 = lean_ctor_get(x_258, 1);
lean_dec(x_261);
lean_ctor_set(x_258, 1, x_244);
x_262 = l_Lean_Meta_mkAppM___closed__1;
x_263 = l___private_Init_Lean_Util_Trace_1__addNode___at___private_Init_Lean_Meta_LevelDefEq_9__processPostponedStep___spec__7(x_242, x_262, x_3, x_258);
lean_dec(x_3);
x_264 = !lean_is_exclusive(x_263);
if (x_264 == 0)
{
lean_object* x_265; 
x_265 = lean_ctor_get(x_263, 0);
lean_dec(x_265);
lean_ctor_set(x_263, 0, x_259);
return x_263;
}
else
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_263, 1);
lean_inc(x_266);
lean_dec(x_263);
x_267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_267, 0, x_259);
lean_ctor_set(x_267, 1, x_266);
return x_267;
}
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_268 = lean_ctor_get(x_258, 0);
x_269 = lean_ctor_get(x_258, 2);
x_270 = lean_ctor_get(x_258, 3);
x_271 = lean_ctor_get(x_258, 4);
x_272 = lean_ctor_get(x_258, 5);
lean_inc(x_272);
lean_inc(x_271);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_258);
x_273 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_273, 0, x_268);
lean_ctor_set(x_273, 1, x_244);
lean_ctor_set(x_273, 2, x_269);
lean_ctor_set(x_273, 3, x_270);
lean_ctor_set(x_273, 4, x_271);
lean_ctor_set(x_273, 5, x_272);
x_274 = l_Lean_Meta_mkAppM___closed__1;
x_275 = l___private_Init_Lean_Util_Trace_1__addNode___at___private_Init_Lean_Meta_LevelDefEq_9__processPostponedStep___spec__7(x_242, x_274, x_3, x_273);
lean_dec(x_3);
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_277 = x_275;
} else {
 lean_dec_ref(x_275);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(0, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_259);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; uint8_t x_281; 
x_279 = lean_ctor_get(x_257, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_257, 0);
lean_inc(x_280);
lean_dec(x_257);
x_281 = !lean_is_exclusive(x_279);
if (x_281 == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; uint8_t x_285; 
x_282 = lean_ctor_get(x_279, 1);
lean_dec(x_282);
lean_ctor_set(x_279, 1, x_244);
x_283 = l_Lean_Meta_mkAppM___closed__1;
x_284 = l___private_Init_Lean_Util_Trace_1__addNode___at___private_Init_Lean_Meta_LevelDefEq_9__processPostponedStep___spec__7(x_242, x_283, x_3, x_279);
lean_dec(x_3);
x_285 = !lean_is_exclusive(x_284);
if (x_285 == 0)
{
lean_object* x_286; 
x_286 = lean_ctor_get(x_284, 0);
lean_dec(x_286);
lean_ctor_set_tag(x_284, 1);
lean_ctor_set(x_284, 0, x_280);
return x_284;
}
else
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_284, 1);
lean_inc(x_287);
lean_dec(x_284);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_280);
lean_ctor_set(x_288, 1, x_287);
return x_288;
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_289 = lean_ctor_get(x_279, 0);
x_290 = lean_ctor_get(x_279, 2);
x_291 = lean_ctor_get(x_279, 3);
x_292 = lean_ctor_get(x_279, 4);
x_293 = lean_ctor_get(x_279, 5);
lean_inc(x_293);
lean_inc(x_292);
lean_inc(x_291);
lean_inc(x_290);
lean_inc(x_289);
lean_dec(x_279);
x_294 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_294, 0, x_289);
lean_ctor_set(x_294, 1, x_244);
lean_ctor_set(x_294, 2, x_290);
lean_ctor_set(x_294, 3, x_291);
lean_ctor_set(x_294, 4, x_292);
lean_ctor_set(x_294, 5, x_293);
x_295 = l_Lean_Meta_mkAppM___closed__1;
x_296 = l___private_Init_Lean_Util_Trace_1__addNode___at___private_Init_Lean_Meta_LevelDefEq_9__processPostponedStep___spec__7(x_242, x_295, x_3, x_294);
lean_dec(x_3);
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
if (lean_is_exclusive(x_296)) {
 lean_ctor_release(x_296, 0);
 lean_ctor_release(x_296, 1);
 x_298 = x_296;
} else {
 lean_dec_ref(x_296);
 x_298 = lean_box(0);
}
if (lean_is_scalar(x_298)) {
 x_299 = lean_alloc_ctor(1, 2, 0);
} else {
 x_299 = x_298;
 lean_ctor_set_tag(x_299, 1);
}
lean_ctor_set(x_299, 0, x_280);
lean_ctor_set(x_299, 1, x_297);
return x_299;
}
}
}
else
{
lean_object* x_300; lean_object* x_301; uint8_t x_302; 
lean_dec(x_1);
x_300 = lean_ctor_get(x_246, 1);
lean_inc(x_300);
x_301 = lean_ctor_get(x_246, 0);
lean_inc(x_301);
lean_dec(x_246);
x_302 = !lean_is_exclusive(x_300);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_303 = lean_ctor_get(x_300, 1);
lean_dec(x_303);
lean_ctor_set(x_300, 1, x_244);
x_304 = l_Lean_Meta_mkAppM___closed__1;
x_305 = l___private_Init_Lean_Util_Trace_1__addNode___at___private_Init_Lean_Meta_LevelDefEq_9__processPostponedStep___spec__7(x_242, x_304, x_3, x_300);
lean_dec(x_3);
x_306 = !lean_is_exclusive(x_305);
if (x_306 == 0)
{
lean_object* x_307; 
x_307 = lean_ctor_get(x_305, 0);
lean_dec(x_307);
lean_ctor_set_tag(x_305, 1);
lean_ctor_set(x_305, 0, x_301);
return x_305;
}
else
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_ctor_get(x_305, 1);
lean_inc(x_308);
lean_dec(x_305);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_301);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_310 = lean_ctor_get(x_300, 0);
x_311 = lean_ctor_get(x_300, 2);
x_312 = lean_ctor_get(x_300, 3);
x_313 = lean_ctor_get(x_300, 4);
x_314 = lean_ctor_get(x_300, 5);
lean_inc(x_314);
lean_inc(x_313);
lean_inc(x_312);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_300);
x_315 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_315, 0, x_310);
lean_ctor_set(x_315, 1, x_244);
lean_ctor_set(x_315, 2, x_311);
lean_ctor_set(x_315, 3, x_312);
lean_ctor_set(x_315, 4, x_313);
lean_ctor_set(x_315, 5, x_314);
x_316 = l_Lean_Meta_mkAppM___closed__1;
x_317 = l___private_Init_Lean_Util_Trace_1__addNode___at___private_Init_Lean_Meta_LevelDefEq_9__processPostponedStep___spec__7(x_242, x_316, x_3, x_315);
lean_dec(x_3);
x_318 = lean_ctor_get(x_317, 1);
lean_inc(x_318);
if (lean_is_exclusive(x_317)) {
 lean_ctor_release(x_317, 0);
 lean_ctor_release(x_317, 1);
 x_319 = x_317;
} else {
 lean_dec_ref(x_317);
 x_319 = lean_box(0);
}
if (lean_is_scalar(x_319)) {
 x_320 = lean_alloc_ctor(1, 2, 0);
} else {
 x_320 = x_319;
 lean_ctor_set_tag(x_320, 1);
}
lean_ctor_set(x_320, 0, x_301);
lean_ctor_set(x_320, 1, x_318);
return x_320;
}
}
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_321 = lean_ctor_get(x_241, 0);
x_322 = lean_ctor_get(x_241, 1);
x_323 = lean_ctor_get(x_241, 2);
x_324 = lean_ctor_get(x_241, 3);
x_325 = lean_ctor_get(x_241, 4);
x_326 = lean_ctor_get(x_241, 5);
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_241);
lean_inc(x_322);
x_327 = l_Lean_MetavarContext_incDepth(x_322);
x_328 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_328, 0, x_321);
lean_ctor_set(x_328, 1, x_327);
lean_ctor_set(x_328, 2, x_323);
lean_ctor_set(x_328, 3, x_324);
lean_ctor_set(x_328, 4, x_325);
lean_ctor_set(x_328, 5, x_326);
lean_inc(x_1);
x_329 = l_Lean_Meta_getConstInfo(x_1, x_3, x_328);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
lean_dec(x_329);
x_332 = l_Lean_ConstantInfo_lparams(x_330);
x_333 = l_List_mapM___main___at_Lean_Meta_mkAppM___spec__1(x_332, x_3, x_331);
x_334 = lean_ctor_get(x_333, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_333, 1);
lean_inc(x_335);
lean_dec(x_333);
lean_inc(x_334);
x_336 = l_Lean_mkConst(x_1, x_334);
x_337 = lean_instantiate_type_lparams(x_330, x_334);
x_338 = lean_unsigned_to_nat(0u);
x_339 = l_Array_empty___closed__1;
lean_inc(x_3);
x_340 = l___private_Init_Lean_Meta_AppBuilder_3__mkAppMAux___main(x_336, x_2, x_338, x_339, x_338, x_339, x_337, x_3, x_335);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_341 = lean_ctor_get(x_340, 1);
lean_inc(x_341);
x_342 = lean_ctor_get(x_340, 0);
lean_inc(x_342);
lean_dec(x_340);
x_343 = lean_ctor_get(x_341, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_341, 2);
lean_inc(x_344);
x_345 = lean_ctor_get(x_341, 3);
lean_inc(x_345);
x_346 = lean_ctor_get(x_341, 4);
lean_inc(x_346);
x_347 = lean_ctor_get(x_341, 5);
lean_inc(x_347);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 lean_ctor_release(x_341, 2);
 lean_ctor_release(x_341, 3);
 lean_ctor_release(x_341, 4);
 lean_ctor_release(x_341, 5);
 x_348 = x_341;
} else {
 lean_dec_ref(x_341);
 x_348 = lean_box(0);
}
if (lean_is_scalar(x_348)) {
 x_349 = lean_alloc_ctor(0, 6, 0);
} else {
 x_349 = x_348;
}
lean_ctor_set(x_349, 0, x_343);
lean_ctor_set(x_349, 1, x_322);
lean_ctor_set(x_349, 2, x_344);
lean_ctor_set(x_349, 3, x_345);
lean_ctor_set(x_349, 4, x_346);
lean_ctor_set(x_349, 5, x_347);
x_350 = l_Lean_Meta_mkAppM___closed__1;
x_351 = l___private_Init_Lean_Util_Trace_1__addNode___at___private_Init_Lean_Meta_LevelDefEq_9__processPostponedStep___spec__7(x_242, x_350, x_3, x_349);
lean_dec(x_3);
x_352 = lean_ctor_get(x_351, 1);
lean_inc(x_352);
if (lean_is_exclusive(x_351)) {
 lean_ctor_release(x_351, 0);
 lean_ctor_release(x_351, 1);
 x_353 = x_351;
} else {
 lean_dec_ref(x_351);
 x_353 = lean_box(0);
}
if (lean_is_scalar(x_353)) {
 x_354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_354 = x_353;
}
lean_ctor_set(x_354, 0, x_342);
lean_ctor_set(x_354, 1, x_352);
return x_354;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_355 = lean_ctor_get(x_340, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_340, 0);
lean_inc(x_356);
lean_dec(x_340);
x_357 = lean_ctor_get(x_355, 0);
lean_inc(x_357);
x_358 = lean_ctor_get(x_355, 2);
lean_inc(x_358);
x_359 = lean_ctor_get(x_355, 3);
lean_inc(x_359);
x_360 = lean_ctor_get(x_355, 4);
lean_inc(x_360);
x_361 = lean_ctor_get(x_355, 5);
lean_inc(x_361);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 lean_ctor_release(x_355, 2);
 lean_ctor_release(x_355, 3);
 lean_ctor_release(x_355, 4);
 lean_ctor_release(x_355, 5);
 x_362 = x_355;
} else {
 lean_dec_ref(x_355);
 x_362 = lean_box(0);
}
if (lean_is_scalar(x_362)) {
 x_363 = lean_alloc_ctor(0, 6, 0);
} else {
 x_363 = x_362;
}
lean_ctor_set(x_363, 0, x_357);
lean_ctor_set(x_363, 1, x_322);
lean_ctor_set(x_363, 2, x_358);
lean_ctor_set(x_363, 3, x_359);
lean_ctor_set(x_363, 4, x_360);
lean_ctor_set(x_363, 5, x_361);
x_364 = l_Lean_Meta_mkAppM___closed__1;
x_365 = l___private_Init_Lean_Util_Trace_1__addNode___at___private_Init_Lean_Meta_LevelDefEq_9__processPostponedStep___spec__7(x_242, x_364, x_3, x_363);
lean_dec(x_3);
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_367 = x_365;
} else {
 lean_dec_ref(x_365);
 x_367 = lean_box(0);
}
if (lean_is_scalar(x_367)) {
 x_368 = lean_alloc_ctor(1, 2, 0);
} else {
 x_368 = x_367;
 lean_ctor_set_tag(x_368, 1);
}
lean_ctor_set(x_368, 0, x_356);
lean_ctor_set(x_368, 1, x_366);
return x_368;
}
}
else
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_dec(x_1);
x_369 = lean_ctor_get(x_329, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_329, 0);
lean_inc(x_370);
lean_dec(x_329);
x_371 = lean_ctor_get(x_369, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_369, 2);
lean_inc(x_372);
x_373 = lean_ctor_get(x_369, 3);
lean_inc(x_373);
x_374 = lean_ctor_get(x_369, 4);
lean_inc(x_374);
x_375 = lean_ctor_get(x_369, 5);
lean_inc(x_375);
if (lean_is_exclusive(x_369)) {
 lean_ctor_release(x_369, 0);
 lean_ctor_release(x_369, 1);
 lean_ctor_release(x_369, 2);
 lean_ctor_release(x_369, 3);
 lean_ctor_release(x_369, 4);
 lean_ctor_release(x_369, 5);
 x_376 = x_369;
} else {
 lean_dec_ref(x_369);
 x_376 = lean_box(0);
}
if (lean_is_scalar(x_376)) {
 x_377 = lean_alloc_ctor(0, 6, 0);
} else {
 x_377 = x_376;
}
lean_ctor_set(x_377, 0, x_371);
lean_ctor_set(x_377, 1, x_322);
lean_ctor_set(x_377, 2, x_372);
lean_ctor_set(x_377, 3, x_373);
lean_ctor_set(x_377, 4, x_374);
lean_ctor_set(x_377, 5, x_375);
x_378 = l_Lean_Meta_mkAppM___closed__1;
x_379 = l___private_Init_Lean_Util_Trace_1__addNode___at___private_Init_Lean_Meta_LevelDefEq_9__processPostponedStep___spec__7(x_242, x_378, x_3, x_377);
lean_dec(x_3);
x_380 = lean_ctor_get(x_379, 1);
lean_inc(x_380);
if (lean_is_exclusive(x_379)) {
 lean_ctor_release(x_379, 0);
 lean_ctor_release(x_379, 1);
 x_381 = x_379;
} else {
 lean_dec_ref(x_379);
 x_381 = lean_box(0);
}
if (lean_is_scalar(x_381)) {
 x_382 = lean_alloc_ctor(1, 2, 0);
} else {
 x_382 = x_381;
 lean_ctor_set_tag(x_382, 1);
}
lean_ctor_set(x_382, 0, x_370);
lean_ctor_set(x_382, 1, x_380);
return x_382;
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
l_Lean_Meta_mkEqTrans___closed__3 = _init_l_Lean_Meta_mkEqTrans___closed__3();
lean_mark_persistent(l_Lean_Meta_mkEqTrans___closed__3);
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
l_Lean_Meta_mkAppM___closed__2 = _init_l_Lean_Meta_mkAppM___closed__2();
lean_mark_persistent(l_Lean_Meta_mkAppM___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
