// Lean compiler output
// Module: Lean.Meta.Match.CaseArraySizes
// Imports: Init Lean.Meta.Tactic.Assert Lean.Meta.Match.CaseValues
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
lean_object* l_Lean_Meta_CaseArraySizesSubgoal_subst___default;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_caseArraySizes___closed__2;
lean_object* l_Lean_Meta_mkDecideProof___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkAppM___rarg___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM___at_Lean_Meta_mkDecideProof___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseArraySizes___closed__3;
lean_object* l_Array_umapMAux___main___at_Lean_Meta_caseArraySizes___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar___at_Lean_Meta_admit___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CaseArraySizesSubgoal_diseqs___default;
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_Array_hasQuote___rarg___closed__2;
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkAppM___rarg___closed__2;
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_20__mkFun___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseArraySizes_match__6___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_CaseArraySizesSubgoal_elems___default;
extern lean_object* l_Lean_Literal_type___closed__3;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Name_inhabited;
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__2;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1;
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_caseArraySizes___spec__3___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__2;
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkDecideProof___rarg___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3;
lean_object* l_Lean_Meta_mkLt___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseArraySizes_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseArraySizes_match__5___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getArrayArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_caseValue___closed__2;
lean_object* l___private_Lean_Meta_AppBuilder_2__mkExpectedTypeHint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getArrayArgType___closed__1;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__5;
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_appendIndexAfter(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getArrayArgType___closed__2;
lean_object* l_Lean_Meta_mkAppM___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_inferType___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD___at___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_mkLt___rarg___closed__4;
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Meta_substCore___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseArraySizes_match__2___rarg(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_match__1(lean_object*);
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_141____closed__4;
extern lean_object* l_Lean_boolToExpr___lambda__1___closed__6;
lean_object* l_Lean_Meta_CaseArraySizesSubgoal_inhabited;
lean_object* l_Lean_Meta_mkForallFVars___at_Lean_Meta_assertAfter___spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getArrayArgType___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2;
lean_object* l_Lean_Meta_assertExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_caseArraySizes___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseArraySizes_match__6(lean_object*);
extern lean_object* l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__24;
lean_object* l_Lean_mkApp(lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseArraySizes_match__2(lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_caseArraySizes___spec__2(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
extern lean_object* l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
lean_object* l_Lean_Meta_mkArrayLit___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseArraySizes_match__4___rarg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1;
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__4;
lean_object* l_Lean_Meta_getDecLevel___at___private_Lean_Meta_AppBuilder_27__mkListLitImp___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseArraySizes_match__3(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValues(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseArraySizes___closed__1;
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l___private_Lean_Meta_AppBuilder_3__mkEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_revert___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__7___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_caseArraySizes___spec__2___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getArrayArgType___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_caseArraySizes___spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseArraySizes_match__1(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_CaseArraySizesSubgoal_inhabited___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_27__mkListLitImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseArraySizes_match__4(lean_object*);
lean_object* l_Lean_Meta_caseArraySizes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseArraySizes_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseArraySizes_match__5(lean_object*);
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_match__1___rarg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_CaseArraySizesSubgoal_elems___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_CaseArraySizesSubgoal_diseqs___default() {
_start:
{
lean_object* x_1; 
x_1 = l_Array_empty___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_CaseArraySizesSubgoal_subst___default() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_CaseArraySizesSubgoal_inhabited___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = l_Array_empty___closed__1;
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_CaseArraySizesSubgoal_inhabited() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Meta_CaseArraySizesSubgoal_inhabited___closed__1;
return x_1;
}
}
lean_object* l_Lean_Meta_getArrayArgType___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Expr_appArg_x21(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_getArrayArgType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("array expected");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_getArrayArgType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_getArrayArgType___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_getArrayArgType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_inferType___at_Lean_Meta_throwLetTypeMismatchMessage___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Meta_whnfD___at___private_Lean_Meta_Check_0__Lean_Meta_getFunctionDomain___spec__1(x_8, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_141____closed__4;
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Expr_isAppOfArity___main(x_11, x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_11);
x_16 = l_Lean_indentExpr(x_1);
x_17 = l_Lean_Meta_getArrayArgType___closed__2;
x_18 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Array_iterateMAux___main___at_Lean_withNestedTraces___spec__4___closed__1;
x_20 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at_Lean_Meta_throwLetTypeMismatchMessage___spec__2___rarg(x_20, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
return x_21;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = l_Lean_Meta_getArrayArgType___lambda__1(x_11, x_26, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_11);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_10, 0);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_10);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
return x_7;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_7, 0);
x_34 = lean_ctor_get(x_7, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_7);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
lean_object* l_Lean_Meta_getArrayArgType___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_getArrayArgType___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_mkAppM___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_20__mkFun___boxed), 6, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___rarg___lambda__1___boxed), 7, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_214 = lean_st_ref_get(x_6, x_7);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_215, 3);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_ctor_get_uint8(x_216, sizeof(void*)*1);
lean_dec(x_216);
if (x_217 == 0)
{
lean_object* x_218; uint8_t x_219; 
x_218 = lean_ctor_get(x_214, 1);
lean_inc(x_218);
lean_dec(x_214);
x_219 = 0;
x_11 = x_219;
x_12 = x_218;
goto block_213;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_220 = lean_ctor_get(x_214, 1);
lean_inc(x_220);
lean_dec(x_214);
x_221 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_222 = l___private_Lean_Util_Trace_3__checkTraceOptionM___at_Lean_Meta_isLevelDefEq___spec__1(x_221, x_3, x_4, x_5, x_6, x_220);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
lean_dec(x_222);
x_225 = lean_unbox(x_223);
lean_dec(x_223);
x_11 = x_225;
x_12 = x_224;
goto block_213;
}
block_213:
{
if (x_11 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_13 = lean_st_ref_get(x_6, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 3);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
lean_dec(x_15);
x_18 = lean_st_ref_take(x_6, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_19, 3);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_20);
if (x_24 == 0)
{
uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = 0;
lean_ctor_set_uint8(x_20, sizeof(void*)*1, x_25);
x_26 = lean_st_ref_set(x_6, x_19, x_21);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_6);
x_28 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__2___rarg(x_10, x_3, x_4, x_5, x_6, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_st_ref_get(x_6, x_30);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_st_ref_take(x_6, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_34, 3);
lean_dec(x_38);
x_39 = !lean_is_exclusive(x_35);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; 
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_17);
x_40 = lean_st_ref_set(x_6, x_34, x_36);
lean_dec(x_6);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_29);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_29);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_45 = lean_ctor_get(x_35, 0);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_17);
lean_ctor_set(x_34, 3, x_46);
x_47 = lean_st_ref_set(x_6, x_34, x_36);
lean_dec(x_6);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_29);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_51 = lean_ctor_get(x_34, 0);
x_52 = lean_ctor_get(x_34, 1);
x_53 = lean_ctor_get(x_34, 2);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_34);
x_54 = lean_ctor_get(x_35, 0);
lean_inc(x_54);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 x_55 = x_35;
} else {
 lean_dec_ref(x_35);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(0, 1, 1);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_17);
x_57 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_52);
lean_ctor_set(x_57, 2, x_53);
lean_ctor_set(x_57, 3, x_56);
x_58 = lean_st_ref_set(x_6, x_57, x_36);
lean_dec(x_6);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_60 = x_58;
} else {
 lean_dec_ref(x_58);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_29);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_62 = lean_ctor_get(x_28, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_28, 1);
lean_inc(x_63);
lean_dec(x_28);
x_64 = lean_st_ref_get(x_6, x_63);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_st_ref_take(x_6, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec(x_66);
x_70 = !lean_is_exclusive(x_67);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; 
x_71 = lean_ctor_get(x_67, 3);
lean_dec(x_71);
x_72 = !lean_is_exclusive(x_68);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
lean_ctor_set_uint8(x_68, sizeof(void*)*1, x_17);
x_73 = lean_st_ref_set(x_6, x_67, x_69);
lean_dec(x_6);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 0);
lean_dec(x_75);
lean_ctor_set_tag(x_73, 1);
lean_ctor_set(x_73, 0, x_62);
return x_73;
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_62);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_68, 0);
lean_inc(x_78);
lean_dec(x_68);
x_79 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set_uint8(x_79, sizeof(void*)*1, x_17);
lean_ctor_set(x_67, 3, x_79);
x_80 = lean_st_ref_set(x_6, x_67, x_69);
lean_dec(x_6);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_82 = x_80;
} else {
 lean_dec_ref(x_80);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
 lean_ctor_set_tag(x_83, 1);
}
lean_ctor_set(x_83, 0, x_62);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_84 = lean_ctor_get(x_67, 0);
x_85 = lean_ctor_get(x_67, 1);
x_86 = lean_ctor_get(x_67, 2);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_67);
x_87 = lean_ctor_get(x_68, 0);
lean_inc(x_87);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 x_88 = x_68;
} else {
 lean_dec_ref(x_68);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(0, 1, 1);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_17);
x_90 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_90, 0, x_84);
lean_ctor_set(x_90, 1, x_85);
lean_ctor_set(x_90, 2, x_86);
lean_ctor_set(x_90, 3, x_89);
x_91 = lean_st_ref_set(x_6, x_90, x_69);
lean_dec(x_6);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
 lean_ctor_set_tag(x_94, 1);
}
lean_ctor_set(x_94, 0, x_62);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
else
{
lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_95 = lean_ctor_get(x_20, 0);
lean_inc(x_95);
lean_dec(x_20);
x_96 = 0;
x_97 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*1, x_96);
lean_ctor_set(x_19, 3, x_97);
x_98 = lean_st_ref_set(x_6, x_19, x_21);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
lean_dec(x_98);
lean_inc(x_6);
x_100 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__2___rarg(x_10, x_3, x_4, x_5, x_6, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_st_ref_get(x_6, x_102);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_st_ref_take(x_6, x_104);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_106, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec(x_105);
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 1);
lean_inc(x_110);
x_111 = lean_ctor_get(x_106, 2);
lean_inc(x_111);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 lean_ctor_release(x_106, 2);
 lean_ctor_release(x_106, 3);
 x_112 = x_106;
} else {
 lean_dec_ref(x_106);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_107, 0);
lean_inc(x_113);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_114 = x_107;
} else {
 lean_dec_ref(x_107);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(0, 1, 1);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set_uint8(x_115, sizeof(void*)*1, x_17);
if (lean_is_scalar(x_112)) {
 x_116 = lean_alloc_ctor(0, 4, 0);
} else {
 x_116 = x_112;
}
lean_ctor_set(x_116, 0, x_109);
lean_ctor_set(x_116, 1, x_110);
lean_ctor_set(x_116, 2, x_111);
lean_ctor_set(x_116, 3, x_115);
x_117 = lean_st_ref_set(x_6, x_116, x_108);
lean_dec(x_6);
x_118 = lean_ctor_get(x_117, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_119 = x_117;
} else {
 lean_dec_ref(x_117);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_101);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_121 = lean_ctor_get(x_100, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_100, 1);
lean_inc(x_122);
lean_dec(x_100);
x_123 = lean_st_ref_get(x_6, x_122);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
lean_dec(x_123);
x_125 = lean_st_ref_take(x_6, x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_126, 3);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_dec(x_125);
x_129 = lean_ctor_get(x_126, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_126, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_126, 2);
lean_inc(x_131);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 lean_ctor_release(x_126, 2);
 lean_ctor_release(x_126, 3);
 x_132 = x_126;
} else {
 lean_dec_ref(x_126);
 x_132 = lean_box(0);
}
x_133 = lean_ctor_get(x_127, 0);
lean_inc(x_133);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 x_134 = x_127;
} else {
 lean_dec_ref(x_127);
 x_134 = lean_box(0);
}
if (lean_is_scalar(x_134)) {
 x_135 = lean_alloc_ctor(0, 1, 1);
} else {
 x_135 = x_134;
}
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set_uint8(x_135, sizeof(void*)*1, x_17);
if (lean_is_scalar(x_132)) {
 x_136 = lean_alloc_ctor(0, 4, 0);
} else {
 x_136 = x_132;
}
lean_ctor_set(x_136, 0, x_129);
lean_ctor_set(x_136, 1, x_130);
lean_ctor_set(x_136, 2, x_131);
lean_ctor_set(x_136, 3, x_135);
x_137 = lean_st_ref_set(x_6, x_136, x_128);
lean_dec(x_6);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_139 = x_137;
} else {
 lean_dec_ref(x_137);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
 lean_ctor_set_tag(x_140, 1);
}
lean_ctor_set(x_140, 0, x_121);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_141 = lean_ctor_get(x_19, 0);
x_142 = lean_ctor_get(x_19, 1);
x_143 = lean_ctor_get(x_19, 2);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_19);
x_144 = lean_ctor_get(x_20, 0);
lean_inc(x_144);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 x_145 = x_20;
} else {
 lean_dec_ref(x_20);
 x_145 = lean_box(0);
}
x_146 = 0;
if (lean_is_scalar(x_145)) {
 x_147 = lean_alloc_ctor(0, 1, 1);
} else {
 x_147 = x_145;
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set_uint8(x_147, sizeof(void*)*1, x_146);
x_148 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_148, 0, x_141);
lean_ctor_set(x_148, 1, x_142);
lean_ctor_set(x_148, 2, x_143);
lean_ctor_set(x_148, 3, x_147);
x_149 = lean_st_ref_set(x_6, x_148, x_21);
x_150 = lean_ctor_get(x_149, 1);
lean_inc(x_150);
lean_dec(x_149);
lean_inc(x_6);
x_151 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__2___rarg(x_10, x_3, x_4, x_5, x_6, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_st_ref_get(x_6, x_153);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
lean_dec(x_154);
x_156 = lean_st_ref_take(x_6, x_155);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_157, 3);
lean_inc(x_158);
x_159 = lean_ctor_get(x_156, 1);
lean_inc(x_159);
lean_dec(x_156);
x_160 = lean_ctor_get(x_157, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_157, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_157, 2);
lean_inc(x_162);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 lean_ctor_release(x_157, 2);
 lean_ctor_release(x_157, 3);
 x_163 = x_157;
} else {
 lean_dec_ref(x_157);
 x_163 = lean_box(0);
}
x_164 = lean_ctor_get(x_158, 0);
lean_inc(x_164);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 x_165 = x_158;
} else {
 lean_dec_ref(x_158);
 x_165 = lean_box(0);
}
if (lean_is_scalar(x_165)) {
 x_166 = lean_alloc_ctor(0, 1, 1);
} else {
 x_166 = x_165;
}
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set_uint8(x_166, sizeof(void*)*1, x_17);
if (lean_is_scalar(x_163)) {
 x_167 = lean_alloc_ctor(0, 4, 0);
} else {
 x_167 = x_163;
}
lean_ctor_set(x_167, 0, x_160);
lean_ctor_set(x_167, 1, x_161);
lean_ctor_set(x_167, 2, x_162);
lean_ctor_set(x_167, 3, x_166);
x_168 = lean_st_ref_set(x_6, x_167, x_159);
lean_dec(x_6);
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_170 = x_168;
} else {
 lean_dec_ref(x_168);
 x_170 = lean_box(0);
}
if (lean_is_scalar(x_170)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_170;
}
lean_ctor_set(x_171, 0, x_152);
lean_ctor_set(x_171, 1, x_169);
return x_171;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_172 = lean_ctor_get(x_151, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_151, 1);
lean_inc(x_173);
lean_dec(x_151);
x_174 = lean_st_ref_get(x_6, x_173);
x_175 = lean_ctor_get(x_174, 1);
lean_inc(x_175);
lean_dec(x_174);
x_176 = lean_st_ref_take(x_6, x_175);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_177, 3);
lean_inc(x_178);
x_179 = lean_ctor_get(x_176, 1);
lean_inc(x_179);
lean_dec(x_176);
x_180 = lean_ctor_get(x_177, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_177, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_177, 2);
lean_inc(x_182);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 lean_ctor_release(x_177, 2);
 lean_ctor_release(x_177, 3);
 x_183 = x_177;
} else {
 lean_dec_ref(x_177);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_178, 0);
lean_inc(x_184);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 x_185 = x_178;
} else {
 lean_dec_ref(x_178);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(0, 1, 1);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set_uint8(x_186, sizeof(void*)*1, x_17);
if (lean_is_scalar(x_183)) {
 x_187 = lean_alloc_ctor(0, 4, 0);
} else {
 x_187 = x_183;
}
lean_ctor_set(x_187, 0, x_180);
lean_ctor_set(x_187, 1, x_181);
lean_ctor_set(x_187, 2, x_182);
lean_ctor_set(x_187, 3, x_186);
x_188 = lean_st_ref_set(x_6, x_187, x_179);
lean_dec(x_6);
x_189 = lean_ctor_get(x_188, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_190 = x_188;
} else {
 lean_dec_ref(x_188);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
 lean_ctor_set_tag(x_191, 1);
}
lean_ctor_set(x_191, 0, x_172);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_192 = lean_ctor_get(x_5, 3);
lean_inc(x_192);
x_193 = l___private_Lean_Util_Trace_5__getResetTraces___at_Lean_Meta_isLevelDefEq___spec__4___rarg(x_6, x_12);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_196 = l_Lean_Meta_withNewMCtxDepth___at___private_Lean_Meta_Instances_1__mkInstanceKey___spec__2___rarg(x_10, x_3, x_4, x_5, x_6, x_195);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_200 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_194, x_199, x_192, x_3, x_4, x_5, x_6, x_198);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_201 = !lean_is_exclusive(x_200);
if (x_201 == 0)
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_200, 0);
lean_dec(x_202);
lean_ctor_set(x_200, 0, x_197);
return x_200;
}
else
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_200, 1);
lean_inc(x_203);
lean_dec(x_200);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_197);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; 
x_205 = lean_ctor_get(x_196, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_196, 1);
lean_inc(x_206);
lean_dec(x_196);
x_207 = l_Lean_Meta_mkAppM___rarg___closed__2;
x_208 = l___private_Lean_Util_Trace_4__addNode___at_Lean_Meta_isLevelDefEq___spec__5(x_194, x_207, x_192, x_3, x_4, x_5, x_6, x_206);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_209 = !lean_is_exclusive(x_208);
if (x_209 == 0)
{
lean_object* x_210; 
x_210 = lean_ctor_get(x_208, 0);
lean_dec(x_210);
lean_ctor_set_tag(x_208, 1);
lean_ctor_set(x_208, 0, x_205);
return x_208;
}
else
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_208, 1);
lean_inc(x_211);
lean_dec(x_208);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_205);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
}
}
}
lean_object* l_Lean_Meta_mkLt___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = l_Lean_mkAppStx___closed__9;
x_9 = lean_array_push(x_8, x_1);
x_10 = lean_array_push(x_9, x_2);
x_11 = l_Lean_Meta_mkLt___rarg___closed__4;
x_12 = l_Lean_Meta_mkAppM___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___spec__2(x_11, x_10, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
lean_object* l_Lean_Meta_mkDecideProof___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_mkOptionalNode___closed__2;
x_8 = lean_array_push(x_7, x_1);
x_9 = l_Lean_Meta_mkDecideProof___rarg___closed__2;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Meta_mkAppM___at_Lean_Meta_mkDecideProof___spec__1(x_9, x_8, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_boolToExpr___lambda__1___closed__6;
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_11, x_13, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(x_13, x_2, x_3, x_4, x_5, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_20 = l___private_Lean_Meta_AppBuilder_2__mkExpectedTypeHint(x_18, x_15, x_2, x_3, x_4, x_5, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_push(x_7, x_21);
x_24 = l_Lean_Meta_mkDecideProof___rarg___lambda__1___closed__2;
x_25 = l_Lean_Meta_mkAppM___at_Lean_Meta_mkDecideProof___spec__1(x_24, x_23, x_2, x_3, x_4, x_5, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
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
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_17);
if (x_30 == 0)
{
return x_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_17, 0);
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_17);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_14);
if (x_34 == 0)
{
return x_14;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_14, 0);
x_36 = lean_ctor_get(x_14, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_14);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = !lean_is_exclusive(x_10);
if (x_38 == 0)
{
return x_10;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_10, 0);
x_40 = lean_ctor_get(x_10, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_10);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("getLit");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_141____closed__4;
x_2 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Lean_mkNatLit(x_2);
x_11 = l_Lean_mkNatLit(x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_10);
x_12 = l_Lean_Meta_mkLt___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___spec__1(x_10, x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_15 = l_Lean_Meta_mkDecideProof___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___spec__3(x_13, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Std_PersistentHashMap_mkCollisionNode___rarg___closed__1;
x_19 = lean_array_push(x_18, x_1);
x_20 = lean_array_push(x_19, x_10);
x_21 = lean_array_push(x_20, x_4);
x_22 = lean_array_push(x_21, x_16);
x_23 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__2;
x_24 = l_Lean_Meta_mkAppM___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___spec__2(x_23, x_22, x_5, x_6, x_7, x_8, x_17);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
return x_12;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_12);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkArrayLit___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_Meta_getDecLevel___at___private_Lean_Meta_AppBuilder_27__mkListLitImp___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = l___private_Lean_Meta_AppBuilder_27__mkListLitImp(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_Array_hasQuote___rarg___closed__2;
x_17 = l_Lean_mkConst(x_16, x_15);
x_18 = l_Lean_mkApp(x_17, x_1);
x_19 = l_Lean_mkApp(x_18, x_13);
lean_ctor_set(x_11, 0, x_19);
return x_11;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_11, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_11);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_9);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_Array_hasQuote___rarg___closed__2;
x_25 = l_Lean_mkConst(x_24, x_23);
x_26 = l_Lean_mkApp(x_25, x_1);
x_27 = l_Lean_mkApp(x_26, x_20);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
return x_8;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_8, 0);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_8);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_getMVarType(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_push(x_2, x_5);
x_15 = l_Lean_Meta_mkForallFVars___at_Lean_Meta_assertAfter___spec__13(x_14, x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_array_push(x_3, x_4);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_15, 0, x_19);
return x_15;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_array_push(x_3, x_4);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_array_push(x_1, x_11);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_18 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(x_2, x_3, x_4, x_5, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_push(x_6, x_19);
x_22 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(x_7, x_2, x_4, x_8, x_5, x_9, x_10, x_17, x_21, x_12, x_13, x_14, x_15, x_20);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_23 = !lean_is_exclusive(x_18);
if (x_23 == 0)
{
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 0);
x_25 = lean_ctor_get(x_18, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_18);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("toArrayLitEq");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_141____closed__4;
x_2 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(3u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("hEqALit");
return x_1;
}
}
static lean_object* _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__4;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_7, x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_4);
x_16 = l_Array_toList___rarg(x_8);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_17 = l_Lean_Meta_mkArrayLit___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___spec__1(x_6, x_16, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_2);
x_20 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_2, x_18, x_10, x_11, x_12, x_13, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_mkNatLit(x_3);
x_24 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3;
x_25 = lean_array_push(x_24, x_2);
x_26 = lean_array_push(x_25, x_23);
x_27 = lean_array_push(x_26, x_5);
x_28 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_29 = l_Lean_Meta_mkAppM___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___spec__2(x_28, x_27, x_10, x_11, x_12, x_13, x_22);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lambda__1___boxed), 10, 4);
lean_closure_set(x_32, 0, x_1);
lean_closure_set(x_32, 1, x_8);
lean_closure_set(x_32, 2, x_9);
lean_closure_set(x_32, 3, x_30);
x_33 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__5;
x_34 = 0;
x_35 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__7___rarg(x_33, x_34, x_21, x_32, x_10, x_11, x_12, x_13, x_31);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_29);
if (x_36 == 0)
{
return x_29;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_29, 0);
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_29);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_20);
if (x_40 == 0)
{
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_20);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_17);
if (x_44 == 0)
{
return x_17;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_17, 0);
x_46 = lean_ctor_get(x_17, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_17);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_7, x_48);
lean_inc(x_49);
lean_inc(x_4);
x_50 = l_Lean_Name_appendIndexAfter(x_4, x_49);
lean_inc(x_6);
x_51 = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lambda__2), 16, 10);
lean_closure_set(x_51, 0, x_8);
lean_closure_set(x_51, 1, x_2);
lean_closure_set(x_51, 2, x_7);
lean_closure_set(x_51, 3, x_3);
lean_closure_set(x_51, 4, x_5);
lean_closure_set(x_51, 5, x_9);
lean_closure_set(x_51, 6, x_1);
lean_closure_set(x_51, 7, x_4);
lean_closure_set(x_51, 8, x_6);
lean_closure_set(x_51, 9, x_49);
x_52 = 0;
x_53 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__7___rarg(x_50, x_52, x_6, x_51, x_10, x_11, x_12, x_13, x_14);
return x_53;
}
}
}
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_11;
}
}
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_2);
x_11 = l_Lean_Meta_getArrayArgType(x_2, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_empty___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(x_1, x_2, x_3, x_4, x_5, x_12, x_14, x_15, x_15, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
lean_inc(x_1);
x_21 = l_Lean_Meta_getMVarTag(x_1, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_6);
x_24 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_19, x_22, x_6, x_7, x_8, x_9, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_25);
x_27 = l_Array_iterateMAux___main___at_Lean_mkAppN___spec__1(x_20, x_20, x_14, x_25);
lean_dec(x_20);
x_28 = l_Lean_Meta_assignExprMVar___at_Lean_Meta_admit___spec__2(x_1, x_27, x_6, x_7, x_8, x_9, x_26);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = l_Lean_Expr_mvarId_x21(x_25);
lean_dec(x_25);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = l_Lean_Expr_mvarId_x21(x_25);
lean_dec(x_25);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
uint8_t x_35; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_21);
if (x_35 == 0)
{
return x_21;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_21, 0);
x_37 = lean_ctor_get(x_21, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_21);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
return x_16;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_16, 0);
x_41 = lean_ctor_get(x_16, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_16);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_11);
if (x_43 == 0)
{
return x_11;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
lean_object* l_Lean_Meta_caseArraySizes_match__1___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_caseArraySizes_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_caseArraySizes_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_caseArraySizes_match__2___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_caseArraySizes_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_caseArraySizes_match__2___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_caseArraySizes_match__3___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_caseArraySizes_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_caseArraySizes_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_caseArraySizes_match__4___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_caseArraySizes_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_caseArraySizes_match__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_caseArraySizes_match__5___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_caseArraySizes_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_caseArraySizes_match__5___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_caseArraySizes_match__6___rarg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_caseArraySizes_match__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_caseArraySizes_match__6___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_caseArraySizes___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_1);
x_5 = x_2;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = x_6;
x_10 = l_Lean_mkNatLit(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_1, x_11);
x_13 = x_10;
x_14 = lean_array_fset(x_8, x_1, x_13);
lean_dec(x_1);
x_1 = x_12;
x_2 = x_14;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_caseArraySizes___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_3);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = x_3;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_array_fget(x_3, x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_fset(x_3, x_2, x_8);
x_10 = x_7;
x_11 = l_Lean_Meta_FVarSubst_get(x_1, x_10);
x_12 = l_Lean_Expr_fvarId_x21(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_2, x_13);
x_15 = x_12;
x_16 = lean_array_fset(x_9, x_2, x_15);
lean_dec(x_2);
x_2 = x_14;
x_3 = x_16;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_caseArraySizes___spec__3___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
x_13 = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = 0;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_introNCore(x_14, x_3, x_16, x_17, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_23 = l_Lean_Meta_intro1Core(x_22, x_17, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_28 = l_Lean_Meta_clear(x_27, x_5, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = 1;
x_32 = l_Lean_Meta_substCore(x_29, x_26, x_17, x_6, x_31, x_8, x_9, x_10, x_11, x_30);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Array_empty___closed__1;
x_38 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_21);
lean_ctor_set(x_38, 2, x_37);
lean_ctor_set(x_38, 3, x_35);
lean_ctor_set(x_32, 0, x_38);
return x_32;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_32, 0);
x_40 = lean_ctor_get(x_32, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_32);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_dec(x_39);
x_43 = l_Array_empty___closed__1;
x_44 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_21);
lean_ctor_set(x_44, 2, x_43);
lean_ctor_set(x_44, 3, x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_21);
x_46 = !lean_is_exclusive(x_32);
if (x_46 == 0)
{
return x_32;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_32, 0);
x_48 = lean_ctor_get(x_32, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_32);
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
lean_dec(x_26);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_50 = !lean_is_exclusive(x_28);
if (x_50 == 0)
{
return x_28;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_28, 0);
x_52 = lean_ctor_get(x_28, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_28);
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
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_54 = !lean_is_exclusive(x_23);
if (x_54 == 0)
{
return x_23;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_23, 0);
x_56 = lean_ctor_get(x_23, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_23);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
x_58 = !lean_is_exclusive(x_18);
if (x_58 == 0)
{
return x_18;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_18, 0);
x_60 = lean_ctor_get(x_18, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_18);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_13);
if (x_62 == 0)
{
return x_13;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_13, 0);
x_64 = lean_ctor_get(x_13, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_13);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_caseArraySizes___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_7);
x_14 = lean_nat_dec_lt(x_6, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = x_7;
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_17 = lean_array_fget(x_7, x_6);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_fset(x_7, x_6, x_18);
x_20 = x_17;
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_inc(x_5);
x_23 = l_Lean_Meta_FVarSubst_get(x_21, x_5);
x_24 = l_Lean_Expr_fvarId_x21(x_23);
lean_dec(x_23);
x_25 = lean_array_get_size(x_1);
x_26 = lean_nat_dec_lt(x_6, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
uint8_t x_27; uint8_t x_28; lean_object* x_29; 
lean_dec(x_24);
x_27 = 0;
x_28 = 1;
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
x_29 = l_Lean_Meta_substCore(x_22, x_5, x_27, x_21, x_28, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_dec(x_20);
x_35 = x_34;
x_36 = l_Array_umapMAux___main___at_Lean_Meta_caseArraySizes___spec__2(x_32, x_18, x_35);
x_37 = x_36;
x_38 = l_Array_empty___closed__1;
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_39, 2, x_37);
lean_ctor_set(x_39, 3, x_32);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_6, x_40);
x_42 = x_39;
x_43 = lean_array_fset(x_19, x_6, x_42);
lean_dec(x_6);
x_6 = x_41;
x_7 = x_43;
x_12 = x_31;
goto _start;
}
else
{
uint8_t x_45; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_29);
if (x_45 == 0)
{
return x_29;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_29, 0);
x_47 = lean_ctor_get(x_29, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_29);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_49 = lean_array_fget(x_1, x_6);
x_50 = lean_ctor_get(x_20, 1);
lean_inc(x_50);
lean_dec(x_20);
x_51 = l_Lean_Name_inhabited;
x_52 = lean_array_get(x_51, x_50, x_18);
lean_dec(x_50);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_53 = l_Lean_Meta_clear(x_22, x_52, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
lean_inc(x_4);
x_56 = l_Lean_Meta_FVarSubst_get(x_21, x_4);
x_57 = l_Lean_Expr_fvarId_x21(x_56);
lean_dec(x_56);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_58 = l_Lean_Meta_clear(x_54, x_57, x_8, x_9, x_10, x_11, x_55);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
lean_inc(x_24);
x_61 = l_Lean_mkFVar(x_24);
x_62 = lean_alloc_closure((void*)(l_Lean_Meta_mkEqSymm___at_Lean_Meta_substCore___spec__4), 6, 1);
lean_closure_set(x_62, 0, x_61);
lean_inc(x_2);
lean_inc(x_3);
lean_inc(x_59);
x_63 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_caseArraySizes___spec__3___lambda__1), 12, 6);
lean_closure_set(x_63, 0, x_59);
lean_closure_set(x_63, 1, x_3);
lean_closure_set(x_63, 2, x_49);
lean_closure_set(x_63, 3, x_2);
lean_closure_set(x_63, 4, x_24);
lean_closure_set(x_63, 5, x_21);
x_64 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_64, 0, x_62);
lean_closure_set(x_64, 1, x_63);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_65 = l_Lean_Meta_withMVarContext___at_Lean_Meta_revert___spec__5___rarg(x_59, x_64, x_8, x_9, x_10, x_11, x_60);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_add(x_6, x_68);
x_70 = x_66;
x_71 = lean_array_fset(x_19, x_6, x_70);
lean_dec(x_6);
x_6 = x_69;
x_7 = x_71;
x_12 = x_67;
goto _start;
}
else
{
uint8_t x_73; 
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_65);
if (x_73 == 0)
{
return x_65;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_65, 0);
x_75 = lean_ctor_get(x_65, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_65);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_49);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_77 = !lean_is_exclusive(x_58);
if (x_77 == 0)
{
return x_58;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_58, 0);
x_79 = lean_ctor_get(x_58, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_58);
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
lean_dec(x_49);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_81 = !lean_is_exclusive(x_53);
if (x_81 == 0)
{
return x_53;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_53, 0);
x_83 = lean_ctor_get(x_53, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_53);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_caseArraySizes___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_141____closed__4;
x_2 = l_Array_myMacro____x40_Init_Data_Array_Macros___hyg_464____closed__24;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_caseArraySizes___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("aSize");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_caseArraySizes___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_caseArraySizes___closed__2;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_caseArraySizes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_mkFVar(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_11);
x_12 = l_Lean_Meta_getArrayArgType(x_11, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_11);
x_15 = lean_array_push(x_14, x_11);
x_16 = l_Lean_Meta_caseArraySizes___closed__1;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Meta_mkAppM___at___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___spec__2(x_16, x_15, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Meta_caseArraySizes___closed__3;
x_21 = l_Lean_Literal_type___closed__3;
x_22 = l_Lean_Meta_caseValue___closed__2;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_23 = l_Lean_Meta_assertExt(x_1, x_20, x_21, x_18, x_22, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = l_Lean_Meta_intro1Core(x_24, x_26, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_32 = l_Lean_Meta_intro1Core(x_31, x_26, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
lean_inc(x_3);
x_37 = x_3;
x_38 = lean_unsigned_to_nat(0u);
x_39 = l_Array_umapMAux___main___at_Lean_Meta_caseArraySizes___spec__1(x_38, x_37);
x_40 = x_39;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_30);
x_41 = l_Lean_Meta_caseValues(x_36, x_30, x_40, x_5, x_6, x_7, x_8, x_9, x_34);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = x_42;
x_45 = lean_alloc_closure((void*)(l_Array_umapMAux___main___at_Lean_Meta_caseArraySizes___spec__3___boxed), 12, 7);
lean_closure_set(x_45, 0, x_3);
lean_closure_set(x_45, 1, x_4);
lean_closure_set(x_45, 2, x_11);
lean_closure_set(x_45, 3, x_30);
lean_closure_set(x_45, 4, x_35);
lean_closure_set(x_45, 5, x_38);
lean_closure_set(x_45, 6, x_44);
x_46 = x_45;
x_47 = lean_apply_5(x_46, x_6, x_7, x_8, x_9, x_43);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_35);
lean_dec(x_30);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_48 = !lean_is_exclusive(x_41);
if (x_48 == 0)
{
return x_41;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_41, 0);
x_50 = lean_ctor_get(x_41, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_41);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec(x_30);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_32);
if (x_52 == 0)
{
return x_32;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_32, 0);
x_54 = lean_ctor_get(x_32, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_32);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_56 = !lean_is_exclusive(x_27);
if (x_56 == 0)
{
return x_27;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_27, 0);
x_58 = lean_ctor_get(x_27, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_27);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_60 = !lean_is_exclusive(x_23);
if (x_60 == 0)
{
return x_23;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_23, 0);
x_62 = lean_ctor_get(x_23, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_23);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_17);
if (x_64 == 0)
{
return x_17;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_17, 0);
x_66 = lean_ctor_get(x_17, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_17);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_12);
if (x_68 == 0)
{
return x_12;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_12, 0);
x_70 = lean_ctor_get(x_12, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_12);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_caseArraySizes___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_umapMAux___main___at_Lean_Meta_caseArraySizes___spec__2(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_caseArraySizes___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_umapMAux___main___at_Lean_Meta_caseArraySizes___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_13;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(lean_object*);
lean_object* initialize_Lean_Meta_Match_CaseValues(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Match_CaseArraySizes(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_CaseValues(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_CaseArraySizesSubgoal_elems___default = _init_l_Lean_Meta_CaseArraySizesSubgoal_elems___default();
lean_mark_persistent(l_Lean_Meta_CaseArraySizesSubgoal_elems___default);
l_Lean_Meta_CaseArraySizesSubgoal_diseqs___default = _init_l_Lean_Meta_CaseArraySizesSubgoal_diseqs___default();
lean_mark_persistent(l_Lean_Meta_CaseArraySizesSubgoal_diseqs___default);
l_Lean_Meta_CaseArraySizesSubgoal_subst___default = _init_l_Lean_Meta_CaseArraySizesSubgoal_subst___default();
lean_mark_persistent(l_Lean_Meta_CaseArraySizesSubgoal_subst___default);
l_Lean_Meta_CaseArraySizesSubgoal_inhabited___closed__1 = _init_l_Lean_Meta_CaseArraySizesSubgoal_inhabited___closed__1();
lean_mark_persistent(l_Lean_Meta_CaseArraySizesSubgoal_inhabited___closed__1);
l_Lean_Meta_CaseArraySizesSubgoal_inhabited = _init_l_Lean_Meta_CaseArraySizesSubgoal_inhabited();
lean_mark_persistent(l_Lean_Meta_CaseArraySizesSubgoal_inhabited);
l_Lean_Meta_getArrayArgType___closed__1 = _init_l_Lean_Meta_getArrayArgType___closed__1();
lean_mark_persistent(l_Lean_Meta_getArrayArgType___closed__1);
l_Lean_Meta_getArrayArgType___closed__2 = _init_l_Lean_Meta_getArrayArgType___closed__2();
lean_mark_persistent(l_Lean_Meta_getArrayArgType___closed__2);
l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1 = _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1);
l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__2 = _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__2);
l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1 = _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1);
l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2 = _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2);
l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3 = _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3);
l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__4 = _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__4();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__4);
l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__5 = _init_l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__5();
lean_mark_persistent(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__5);
l_Lean_Meta_caseArraySizes___closed__1 = _init_l_Lean_Meta_caseArraySizes___closed__1();
lean_mark_persistent(l_Lean_Meta_caseArraySizes___closed__1);
l_Lean_Meta_caseArraySizes___closed__2 = _init_l_Lean_Meta_caseArraySizes___closed__2();
lean_mark_persistent(l_Lean_Meta_caseArraySizes___closed__2);
l_Lean_Meta_caseArraySizes___closed__3 = _init_l_Lean_Meta_caseArraySizes___closed__3();
lean_mark_persistent(l_Lean_Meta_caseArraySizes___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
