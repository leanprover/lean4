// Lean compiler output
// Module: Lean.Meta.Tactic.Subst
// Imports: Init Lean.Meta.AppBuilder Lean.Meta.MatchUtil Lean.Meta.Tactic.Util Lean.Meta.Tactic.Revert Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Clear Lean.Meta.Tactic.FVarSubst
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
lean_object* l_Lean_Meta_substCore___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___boxed(lean_object**);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_Meta_subst_match__1(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__4;
lean_object* l_Lean_Meta_substCore___lambda__7___boxed(lean_object**);
lean_object* l_Lean_Meta_substCore_match__6(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__11;
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__2;
lean_object* l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__26;
lean_object* l_Lean_Meta_substCore___lambda__13___closed__12;
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2___boxed(lean_object**);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__12___closed__1;
lean_object* l_Std_PersistentArray_findSomeMAux___at_Lean_Meta_subst___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___at_Lean_Meta_subst___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore_match__4___rarg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_Meta_subst_match__2(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__12___closed__2;
lean_object* l_Lean_Meta_substCore___lambda__13___closed__9;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst_match__2___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__3;
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___at_Lean_Meta_subst___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__20;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__10;
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
lean_object* l_Array_findSomeMAux___at_Lean_Meta_subst___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__16;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_subst_match__3___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore_match__3(lean_object*);
lean_object* l_Std_PersistentArray_findSomeMAux___at_Lean_Meta_subst___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__10___boxed(lean_object**);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__21;
lean_object* l_Lean_Meta_substCore___lambda__13___closed__23;
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__13;
extern lean_object* l_Lean_Init_LeanInit___instance__1;
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___at_Lean_Meta_subst___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_throwUnknownConstant___rarg___closed__3;
lean_object* l_Lean_Meta_substCore___lambda__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst_match__3(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__1;
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__6___boxed(lean_object**);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__22;
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__5;
lean_object* l_Lean_Meta_substCore___lambda__13___closed__14;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Meta_substCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__25;
lean_object* l_Lean_Meta_subst___lambda__1___closed__3;
lean_object* l_Lean_Meta_substCore_match__5(lean_object*);
extern lean_object* l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
lean_object* l_Lean_Meta_substCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRec___at_Lean_Meta_substCore___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___at_Lean_Meta_subst___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__7;
lean_object* l_Lean_Meta_subst___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__11___boxed(lean_object**);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__18;
lean_object* l_Lean_Meta_substCore___lambda__13___closed__24;
lean_object* l_List_map___at_Lean_Meta_substCore___spec__8(lean_object*);
lean_object* l_Lean_Meta_substCore_match__6___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__9___boxed(lean_object**);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__15;
lean_object* l_Lean_Meta_substCore___lambda__13___closed__19;
lean_object* l_Lean_Meta_substCore_match__1(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Meta_substCore_match__1___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___at_Lean_Meta_revert___spec__5___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__11___closed__1;
lean_object* l_Lean_Meta_substCore___lambda__11___closed__4;
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_1147_(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__11___closed__2;
lean_object* l_Lean_Meta_substCore___lambda__13(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__2;
lean_object* l_Array_findSomeMAux___at_Lean_Meta_subst___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore_match__4(lean_object*);
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_substCore___lambda__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__4;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__17;
extern lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
lean_object* l_Lean_Meta_substCore___lambda__13___closed__8;
lean_object* l_Lean_Meta_substCore_match__2(lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__1;
lean_object* l_Lean_Meta_substCore_match__3___rarg(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_getMVarTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Meta_substCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore_match__5___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__11___closed__5;
extern lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Util___hyg_225____closed__2;
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__13___closed__6;
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__8___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__11___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore_match__1___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_substCore_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_substCore_match__1___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_3(x_3, x_8, x_9, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Meta_substCore_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_substCore_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore_match__3___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_substCore_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_substCore_match__3___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore_match__4___rarg(lean_object* x_1, lean_object* x_2) {
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
lean_object* l_Lean_Meta_substCore_match__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_substCore_match__4___rarg), 2, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore_match__5___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_6 = lean_box_uint64(x_5);
x_7 = lean_apply_2(x_2, x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_apply_1(x_3, x_1);
return x_8;
}
}
}
lean_object* l_Lean_Meta_substCore_match__5(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_substCore_match__5___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore_match__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_3(x_3, x_8, x_9, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Meta_substCore_match__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_substCore_match__6___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_4, x_13);
lean_dec(x_4);
x_15 = lean_nat_sub(x_3, x_14);
x_16 = lean_nat_sub(x_15, x_13);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_add(x_16, x_17);
x_19 = l_Lean_Init_LeanInit___instance__1;
x_20 = lean_array_get(x_19, x_1, x_18);
lean_dec(x_18);
x_21 = lean_array_get(x_19, x_2, x_16);
lean_dec(x_16);
x_22 = l_Lean_mkFVar(x_21);
x_23 = l_Lean_Meta_FVarSubst_insert(x_5, x_20, x_22);
x_4 = x_14;
x_5 = x_23;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
}
}
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Meta_substCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Meta_substCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
else
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_10);
if (x_15 == 0)
{
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 0);
x_17 = lean_ctor_get(x_10, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_10);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg___boxed), 9, 0);
return x_2;
}
}
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_4, x_13);
lean_dec(x_4);
x_15 = lean_nat_sub(x_3, x_14);
x_16 = lean_nat_sub(x_15, x_13);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_add(x_16, x_17);
x_19 = l_Lean_Init_LeanInit___instance__1;
x_20 = lean_array_get(x_19, x_1, x_18);
lean_dec(x_18);
x_21 = lean_array_get(x_19, x_2, x_16);
lean_dec(x_16);
x_22 = l_Lean_mkFVar(x_21);
x_23 = l_Lean_Meta_FVarSubst_insert(x_5, x_20, x_22);
x_4 = x_14;
x_5 = x_23;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
}
}
lean_object* l_Lean_Meta_mkEqRec___at_Lean_Meta_substCore___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_4, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_4, x_13);
lean_dec(x_4);
x_15 = lean_nat_sub(x_3, x_14);
x_16 = lean_nat_sub(x_15, x_13);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_add(x_16, x_17);
x_19 = l_Lean_Init_LeanInit___instance__1;
x_20 = lean_array_get(x_19, x_1, x_18);
lean_dec(x_18);
x_21 = lean_array_get(x_19, x_2, x_16);
lean_dec(x_16);
x_22 = l_Lean_mkFVar(x_21);
x_23 = l_Lean_Meta_FVarSubst_insert(x_5, x_20, x_22);
x_4 = x_14;
x_5 = x_23;
goto _start;
}
else
{
lean_object* x_25; 
lean_dec(x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_10);
return x_25;
}
}
}
lean_object* l_List_map___at_Lean_Meta_substCore___spec__8(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_6, 0, x_4);
x_7 = l_List_map___at_Lean_Meta_substCore___spec__8(x_5);
lean_ctor_set(x_1, 1, x_7);
lean_ctor_set(x_1, 0, x_6);
return x_1;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = l_List_map___at_Lean_Meta_substCore___spec__8(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_array_get_size(x_1);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_19 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_20 = l_Lean_Meta_introNCore(x_10, x_18, x_2, x_19, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_array_get_size(x_24);
lean_inc(x_25);
x_26 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1(x_1, x_24, x_25, x_25, x_3, x_11, x_12, x_13, x_14, x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_25);
lean_dec(x_24);
if (x_4 == 0)
{
uint8_t x_27; 
lean_dec(x_9);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_Meta_FVarSubst_insert(x_28, x_5, x_6);
x_30 = l_Lean_Meta_FVarSubst_insert(x_29, x_7, x_8);
lean_ctor_set(x_21, 0, x_30);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = l_Lean_Meta_FVarSubst_insert(x_31, x_5, x_6);
x_34 = l_Lean_Meta_FVarSubst_insert(x_33, x_7, x_8);
lean_ctor_set(x_21, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = l_Lean_Meta_FVarSubst_insert(x_37, x_5, x_9);
x_39 = l_Lean_Meta_FVarSubst_insert(x_38, x_7, x_8);
lean_ctor_set(x_21, 0, x_39);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_26, 0);
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_26);
x_42 = l_Lean_Meta_FVarSubst_insert(x_40, x_5, x_9);
x_43 = l_Lean_Meta_FVarSubst_insert(x_42, x_7, x_8);
lean_ctor_set(x_21, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_21);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_21, 0);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_21);
x_47 = lean_array_get_size(x_45);
lean_inc(x_47);
x_48 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1(x_1, x_45, x_47, x_47, x_3, x_11, x_12, x_13, x_14, x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_47);
lean_dec(x_45);
if (x_4 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_9);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = l_Lean_Meta_FVarSubst_insert(x_49, x_5, x_6);
x_53 = l_Lean_Meta_FVarSubst_insert(x_52, x_7, x_8);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_46);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_6);
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_58 = x_48;
} else {
 lean_dec_ref(x_48);
 x_58 = lean_box(0);
}
x_59 = l_Lean_Meta_FVarSubst_insert(x_56, x_5, x_9);
x_60 = l_Lean_Meta_FVarSubst_insert(x_59, x_7, x_8);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_46);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
return x_20;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_20, 0);
x_65 = lean_ctor_get(x_20, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_20);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__3(x_1, x_14, x_15, x_16, x_17, x_18, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Expr_mvarId_x21(x_2);
if (x_6 == 0)
{
lean_object* x_23; 
lean_dec(x_13);
lean_dec(x_12);
x_23 = l_Lean_Meta_substCore___lambda__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22, x_15, x_16, x_17, x_18, x_21);
return x_23;
}
else
{
lean_object* x_24; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_24 = l_Lean_Meta_clear(x_22, x_12, x_15, x_16, x_17, x_18, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_27 = l_Lean_Meta_clear(x_25, x_13, x_15, x_16, x_17, x_18, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_substCore___lambda__1(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28, x_15, x_16, x_17, x_18, x_29);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
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
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_24);
if (x_35 == 0)
{
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_24);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_17);
x_22 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_2, x_17, x_18, x_19, x_20, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_23);
x_25 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqNDRecImp(x_15, x_23, x_16, x_17, x_18, x_19, x_20, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_substCore___lambda__2(x_3, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_26, x_17, x_18, x_19, x_20, x_27);
lean_dec(x_23);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_Expr_replaceFVar(x_1, x_2, x_12);
lean_dec(x_12);
x_15 = lean_array_push(x_3, x_4);
x_16 = lean_array_push(x_15, x_5);
x_17 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_16, x_14, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_array_get_size(x_1);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_19 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_20 = l_Lean_Meta_introNCore(x_10, x_18, x_2, x_19, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_array_get_size(x_24);
lean_inc(x_25);
x_26 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__5(x_1, x_24, x_25, x_25, x_3, x_11, x_12, x_13, x_14, x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_25);
lean_dec(x_24);
if (x_4 == 0)
{
uint8_t x_27; 
lean_dec(x_9);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_Meta_FVarSubst_insert(x_28, x_5, x_6);
x_30 = l_Lean_Meta_FVarSubst_insert(x_29, x_7, x_8);
lean_ctor_set(x_21, 0, x_30);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = l_Lean_Meta_FVarSubst_insert(x_31, x_5, x_6);
x_34 = l_Lean_Meta_FVarSubst_insert(x_33, x_7, x_8);
lean_ctor_set(x_21, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = l_Lean_Meta_FVarSubst_insert(x_37, x_5, x_9);
x_39 = l_Lean_Meta_FVarSubst_insert(x_38, x_7, x_8);
lean_ctor_set(x_21, 0, x_39);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_26, 0);
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_26);
x_42 = l_Lean_Meta_FVarSubst_insert(x_40, x_5, x_9);
x_43 = l_Lean_Meta_FVarSubst_insert(x_42, x_7, x_8);
lean_ctor_set(x_21, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_21);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_21, 0);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_21);
x_47 = lean_array_get_size(x_45);
lean_inc(x_47);
x_48 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__5(x_1, x_45, x_47, x_47, x_3, x_11, x_12, x_13, x_14, x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_47);
lean_dec(x_45);
if (x_4 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_9);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = l_Lean_Meta_FVarSubst_insert(x_49, x_5, x_6);
x_53 = l_Lean_Meta_FVarSubst_insert(x_52, x_7, x_8);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_46);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_6);
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_58 = x_48;
} else {
 lean_dec_ref(x_48);
 x_58 = lean_box(0);
}
x_59 = l_Lean_Meta_FVarSubst_insert(x_56, x_5, x_9);
x_60 = l_Lean_Meta_FVarSubst_insert(x_59, x_7, x_8);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_46);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
return x_20;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_20, 0);
x_65 = lean_ctor_get(x_20, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_20);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__3(x_1, x_14, x_15, x_16, x_17, x_18, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Expr_mvarId_x21(x_2);
if (x_6 == 0)
{
lean_object* x_23; 
lean_dec(x_13);
lean_dec(x_12);
x_23 = l_Lean_Meta_substCore___lambda__5(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22, x_15, x_16, x_17, x_18, x_21);
return x_23;
}
else
{
lean_object* x_24; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_24 = l_Lean_Meta_clear(x_22, x_12, x_15, x_16, x_17, x_18, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_27 = l_Lean_Meta_clear(x_25, x_13, x_15, x_16, x_17, x_18, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_substCore___lambda__5(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28, x_15, x_16, x_17, x_18, x_29);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
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
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_24);
if (x_35 == 0)
{
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_24);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_17);
x_22 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_2, x_17, x_18, x_19, x_20, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_23);
x_25 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp(x_15, x_23, x_16, x_17, x_18, x_19, x_20, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_substCore___lambda__6(x_3, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_26, x_17, x_18, x_19, x_20, x_27);
lean_dec(x_23);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_array_get_size(x_1);
x_17 = lean_unsigned_to_nat(2u);
x_18 = lean_nat_sub(x_16, x_17);
lean_dec(x_16);
x_19 = 1;
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_20 = l_Lean_Meta_introNCore(x_10, x_18, x_2, x_19, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_array_get_size(x_24);
lean_inc(x_25);
x_26 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__7(x_1, x_24, x_25, x_25, x_3, x_11, x_12, x_13, x_14, x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_25);
lean_dec(x_24);
if (x_4 == 0)
{
uint8_t x_27; 
lean_dec(x_9);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_Meta_FVarSubst_insert(x_28, x_5, x_6);
x_30 = l_Lean_Meta_FVarSubst_insert(x_29, x_7, x_8);
lean_ctor_set(x_21, 0, x_30);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = l_Lean_Meta_FVarSubst_insert(x_31, x_5, x_6);
x_34 = l_Lean_Meta_FVarSubst_insert(x_33, x_7, x_8);
lean_ctor_set(x_21, 0, x_34);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_6);
x_36 = !lean_is_exclusive(x_26);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_26, 0);
x_38 = l_Lean_Meta_FVarSubst_insert(x_37, x_5, x_9);
x_39 = l_Lean_Meta_FVarSubst_insert(x_38, x_7, x_8);
lean_ctor_set(x_21, 0, x_39);
lean_ctor_set(x_26, 0, x_21);
return x_26;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_26, 0);
x_41 = lean_ctor_get(x_26, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_26);
x_42 = l_Lean_Meta_FVarSubst_insert(x_40, x_5, x_9);
x_43 = l_Lean_Meta_FVarSubst_insert(x_42, x_7, x_8);
lean_ctor_set(x_21, 0, x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_21);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_21, 0);
x_46 = lean_ctor_get(x_21, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_21);
x_47 = lean_array_get_size(x_45);
lean_inc(x_47);
x_48 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__7(x_1, x_45, x_47, x_47, x_3, x_11, x_12, x_13, x_14, x_22);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_47);
lean_dec(x_45);
if (x_4 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_9);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_51 = x_48;
} else {
 lean_dec_ref(x_48);
 x_51 = lean_box(0);
}
x_52 = l_Lean_Meta_FVarSubst_insert(x_49, x_5, x_6);
x_53 = l_Lean_Meta_FVarSubst_insert(x_52, x_7, x_8);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_46);
if (lean_is_scalar(x_51)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_51;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_6);
x_56 = lean_ctor_get(x_48, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_58 = x_48;
} else {
 lean_dec_ref(x_48);
 x_58 = lean_box(0);
}
x_59 = l_Lean_Meta_FVarSubst_insert(x_56, x_5, x_9);
x_60 = l_Lean_Meta_FVarSubst_insert(x_59, x_7, x_8);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_46);
if (lean_is_scalar(x_58)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_58;
}
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_57);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_20);
if (x_63 == 0)
{
return x_20;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_20, 0);
x_65 = lean_ctor_get(x_20, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_20);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_0__Lean_Meta_getLevelImp___spec__3(x_1, x_14, x_15, x_16, x_17, x_18, x_19);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Expr_mvarId_x21(x_2);
if (x_6 == 0)
{
lean_object* x_23; 
lean_dec(x_13);
lean_dec(x_12);
x_23 = l_Lean_Meta_substCore___lambda__8(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22, x_15, x_16, x_17, x_18, x_21);
return x_23;
}
else
{
lean_object* x_24; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_24 = l_Lean_Meta_clear(x_22, x_12, x_15, x_16, x_17, x_18, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_27 = l_Lean_Meta_clear(x_25, x_13, x_15, x_16, x_17, x_18, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Meta_substCore___lambda__8(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28, x_15, x_16, x_17, x_18, x_29);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
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
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_24);
if (x_35 == 0)
{
return x_24;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_24, 0);
x_37 = lean_ctor_get(x_24, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_24);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_inc(x_17);
x_22 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_2, x_17, x_18, x_19, x_20, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_23);
x_25 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqRecImp(x_15, x_23, x_16, x_17, x_18, x_19, x_20, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_substCore___lambda__9(x_3, x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_26, x_17, x_18, x_19, x_20, x_27);
lean_dec(x_23);
return x_28;
}
else
{
uint8_t x_29; 
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
return x_25;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_25, 0);
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_25);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__11___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_h");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__11___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_substCore___lambda__11___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__11___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.Tactic.Subst");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__11___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("Lean.Meta.substCore");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__11___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = l_Lean_Meta_substCore___lambda__11___closed__3;
x_2 = l_Lean_Meta_substCore___lambda__11___closed__4;
x_3 = lean_unsigned_to_nat(48u);
x_4 = lean_unsigned_to_nat(20u);
x_5 = l___private_Init_LeanInit_0__Lean_eraseMacroScopesAux___closed__3;
x_6 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
lean_object* l_Lean_Meta_substCore___lambda__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, uint8_t x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20) {
_start:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 2);
lean_inc(x_21);
lean_dec(x_15);
lean_inc(x_16);
lean_inc(x_1);
x_22 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_1, x_16, x_17, x_18, x_19, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_LocalDecl_type(x_23);
lean_dec(x_23);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_26 = l_Lean_Meta_matchEq_x3f(x_25, x_16, x_17, x_18, x_19, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_100 = l___private_Lean_Meta_Basic_0__Lean_Meta_isClassQuick_x3f___closed__1;
x_101 = l_Lean_Meta_substCore___lambda__11___closed__5;
x_102 = lean_panic_fn(x_100, x_101);
x_103 = lean_apply_5(x_102, x_16, x_17, x_18, x_19, x_28);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_27, 0);
lean_inc(x_104);
lean_dec(x_27);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
if (x_13 == 0)
{
lean_object* x_106; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_29 = x_106;
goto block_99;
}
else
{
lean_object* x_107; 
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
lean_dec(x_105);
x_29 = x_107;
goto block_99;
}
}
block_99:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_st_ref_get(x_17, x_28);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_21);
x_34 = l_Lean_MetavarContext_exprDependsOn(x_33, x_21, x_1);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_14);
x_36 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2);
x_37 = lean_array_push(x_36, x_2);
lean_inc(x_16);
lean_inc(x_21);
x_38 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_37, x_21, x_16, x_17, x_18, x_19, x_32);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_2);
x_41 = l_Lean_Expr_replaceFVar(x_21, x_2, x_29);
lean_dec(x_21);
if (x_13 == 0)
{
lean_object* x_42; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_11);
x_42 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(x_11, x_16, x_17, x_18, x_19, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Meta_substCore___lambda__3(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2, x_10, x_11, x_29, x_1, x_12, x_39, x_43, x_16, x_17, x_18, x_19, x_44);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_42);
if (x_46 == 0)
{
return x_42;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; 
lean_inc(x_11);
x_50 = l_Lean_Meta_substCore___lambda__3(x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2, x_10, x_11, x_29, x_1, x_12, x_39, x_11, x_16, x_17, x_18, x_19, x_40);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_29);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_38);
if (x_51 == 0)
{
return x_38;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_38, 0);
x_53 = lean_ctor_get(x_38, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_38);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; 
lean_inc(x_2);
x_55 = l_Lean_Expr_replaceFVar(x_21, x_2, x_29);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_29);
x_56 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqReflImp(x_29, x_16, x_17, x_18, x_19, x_32);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
lean_inc(x_11);
x_59 = l_Lean_Expr_replaceFVar(x_55, x_11, x_57);
lean_dec(x_57);
lean_dec(x_55);
if (x_13 == 0)
{
lean_object* x_60; 
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_2);
lean_inc(x_29);
x_60 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqImp(x_29, x_2, x_16, x_17, x_18, x_19, x_58);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_2);
lean_inc(x_11);
x_63 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__4___boxed), 10, 4);
lean_closure_set(x_63, 0, x_21);
lean_closure_set(x_63, 1, x_11);
lean_closure_set(x_63, 2, x_14);
lean_closure_set(x_63, 3, x_2);
x_64 = l_Lean_Meta_substCore___lambda__11___closed__2;
x_65 = 0;
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
x_66 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg(x_64, x_65, x_61, x_63, x_16, x_17, x_18, x_19, x_62);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_11);
x_69 = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkEqSymmImp(x_11, x_16, x_17, x_18, x_19, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = l_Lean_Meta_substCore___lambda__7(x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2, x_10, x_11, x_29, x_1, x_12, x_67, x_70, x_16, x_17, x_18, x_19, x_71);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec(x_67);
lean_dec(x_59);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_69);
if (x_73 == 0)
{
return x_69;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_69, 0);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_69);
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
lean_dec(x_59);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_66);
if (x_77 == 0)
{
return x_66;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_66, 0);
x_79 = lean_ctor_get(x_66, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_66);
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
lean_dec(x_59);
lean_dec(x_29);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_60);
if (x_81 == 0)
{
return x_60;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_60, 0);
x_83 = lean_ctor_get(x_60, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_60);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_inc(x_2);
x_85 = lean_array_push(x_14, x_2);
lean_inc(x_11);
x_86 = lean_array_push(x_85, x_11);
lean_inc(x_16);
x_87 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_86, x_21, x_16, x_17, x_18, x_19, x_58);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_11);
x_90 = l_Lean_Meta_substCore___lambda__10(x_59, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_2, x_10, x_11, x_29, x_1, x_12, x_88, x_11, x_16, x_17, x_18, x_19, x_89);
return x_90;
}
else
{
uint8_t x_91; 
lean_dec(x_59);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_87);
if (x_91 == 0)
{
return x_87;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_87, 0);
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_87);
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
lean_dec(x_55);
lean_dec(x_29);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_56);
if (x_95 == 0)
{
return x_56;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_56, 0);
x_97 = lean_ctor_get(x_56, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_56);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_108 = !lean_is_exclusive(x_26);
if (x_108 == 0)
{
return x_26;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_26, 0);
x_110 = lean_ctor_get(x_26, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_26);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_22);
if (x_112 == 0)
{
return x_22;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_22, 0);
x_114 = lean_ctor_get(x_22, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_22);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__12___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reverted variables ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__12___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__12___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore___lambda__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_10);
lean_inc(x_1);
x_15 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_1, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_mkAppStx___closed__9;
lean_inc(x_1);
x_18 = lean_array_push(x_17, x_1);
lean_inc(x_2);
x_19 = lean_array_push(x_18, x_2);
x_20 = 1;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_21 = l_Lean_Meta_revert(x_3, x_19, x_20, x_10, x_11, x_12, x_13, x_16);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_26 = lean_box(0);
x_27 = lean_unsigned_to_nat(2u);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_28 = l_Lean_Meta_introNCore(x_25, x_27, x_26, x_20, x_10, x_11, x_12, x_13, x_23);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_48; lean_object* x_49; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_60 = lean_st_ref_get(x_13, x_30);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 3);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_ctor_get_uint8(x_62, sizeof(void*)*1);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
lean_dec(x_60);
x_65 = 0;
x_48 = x_65;
x_49 = x_64;
goto block_59;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
lean_dec(x_60);
lean_inc(x_8);
x_67 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_8, x_10, x_11, x_12, x_13, x_66);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_unbox(x_68);
lean_dec(x_68);
x_48 = x_70;
x_49 = x_69;
goto block_59;
}
block_47:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_34 = l_Lean_Init_LeanInit___instance__1;
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_array_get(x_34, x_31, x_35);
lean_inc(x_36);
x_37 = l_Lean_mkFVar(x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_array_get(x_34, x_31, x_38);
lean_dec(x_31);
lean_inc(x_39);
x_40 = l_Lean_mkFVar(x_39);
lean_inc(x_32);
x_41 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1___boxed), 6, 1);
lean_closure_set(x_41, 0, x_32);
x_42 = lean_box(x_6);
x_43 = lean_box(x_7);
lean_inc(x_32);
x_44 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__11___boxed), 20, 14);
lean_closure_set(x_44, 0, x_39);
lean_closure_set(x_44, 1, x_37);
lean_closure_set(x_44, 2, x_4);
lean_closure_set(x_44, 3, x_32);
lean_closure_set(x_44, 4, x_24);
lean_closure_set(x_44, 5, x_26);
lean_closure_set(x_44, 6, x_5);
lean_closure_set(x_44, 7, x_42);
lean_closure_set(x_44, 8, x_1);
lean_closure_set(x_44, 9, x_2);
lean_closure_set(x_44, 10, x_40);
lean_closure_set(x_44, 11, x_36);
lean_closure_set(x_44, 12, x_43);
lean_closure_set(x_44, 13, x_17);
x_45 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__8___spec__2___rarg), 7, 2);
lean_closure_set(x_45, 0, x_41);
lean_closure_set(x_45, 1, x_44);
x_46 = l_Lean_Meta_withMVarContext___at_Lean_Meta_revert___spec__5___rarg(x_32, x_45, x_10, x_11, x_12, x_13, x_33);
return x_46;
}
block_59:
{
if (x_48 == 0)
{
lean_dec(x_8);
x_33 = x_49;
goto block_47;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = l_Array_toList___rarg(x_24);
x_51 = l_List_map___at_Lean_Meta_substCore___spec__8(x_50);
x_52 = l_Lean_MessageData_ofList(x_51);
lean_dec(x_51);
x_53 = l_Lean_Meta_substCore___lambda__12___closed__2;
x_54 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
x_55 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_56 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_8, x_56, x_10, x_11, x_12, x_13, x_49);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_33 = x_58;
goto block_47;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_28);
if (x_71 == 0)
{
return x_28;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_28, 0);
x_73 = lean_ctor_get(x_28, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_28);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_75 = !lean_is_exclusive(x_21);
if (x_75 == 0)
{
return x_21;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_21, 0);
x_77 = lean_ctor_get(x_21, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_21);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_15);
if (x_79 == 0)
{
return x_15;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_15, 0);
x_81 = lean_ctor_get(x_15, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_15);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("subst");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_substCore___lambda__13___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("argument must be an equality proof");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid equality proof, it is not of the form ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__6;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("\nafter WHNF, variable expected, but obtained");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__8;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(x = t)");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__10;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__7;
x_2 = l_Lean_Meta_substCore___lambda__13___closed__11;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__12;
x_2 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(t = x)");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__14;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__7;
x_2 = l_Lean_Meta_substCore___lambda__13___closed__15;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__16;
x_2 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_3 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Util___hyg_225____closed__2;
x_2 = l_Lean_Meta_substCore___lambda__13___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__19() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' occurs at");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__19;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("substituting ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__21;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__23() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" (id: ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__24() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__23;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__25() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" with ");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lambda__13___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__13___closed__25;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore___lambda__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Meta_substCore___lambda__13___closed__2;
lean_inc(x_1);
x_13 = l_Lean_Meta_checkNotAssigned(x_1, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_2);
x_15 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_2, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_LocalDecl_type(x_16);
lean_dec(x_16);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_18);
x_19 = l_Lean_Meta_matchEq_x3f(x_18, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Meta_substCore___lambda__13___closed__5;
x_23 = lean_box(0);
x_24 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_22, x_23, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_dec(x_26);
if (x_5 == 0)
{
uint8_t x_122; 
x_122 = 0;
x_30 = x_122;
goto block_121;
}
else
{
uint8_t x_123; 
x_123 = 1;
x_30 = x_123;
goto block_121;
}
block_121:
{
lean_object* x_31; 
if (x_30 == 0)
{
lean_inc(x_28);
x_31 = x_28;
goto block_120;
}
else
{
lean_inc(x_29);
x_31 = x_29;
goto block_120;
}
block_120:
{
lean_object* x_32; 
if (x_30 == 0)
{
lean_dec(x_28);
x_32 = x_29;
goto block_119;
}
else
{
lean_dec(x_29);
x_32 = x_28;
goto block_119;
}
block_119:
{
lean_object* x_33; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_33 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_31, x_7, x_8, x_9, x_10, x_27);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 1)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_63; lean_object* x_64; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
lean_dec(x_18);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_82 = lean_st_ref_get(x_10, x_35);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_83, 3);
lean_inc(x_84);
lean_dec(x_83);
x_85 = lean_ctor_get_uint8(x_84, sizeof(void*)*1);
lean_dec(x_84);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
lean_dec(x_82);
x_87 = 0;
x_63 = x_87;
x_64 = x_86;
goto block_81;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_dec(x_82);
x_89 = l_Lean_Meta_substCore___lambda__13___closed__18;
x_90 = l___private_Lean_Util_Trace_0__Lean_checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___spec__2(x_89, x_7, x_8, x_9, x_10, x_88);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_unbox(x_91);
lean_dec(x_91);
x_63 = x_93;
x_64 = x_92;
goto block_81;
}
block_62:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_st_ref_get(x_8, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_32);
x_42 = l_Lean_MetavarContext_exprDependsOn(x_41, x_32, x_36);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_34);
lean_dec(x_32);
x_44 = l_Lean_Meta_substCore___lambda__13___closed__18;
x_45 = lean_box(0);
x_46 = l_Lean_Meta_substCore___lambda__12(x_36, x_2, x_1, x_6, x_3, x_4, x_30, x_44, x_45, x_7, x_8, x_9, x_10, x_40);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
lean_dec(x_36);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_47 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_47, 0, x_34);
x_48 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_49 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Meta_substCore___lambda__13___closed__20;
x_51 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_indentExpr(x_32);
x_53 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_55 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_box(0);
x_57 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_55, x_56, x_7, x_8, x_9, x_10, x_40);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
return x_57;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
block_81:
{
if (x_63 == 0)
{
x_37 = x_64;
goto block_62;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_inc(x_34);
x_65 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_65, 0, x_34);
x_66 = l_Lean_Meta_substCore___lambda__13___closed__22;
x_67 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = l_Lean_Meta_substCore___lambda__13___closed__24;
x_69 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
lean_inc(x_36);
x_70 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_70, 0, x_36);
x_71 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_Meta_substCore___lambda__13___closed__26;
x_73 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
lean_inc(x_32);
x_74 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_74, 0, x_32);
x_75 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
x_76 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_77 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = l_Lean_Meta_substCore___lambda__13___closed__18;
x_79 = l_Lean_addTrace___at_Lean_Meta_isLevelDefEqAux___spec__1(x_78, x_77, x_7, x_8, x_9, x_10, x_64);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_37 = x_80;
goto block_62;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_32);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_94 = lean_ctor_get(x_33, 1);
lean_inc(x_94);
lean_dec(x_33);
x_95 = l_Lean_indentExpr(x_18);
x_96 = l_Lean_indentExpr(x_34);
if (x_30 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_97 = l_Lean_Meta_substCore___lambda__13___closed__13;
x_98 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
x_99 = l_Lean_Meta_substCore___lambda__13___closed__9;
x_100 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_96);
x_102 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_103 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_box(0);
x_105 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_103, x_104, x_7, x_8, x_9, x_10, x_94);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_106 = l_Lean_Meta_substCore___lambda__13___closed__17;
x_107 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_95);
x_108 = l_Lean_Meta_substCore___lambda__13___closed__9;
x_109 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_96);
x_111 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_112 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_box(0);
x_114 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_112, x_113, x_7, x_8, x_9, x_10, x_94);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_32);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_33);
if (x_115 == 0)
{
return x_33;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_33, 0);
x_117 = lean_ctor_get(x_33, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_33);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_19);
if (x_124 == 0)
{
return x_19;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_19, 0);
x_126 = lean_ctor_get(x_19, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_19);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
uint8_t x_128; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_128 = !lean_is_exclusive(x_15);
if (x_128 == 0)
{
return x_15;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_15, 0);
x_130 = lean_ctor_get(x_15, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_15);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
uint8_t x_132; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_132 = !lean_is_exclusive(x_13);
if (x_132 == 0)
{
return x_13;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_13, 0);
x_134 = lean_ctor_get(x_13, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_13);
x_135 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
}
lean_object* l_Lean_Meta_substCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarTag___boxed), 6, 1);
lean_closure_set(x_11, 0, x_1);
x_12 = lean_box(x_5);
x_13 = lean_box(x_3);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__13___boxed), 11, 5);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_4);
lean_closure_set(x_14, 3, x_12);
lean_closure_set(x_14, 4, x_13);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__8___spec__2___rarg), 7, 2);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_15, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_Lean_Meta_withLocalDecl___at_Lean_Meta_substCore___spec__4___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldM_loop___at_Lean_Meta_substCore___spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Meta_substCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l_Lean_Meta_substCore___lambda__1(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1);
return x_17;
}
}
lean_object* l_Lean_Meta_substCore___lambda__2___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_6);
lean_dec(x_6);
x_21 = l_Lean_Meta_substCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
}
lean_object* l_Lean_Meta_substCore___lambda__3___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; lean_object* x_23; 
x_22 = lean_unbox(x_7);
lean_dec(x_7);
x_23 = l_Lean_Meta_substCore___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_4);
return x_23;
}
}
lean_object* l_Lean_Meta_substCore___lambda__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_substCore___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Meta_substCore___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l_Lean_Meta_substCore___lambda__5(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1);
return x_17;
}
}
lean_object* l_Lean_Meta_substCore___lambda__6___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_6);
lean_dec(x_6);
x_21 = l_Lean_Meta_substCore___lambda__6(x_1, x_2, x_3, x_4, x_5, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
}
lean_object* l_Lean_Meta_substCore___lambda__7___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; lean_object* x_23; 
x_22 = lean_unbox(x_7);
lean_dec(x_7);
x_23 = l_Lean_Meta_substCore___lambda__7(x_1, x_2, x_3, x_4, x_5, x_6, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_4);
return x_23;
}
}
lean_object* l_Lean_Meta_substCore___lambda__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = l_Lean_Meta_substCore___lambda__8(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_1);
return x_17;
}
}
lean_object* l_Lean_Meta_substCore___lambda__9___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
_start:
{
uint8_t x_20; lean_object* x_21; 
x_20 = lean_unbox(x_6);
lean_dec(x_6);
x_21 = l_Lean_Meta_substCore___lambda__9(x_1, x_2, x_3, x_4, x_5, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_3);
lean_dec(x_2);
return x_21;
}
}
lean_object* l_Lean_Meta_substCore___lambda__10___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; lean_object* x_23; 
x_22 = lean_unbox(x_7);
lean_dec(x_7);
x_23 = l_Lean_Meta_substCore___lambda__10(x_1, x_2, x_3, x_4, x_5, x_6, x_22, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_4);
return x_23;
}
}
lean_object* l_Lean_Meta_substCore___lambda__11___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
_start:
{
uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_21 = lean_unbox(x_8);
lean_dec(x_8);
x_22 = lean_unbox(x_13);
lean_dec(x_13);
x_23 = l_Lean_Meta_substCore___lambda__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_21, x_9, x_10, x_11, x_12, x_22, x_14, x_15, x_16, x_17, x_18, x_19, x_20);
lean_dec(x_5);
return x_23;
}
}
lean_object* l_Lean_Meta_substCore___lambda__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = lean_unbox(x_7);
lean_dec(x_7);
x_17 = l_Lean_Meta_substCore___lambda__12(x_1, x_2, x_3, x_4, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_9);
return x_17;
}
}
lean_object* l_Lean_Meta_substCore___lambda__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Meta_substCore___lambda__13(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
lean_object* l_Lean_Meta_substCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_substCore(x_1, x_2, x_11, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
lean_object* l_Lean_Meta_subst_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* l_Lean_Meta_subst_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_subst_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_subst_match__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_apply_2(x_2, x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Meta_subst_match__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_subst_match__2___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_subst_match__3___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_apply_3(x_2, x_8, x_9, x_10);
return x_11;
}
}
}
lean_object* l_Lean_Meta_subst_match__3(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_subst_match__3___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_findSomeMAux___at_Lean_Meta_subst___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_4, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_3, x_4);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_15 = l_Std_PersistentArray_findSomeMAux___at_Lean_Meta_subst___spec__3(x_1, x_2, x_14, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_4, x_18);
lean_dec(x_4);
x_4 = x_19;
x_9 = x_17;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_21 = !lean_is_exclusive(x_15);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_15, 0);
lean_dec(x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
}
}
lean_object* l_Array_findSomeMAux___at_Lean_Meta_subst___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_3);
x_18 = lean_nat_dec_lt(x_4, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_array_fget(x_3, x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_box(0);
x_10 = x_22;
x_11 = x_9;
goto block_16;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = l_Lean_LocalDecl_isAuxDecl(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_LocalDecl_type(x_24);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = l_Lean_Meta_matchEq_x3f(x_26, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_free_object(x_21);
lean_dec(x_24);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(0);
x_10 = x_30;
x_11 = x_29;
goto block_16;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_32 = x_28;
} else {
 lean_dec_ref(x_28);
 x_32 = lean_box(0);
}
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_60; 
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_39 = x_34;
} else {
 lean_dec_ref(x_34);
 x_39 = lean_box(0);
}
x_60 = l_Lean_Expr_isFVar(x_38);
if (x_60 == 0)
{
uint8_t x_61; 
lean_dec(x_39);
lean_dec(x_32);
x_61 = l_Lean_Expr_isFVar(x_37);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_38);
lean_dec(x_37);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_24);
x_62 = lean_box(0);
x_10 = x_62;
x_11 = x_36;
goto block_16;
}
else
{
lean_object* x_63; uint8_t x_64; lean_object* x_65; uint8_t x_66; 
x_63 = l_Lean_Expr_fvarId_x21(x_37);
lean_dec(x_37);
x_64 = lean_name_eq(x_63, x_1);
lean_dec(x_63);
lean_inc(x_2);
x_65 = l_Lean_MetavarContext_exprDependsOn(x_2, x_38, x_1);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
if (x_64 == 0)
{
lean_object* x_67; 
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_24);
x_67 = lean_box(0);
x_10 = x_67;
x_11 = x_36;
goto block_16;
}
else
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_68 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_69 = 0;
x_70 = lean_box(x_69);
lean_ctor_set(x_31, 1, x_70);
lean_ctor_set(x_31, 0, x_68);
lean_ctor_set(x_21, 0, x_31);
x_10 = x_21;
x_11 = x_36;
goto block_16;
}
}
else
{
lean_object* x_71; 
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_24);
x_71 = lean_box(0);
x_10 = x_71;
x_11 = x_36;
goto block_16;
}
}
}
else
{
lean_object* x_72; uint8_t x_73; lean_object* x_74; uint8_t x_75; 
x_72 = l_Lean_Expr_fvarId_x21(x_38);
x_73 = lean_name_eq(x_72, x_1);
lean_dec(x_72);
lean_inc(x_37);
lean_inc(x_2);
x_74 = l_Lean_MetavarContext_exprDependsOn(x_2, x_37, x_1);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
if (x_73 == 0)
{
uint8_t x_76; 
lean_dec(x_39);
lean_dec(x_32);
x_76 = l_Lean_Expr_isFVar(x_37);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_38);
lean_dec(x_37);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_24);
x_77 = lean_box(0);
x_10 = x_77;
x_11 = x_36;
goto block_16;
}
else
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; uint8_t x_81; 
x_78 = l_Lean_Expr_fvarId_x21(x_37);
lean_dec(x_37);
x_79 = lean_name_eq(x_78, x_1);
lean_dec(x_78);
lean_inc(x_2);
x_80 = l_Lean_MetavarContext_exprDependsOn(x_2, x_38, x_1);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
if (x_79 == 0)
{
lean_object* x_82; 
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_24);
x_82 = lean_box(0);
x_10 = x_82;
x_11 = x_36;
goto block_16;
}
else
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_83 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_84 = 0;
x_85 = lean_box(x_84);
lean_ctor_set(x_31, 1, x_85);
lean_ctor_set(x_31, 0, x_83);
lean_ctor_set(x_21, 0, x_31);
x_10 = x_21;
x_11 = x_36;
goto block_16;
}
}
else
{
lean_object* x_86; 
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_24);
x_86 = lean_box(0);
x_10 = x_86;
x_11 = x_36;
goto block_16;
}
}
}
else
{
uint8_t x_87; 
lean_free_object(x_31);
lean_free_object(x_21);
x_87 = 1;
x_40 = x_87;
goto block_59;
}
}
else
{
if (x_73 == 0)
{
uint8_t x_88; 
lean_dec(x_39);
lean_dec(x_32);
x_88 = l_Lean_Expr_isFVar(x_37);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_38);
lean_dec(x_37);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_24);
x_89 = lean_box(0);
x_10 = x_89;
x_11 = x_36;
goto block_16;
}
else
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; uint8_t x_93; 
x_90 = l_Lean_Expr_fvarId_x21(x_37);
lean_dec(x_37);
x_91 = lean_name_eq(x_90, x_1);
lean_dec(x_90);
lean_inc(x_2);
x_92 = l_Lean_MetavarContext_exprDependsOn(x_2, x_38, x_1);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
if (x_91 == 0)
{
lean_object* x_94; 
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_24);
x_94 = lean_box(0);
x_10 = x_94;
x_11 = x_36;
goto block_16;
}
else
{
lean_object* x_95; uint8_t x_96; lean_object* x_97; 
x_95 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_96 = 0;
x_97 = lean_box(x_96);
lean_ctor_set(x_31, 1, x_97);
lean_ctor_set(x_31, 0, x_95);
lean_ctor_set(x_21, 0, x_31);
x_10 = x_21;
x_11 = x_36;
goto block_16;
}
}
else
{
lean_object* x_98; 
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_24);
x_98 = lean_box(0);
x_10 = x_98;
x_11 = x_36;
goto block_16;
}
}
}
else
{
uint8_t x_99; 
lean_free_object(x_31);
lean_free_object(x_21);
x_99 = 0;
x_40 = x_99;
goto block_59;
}
}
}
block_59:
{
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Lean_Expr_isFVar(x_37);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_32);
lean_dec(x_24);
x_42 = lean_box(0);
x_10 = x_42;
x_11 = x_36;
goto block_16;
}
else
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; 
x_43 = l_Lean_Expr_fvarId_x21(x_37);
lean_dec(x_37);
x_44 = lean_name_eq(x_43, x_1);
lean_dec(x_43);
lean_inc(x_2);
x_45 = l_Lean_MetavarContext_exprDependsOn(x_2, x_38, x_1);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
if (x_44 == 0)
{
lean_object* x_47; 
lean_dec(x_39);
lean_dec(x_32);
lean_dec(x_24);
x_47 = lean_box(0);
x_10 = x_47;
x_11 = x_36;
goto block_16;
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_49 = 0;
x_50 = lean_box(x_49);
if (lean_is_scalar(x_39)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_39;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
if (lean_is_scalar(x_32)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_32;
}
lean_ctor_set(x_52, 0, x_51);
x_10 = x_52;
x_11 = x_36;
goto block_16;
}
}
else
{
lean_object* x_53; 
lean_dec(x_39);
lean_dec(x_32);
lean_dec(x_24);
x_53 = lean_box(0);
x_10 = x_53;
x_11 = x_36;
goto block_16;
}
}
}
else
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_38);
lean_dec(x_37);
x_54 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_55 = 1;
x_56 = lean_box(x_55);
if (lean_is_scalar(x_39)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_39;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_32)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_32;
}
lean_ctor_set(x_58, 0, x_57);
x_10 = x_58;
x_11 = x_36;
goto block_16;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_125; 
x_100 = lean_ctor_get(x_31, 1);
lean_inc(x_100);
lean_dec(x_31);
x_101 = lean_ctor_get(x_27, 1);
lean_inc(x_101);
lean_dec(x_27);
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_104 = x_100;
} else {
 lean_dec_ref(x_100);
 x_104 = lean_box(0);
}
x_125 = l_Lean_Expr_isFVar(x_103);
if (x_125 == 0)
{
uint8_t x_126; 
lean_dec(x_104);
lean_dec(x_32);
x_126 = l_Lean_Expr_isFVar(x_102);
if (x_126 == 0)
{
lean_object* x_127; 
lean_dec(x_103);
lean_dec(x_102);
lean_free_object(x_21);
lean_dec(x_24);
x_127 = lean_box(0);
x_10 = x_127;
x_11 = x_101;
goto block_16;
}
else
{
lean_object* x_128; uint8_t x_129; lean_object* x_130; uint8_t x_131; 
x_128 = l_Lean_Expr_fvarId_x21(x_102);
lean_dec(x_102);
x_129 = lean_name_eq(x_128, x_1);
lean_dec(x_128);
lean_inc(x_2);
x_130 = l_Lean_MetavarContext_exprDependsOn(x_2, x_103, x_1);
x_131 = lean_unbox(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
if (x_129 == 0)
{
lean_object* x_132; 
lean_free_object(x_21);
lean_dec(x_24);
x_132 = lean_box(0);
x_10 = x_132;
x_11 = x_101;
goto block_16;
}
else
{
lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; 
x_133 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_134 = 0;
x_135 = lean_box(x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_21, 0, x_136);
x_10 = x_21;
x_11 = x_101;
goto block_16;
}
}
else
{
lean_object* x_137; 
lean_free_object(x_21);
lean_dec(x_24);
x_137 = lean_box(0);
x_10 = x_137;
x_11 = x_101;
goto block_16;
}
}
}
else
{
lean_object* x_138; uint8_t x_139; lean_object* x_140; uint8_t x_141; 
x_138 = l_Lean_Expr_fvarId_x21(x_103);
x_139 = lean_name_eq(x_138, x_1);
lean_dec(x_138);
lean_inc(x_102);
lean_inc(x_2);
x_140 = l_Lean_MetavarContext_exprDependsOn(x_2, x_102, x_1);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
if (x_141 == 0)
{
if (x_139 == 0)
{
uint8_t x_142; 
lean_dec(x_104);
lean_dec(x_32);
x_142 = l_Lean_Expr_isFVar(x_102);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_103);
lean_dec(x_102);
lean_free_object(x_21);
lean_dec(x_24);
x_143 = lean_box(0);
x_10 = x_143;
x_11 = x_101;
goto block_16;
}
else
{
lean_object* x_144; uint8_t x_145; lean_object* x_146; uint8_t x_147; 
x_144 = l_Lean_Expr_fvarId_x21(x_102);
lean_dec(x_102);
x_145 = lean_name_eq(x_144, x_1);
lean_dec(x_144);
lean_inc(x_2);
x_146 = l_Lean_MetavarContext_exprDependsOn(x_2, x_103, x_1);
x_147 = lean_unbox(x_146);
lean_dec(x_146);
if (x_147 == 0)
{
if (x_145 == 0)
{
lean_object* x_148; 
lean_free_object(x_21);
lean_dec(x_24);
x_148 = lean_box(0);
x_10 = x_148;
x_11 = x_101;
goto block_16;
}
else
{
lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; 
x_149 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_150 = 0;
x_151 = lean_box(x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_151);
lean_ctor_set(x_21, 0, x_152);
x_10 = x_21;
x_11 = x_101;
goto block_16;
}
}
else
{
lean_object* x_153; 
lean_free_object(x_21);
lean_dec(x_24);
x_153 = lean_box(0);
x_10 = x_153;
x_11 = x_101;
goto block_16;
}
}
}
else
{
uint8_t x_154; 
lean_free_object(x_21);
x_154 = 1;
x_105 = x_154;
goto block_124;
}
}
else
{
if (x_139 == 0)
{
uint8_t x_155; 
lean_dec(x_104);
lean_dec(x_32);
x_155 = l_Lean_Expr_isFVar(x_102);
if (x_155 == 0)
{
lean_object* x_156; 
lean_dec(x_103);
lean_dec(x_102);
lean_free_object(x_21);
lean_dec(x_24);
x_156 = lean_box(0);
x_10 = x_156;
x_11 = x_101;
goto block_16;
}
else
{
lean_object* x_157; uint8_t x_158; lean_object* x_159; uint8_t x_160; 
x_157 = l_Lean_Expr_fvarId_x21(x_102);
lean_dec(x_102);
x_158 = lean_name_eq(x_157, x_1);
lean_dec(x_157);
lean_inc(x_2);
x_159 = l_Lean_MetavarContext_exprDependsOn(x_2, x_103, x_1);
x_160 = lean_unbox(x_159);
lean_dec(x_159);
if (x_160 == 0)
{
if (x_158 == 0)
{
lean_object* x_161; 
lean_free_object(x_21);
lean_dec(x_24);
x_161 = lean_box(0);
x_10 = x_161;
x_11 = x_101;
goto block_16;
}
else
{
lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; 
x_162 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_163 = 0;
x_164 = lean_box(x_163);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_21, 0, x_165);
x_10 = x_21;
x_11 = x_101;
goto block_16;
}
}
else
{
lean_object* x_166; 
lean_free_object(x_21);
lean_dec(x_24);
x_166 = lean_box(0);
x_10 = x_166;
x_11 = x_101;
goto block_16;
}
}
}
else
{
uint8_t x_167; 
lean_free_object(x_21);
x_167 = 0;
x_105 = x_167;
goto block_124;
}
}
}
block_124:
{
if (x_105 == 0)
{
uint8_t x_106; 
x_106 = l_Lean_Expr_isFVar(x_102);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_32);
lean_dec(x_24);
x_107 = lean_box(0);
x_10 = x_107;
x_11 = x_101;
goto block_16;
}
else
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; uint8_t x_111; 
x_108 = l_Lean_Expr_fvarId_x21(x_102);
lean_dec(x_102);
x_109 = lean_name_eq(x_108, x_1);
lean_dec(x_108);
lean_inc(x_2);
x_110 = l_Lean_MetavarContext_exprDependsOn(x_2, x_103, x_1);
x_111 = lean_unbox(x_110);
lean_dec(x_110);
if (x_111 == 0)
{
if (x_109 == 0)
{
lean_object* x_112; 
lean_dec(x_104);
lean_dec(x_32);
lean_dec(x_24);
x_112 = lean_box(0);
x_10 = x_112;
x_11 = x_101;
goto block_16;
}
else
{
lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_114 = 0;
x_115 = lean_box(x_114);
if (lean_is_scalar(x_104)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_104;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_115);
if (lean_is_scalar(x_32)) {
 x_117 = lean_alloc_ctor(1, 1, 0);
} else {
 x_117 = x_32;
}
lean_ctor_set(x_117, 0, x_116);
x_10 = x_117;
x_11 = x_101;
goto block_16;
}
}
else
{
lean_object* x_118; 
lean_dec(x_104);
lean_dec(x_32);
lean_dec(x_24);
x_118 = lean_box(0);
x_10 = x_118;
x_11 = x_101;
goto block_16;
}
}
}
else
{
lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_103);
lean_dec(x_102);
x_119 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_120 = 1;
x_121 = lean_box(x_120);
if (lean_is_scalar(x_104)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_104;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_121);
if (lean_is_scalar(x_32)) {
 x_123 = lean_alloc_ctor(1, 1, 0);
} else {
 x_123 = x_32;
}
lean_ctor_set(x_123, 0, x_122);
x_10 = x_123;
x_11 = x_101;
goto block_16;
}
}
}
}
}
else
{
uint8_t x_168; 
lean_free_object(x_21);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_168 = !lean_is_exclusive(x_27);
if (x_168 == 0)
{
return x_27;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_27, 0);
x_170 = lean_ctor_get(x_27, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_27);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
lean_object* x_172; 
lean_free_object(x_21);
lean_dec(x_24);
x_172 = lean_box(0);
x_10 = x_172;
x_11 = x_9;
goto block_16;
}
}
else
{
lean_object* x_173; uint8_t x_174; 
x_173 = lean_ctor_get(x_21, 0);
lean_inc(x_173);
lean_dec(x_21);
x_174 = l_Lean_LocalDecl_isAuxDecl(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = l_Lean_LocalDecl_type(x_173);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_176 = l_Lean_Meta_matchEq_x3f(x_175, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_173);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_box(0);
x_10 = x_179;
x_11 = x_178;
goto block_16;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; uint8_t x_208; 
x_180 = lean_ctor_get(x_177, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 x_181 = x_177;
} else {
 lean_dec_ref(x_177);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_183 = x_180;
} else {
 lean_dec_ref(x_180);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_176, 1);
lean_inc(x_184);
lean_dec(x_176);
x_185 = lean_ctor_get(x_182, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_182, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_187 = x_182;
} else {
 lean_dec_ref(x_182);
 x_187 = lean_box(0);
}
x_208 = l_Lean_Expr_isFVar(x_186);
if (x_208 == 0)
{
uint8_t x_209; 
lean_dec(x_187);
lean_dec(x_181);
x_209 = l_Lean_Expr_isFVar(x_185);
if (x_209 == 0)
{
lean_object* x_210; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_173);
x_210 = lean_box(0);
x_10 = x_210;
x_11 = x_184;
goto block_16;
}
else
{
lean_object* x_211; uint8_t x_212; lean_object* x_213; uint8_t x_214; 
x_211 = l_Lean_Expr_fvarId_x21(x_185);
lean_dec(x_185);
x_212 = lean_name_eq(x_211, x_1);
lean_dec(x_211);
lean_inc(x_2);
x_213 = l_Lean_MetavarContext_exprDependsOn(x_2, x_186, x_1);
x_214 = lean_unbox(x_213);
lean_dec(x_213);
if (x_214 == 0)
{
if (x_212 == 0)
{
lean_object* x_215; 
lean_dec(x_183);
lean_dec(x_173);
x_215 = lean_box(0);
x_10 = x_215;
x_11 = x_184;
goto block_16;
}
else
{
lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_216 = l_Lean_LocalDecl_fvarId(x_173);
lean_dec(x_173);
x_217 = 0;
x_218 = lean_box(x_217);
if (lean_is_scalar(x_183)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_183;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_219);
x_10 = x_220;
x_11 = x_184;
goto block_16;
}
}
else
{
lean_object* x_221; 
lean_dec(x_183);
lean_dec(x_173);
x_221 = lean_box(0);
x_10 = x_221;
x_11 = x_184;
goto block_16;
}
}
}
else
{
lean_object* x_222; uint8_t x_223; lean_object* x_224; uint8_t x_225; 
x_222 = l_Lean_Expr_fvarId_x21(x_186);
x_223 = lean_name_eq(x_222, x_1);
lean_dec(x_222);
lean_inc(x_185);
lean_inc(x_2);
x_224 = l_Lean_MetavarContext_exprDependsOn(x_2, x_185, x_1);
x_225 = lean_unbox(x_224);
lean_dec(x_224);
if (x_225 == 0)
{
if (x_223 == 0)
{
uint8_t x_226; 
lean_dec(x_187);
lean_dec(x_181);
x_226 = l_Lean_Expr_isFVar(x_185);
if (x_226 == 0)
{
lean_object* x_227; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_173);
x_227 = lean_box(0);
x_10 = x_227;
x_11 = x_184;
goto block_16;
}
else
{
lean_object* x_228; uint8_t x_229; lean_object* x_230; uint8_t x_231; 
x_228 = l_Lean_Expr_fvarId_x21(x_185);
lean_dec(x_185);
x_229 = lean_name_eq(x_228, x_1);
lean_dec(x_228);
lean_inc(x_2);
x_230 = l_Lean_MetavarContext_exprDependsOn(x_2, x_186, x_1);
x_231 = lean_unbox(x_230);
lean_dec(x_230);
if (x_231 == 0)
{
if (x_229 == 0)
{
lean_object* x_232; 
lean_dec(x_183);
lean_dec(x_173);
x_232 = lean_box(0);
x_10 = x_232;
x_11 = x_184;
goto block_16;
}
else
{
lean_object* x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = l_Lean_LocalDecl_fvarId(x_173);
lean_dec(x_173);
x_234 = 0;
x_235 = lean_box(x_234);
if (lean_is_scalar(x_183)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_183;
}
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_236);
x_10 = x_237;
x_11 = x_184;
goto block_16;
}
}
else
{
lean_object* x_238; 
lean_dec(x_183);
lean_dec(x_173);
x_238 = lean_box(0);
x_10 = x_238;
x_11 = x_184;
goto block_16;
}
}
}
else
{
uint8_t x_239; 
lean_dec(x_183);
x_239 = 1;
x_188 = x_239;
goto block_207;
}
}
else
{
if (x_223 == 0)
{
uint8_t x_240; 
lean_dec(x_187);
lean_dec(x_181);
x_240 = l_Lean_Expr_isFVar(x_185);
if (x_240 == 0)
{
lean_object* x_241; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_173);
x_241 = lean_box(0);
x_10 = x_241;
x_11 = x_184;
goto block_16;
}
else
{
lean_object* x_242; uint8_t x_243; lean_object* x_244; uint8_t x_245; 
x_242 = l_Lean_Expr_fvarId_x21(x_185);
lean_dec(x_185);
x_243 = lean_name_eq(x_242, x_1);
lean_dec(x_242);
lean_inc(x_2);
x_244 = l_Lean_MetavarContext_exprDependsOn(x_2, x_186, x_1);
x_245 = lean_unbox(x_244);
lean_dec(x_244);
if (x_245 == 0)
{
if (x_243 == 0)
{
lean_object* x_246; 
lean_dec(x_183);
lean_dec(x_173);
x_246 = lean_box(0);
x_10 = x_246;
x_11 = x_184;
goto block_16;
}
else
{
lean_object* x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_247 = l_Lean_LocalDecl_fvarId(x_173);
lean_dec(x_173);
x_248 = 0;
x_249 = lean_box(x_248);
if (lean_is_scalar(x_183)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_183;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_251, 0, x_250);
x_10 = x_251;
x_11 = x_184;
goto block_16;
}
}
else
{
lean_object* x_252; 
lean_dec(x_183);
lean_dec(x_173);
x_252 = lean_box(0);
x_10 = x_252;
x_11 = x_184;
goto block_16;
}
}
}
else
{
uint8_t x_253; 
lean_dec(x_183);
x_253 = 0;
x_188 = x_253;
goto block_207;
}
}
}
block_207:
{
if (x_188 == 0)
{
uint8_t x_189; 
x_189 = l_Lean_Expr_isFVar(x_185);
if (x_189 == 0)
{
lean_object* x_190; 
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_181);
lean_dec(x_173);
x_190 = lean_box(0);
x_10 = x_190;
x_11 = x_184;
goto block_16;
}
else
{
lean_object* x_191; uint8_t x_192; lean_object* x_193; uint8_t x_194; 
x_191 = l_Lean_Expr_fvarId_x21(x_185);
lean_dec(x_185);
x_192 = lean_name_eq(x_191, x_1);
lean_dec(x_191);
lean_inc(x_2);
x_193 = l_Lean_MetavarContext_exprDependsOn(x_2, x_186, x_1);
x_194 = lean_unbox(x_193);
lean_dec(x_193);
if (x_194 == 0)
{
if (x_192 == 0)
{
lean_object* x_195; 
lean_dec(x_187);
lean_dec(x_181);
lean_dec(x_173);
x_195 = lean_box(0);
x_10 = x_195;
x_11 = x_184;
goto block_16;
}
else
{
lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = l_Lean_LocalDecl_fvarId(x_173);
lean_dec(x_173);
x_197 = 0;
x_198 = lean_box(x_197);
if (lean_is_scalar(x_187)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_187;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_198);
if (lean_is_scalar(x_181)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_181;
}
lean_ctor_set(x_200, 0, x_199);
x_10 = x_200;
x_11 = x_184;
goto block_16;
}
}
else
{
lean_object* x_201; 
lean_dec(x_187);
lean_dec(x_181);
lean_dec(x_173);
x_201 = lean_box(0);
x_10 = x_201;
x_11 = x_184;
goto block_16;
}
}
}
else
{
lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_186);
lean_dec(x_185);
x_202 = l_Lean_LocalDecl_fvarId(x_173);
lean_dec(x_173);
x_203 = 1;
x_204 = lean_box(x_203);
if (lean_is_scalar(x_187)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_187;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_204);
if (lean_is_scalar(x_181)) {
 x_206 = lean_alloc_ctor(1, 1, 0);
} else {
 x_206 = x_181;
}
lean_ctor_set(x_206, 0, x_205);
x_10 = x_206;
x_11 = x_184;
goto block_16;
}
}
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_173);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_254 = lean_ctor_get(x_176, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_176, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_256 = x_176;
} else {
 lean_dec_ref(x_176);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
else
{
lean_object* x_258; 
lean_dec(x_173);
x_258 = lean_box(0);
x_10 = x_258;
x_11 = x_9;
goto block_16;
}
}
}
}
block_16:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_4 = x_13;
x_9 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
}
lean_object* l_Std_PersistentArray_findSomeMAux___at_Lean_Meta_subst___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_findSomeMAux___at_Lean_Meta_subst___spec__4(x_1, x_2, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_Array_findSomeMAux___at_Lean_Meta_subst___spec__5(x_1, x_2, x_12, x_13, x_4, x_5, x_6, x_7, x_8);
return x_14;
}
}
}
lean_object* l_Array_findSomeMAux___at_Lean_Meta_subst___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_3);
x_18 = lean_nat_dec_lt(x_4, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
else
{
lean_object* x_21; 
x_21 = lean_array_fget(x_3, x_4);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_box(0);
x_10 = x_22;
x_11 = x_9;
goto block_16;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = l_Lean_LocalDecl_isAuxDecl(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = l_Lean_LocalDecl_type(x_24);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = l_Lean_Meta_matchEq_x3f(x_26, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_free_object(x_21);
lean_dec(x_24);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(0);
x_10 = x_30;
x_11 = x_29;
goto block_16;
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_28, 0);
lean_inc(x_31);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 x_32 = x_28;
} else {
 lean_dec_ref(x_28);
 x_32 = lean_box(0);
}
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_60; 
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_ctor_get(x_31, 0);
lean_dec(x_35);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_dec(x_27);
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_34)) {
 lean_ctor_release(x_34, 0);
 lean_ctor_release(x_34, 1);
 x_39 = x_34;
} else {
 lean_dec_ref(x_34);
 x_39 = lean_box(0);
}
x_60 = l_Lean_Expr_isFVar(x_38);
if (x_60 == 0)
{
uint8_t x_61; 
lean_dec(x_39);
lean_dec(x_32);
x_61 = l_Lean_Expr_isFVar(x_37);
if (x_61 == 0)
{
lean_object* x_62; 
lean_dec(x_38);
lean_dec(x_37);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_24);
x_62 = lean_box(0);
x_10 = x_62;
x_11 = x_36;
goto block_16;
}
else
{
lean_object* x_63; uint8_t x_64; lean_object* x_65; uint8_t x_66; 
x_63 = l_Lean_Expr_fvarId_x21(x_37);
lean_dec(x_37);
x_64 = lean_name_eq(x_63, x_1);
lean_dec(x_63);
lean_inc(x_2);
x_65 = l_Lean_MetavarContext_exprDependsOn(x_2, x_38, x_1);
x_66 = lean_unbox(x_65);
lean_dec(x_65);
if (x_66 == 0)
{
if (x_64 == 0)
{
lean_object* x_67; 
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_24);
x_67 = lean_box(0);
x_10 = x_67;
x_11 = x_36;
goto block_16;
}
else
{
lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_68 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_69 = 0;
x_70 = lean_box(x_69);
lean_ctor_set(x_31, 1, x_70);
lean_ctor_set(x_31, 0, x_68);
lean_ctor_set(x_21, 0, x_31);
x_10 = x_21;
x_11 = x_36;
goto block_16;
}
}
else
{
lean_object* x_71; 
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_24);
x_71 = lean_box(0);
x_10 = x_71;
x_11 = x_36;
goto block_16;
}
}
}
else
{
lean_object* x_72; uint8_t x_73; lean_object* x_74; uint8_t x_75; 
x_72 = l_Lean_Expr_fvarId_x21(x_38);
x_73 = lean_name_eq(x_72, x_1);
lean_dec(x_72);
lean_inc(x_37);
lean_inc(x_2);
x_74 = l_Lean_MetavarContext_exprDependsOn(x_2, x_37, x_1);
x_75 = lean_unbox(x_74);
lean_dec(x_74);
if (x_75 == 0)
{
if (x_73 == 0)
{
uint8_t x_76; 
lean_dec(x_39);
lean_dec(x_32);
x_76 = l_Lean_Expr_isFVar(x_37);
if (x_76 == 0)
{
lean_object* x_77; 
lean_dec(x_38);
lean_dec(x_37);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_24);
x_77 = lean_box(0);
x_10 = x_77;
x_11 = x_36;
goto block_16;
}
else
{
lean_object* x_78; uint8_t x_79; lean_object* x_80; uint8_t x_81; 
x_78 = l_Lean_Expr_fvarId_x21(x_37);
lean_dec(x_37);
x_79 = lean_name_eq(x_78, x_1);
lean_dec(x_78);
lean_inc(x_2);
x_80 = l_Lean_MetavarContext_exprDependsOn(x_2, x_38, x_1);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
if (x_79 == 0)
{
lean_object* x_82; 
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_24);
x_82 = lean_box(0);
x_10 = x_82;
x_11 = x_36;
goto block_16;
}
else
{
lean_object* x_83; uint8_t x_84; lean_object* x_85; 
x_83 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_84 = 0;
x_85 = lean_box(x_84);
lean_ctor_set(x_31, 1, x_85);
lean_ctor_set(x_31, 0, x_83);
lean_ctor_set(x_21, 0, x_31);
x_10 = x_21;
x_11 = x_36;
goto block_16;
}
}
else
{
lean_object* x_86; 
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_24);
x_86 = lean_box(0);
x_10 = x_86;
x_11 = x_36;
goto block_16;
}
}
}
else
{
uint8_t x_87; 
lean_free_object(x_31);
lean_free_object(x_21);
x_87 = 1;
x_40 = x_87;
goto block_59;
}
}
else
{
if (x_73 == 0)
{
uint8_t x_88; 
lean_dec(x_39);
lean_dec(x_32);
x_88 = l_Lean_Expr_isFVar(x_37);
if (x_88 == 0)
{
lean_object* x_89; 
lean_dec(x_38);
lean_dec(x_37);
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_24);
x_89 = lean_box(0);
x_10 = x_89;
x_11 = x_36;
goto block_16;
}
else
{
lean_object* x_90; uint8_t x_91; lean_object* x_92; uint8_t x_93; 
x_90 = l_Lean_Expr_fvarId_x21(x_37);
lean_dec(x_37);
x_91 = lean_name_eq(x_90, x_1);
lean_dec(x_90);
lean_inc(x_2);
x_92 = l_Lean_MetavarContext_exprDependsOn(x_2, x_38, x_1);
x_93 = lean_unbox(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
if (x_91 == 0)
{
lean_object* x_94; 
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_24);
x_94 = lean_box(0);
x_10 = x_94;
x_11 = x_36;
goto block_16;
}
else
{
lean_object* x_95; uint8_t x_96; lean_object* x_97; 
x_95 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_96 = 0;
x_97 = lean_box(x_96);
lean_ctor_set(x_31, 1, x_97);
lean_ctor_set(x_31, 0, x_95);
lean_ctor_set(x_21, 0, x_31);
x_10 = x_21;
x_11 = x_36;
goto block_16;
}
}
else
{
lean_object* x_98; 
lean_free_object(x_31);
lean_free_object(x_21);
lean_dec(x_24);
x_98 = lean_box(0);
x_10 = x_98;
x_11 = x_36;
goto block_16;
}
}
}
else
{
uint8_t x_99; 
lean_free_object(x_31);
lean_free_object(x_21);
x_99 = 0;
x_40 = x_99;
goto block_59;
}
}
}
block_59:
{
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = l_Lean_Expr_isFVar(x_37);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_32);
lean_dec(x_24);
x_42 = lean_box(0);
x_10 = x_42;
x_11 = x_36;
goto block_16;
}
else
{
lean_object* x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; 
x_43 = l_Lean_Expr_fvarId_x21(x_37);
lean_dec(x_37);
x_44 = lean_name_eq(x_43, x_1);
lean_dec(x_43);
lean_inc(x_2);
x_45 = l_Lean_MetavarContext_exprDependsOn(x_2, x_38, x_1);
x_46 = lean_unbox(x_45);
lean_dec(x_45);
if (x_46 == 0)
{
if (x_44 == 0)
{
lean_object* x_47; 
lean_dec(x_39);
lean_dec(x_32);
lean_dec(x_24);
x_47 = lean_box(0);
x_10 = x_47;
x_11 = x_36;
goto block_16;
}
else
{
lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_49 = 0;
x_50 = lean_box(x_49);
if (lean_is_scalar(x_39)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_39;
}
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
if (lean_is_scalar(x_32)) {
 x_52 = lean_alloc_ctor(1, 1, 0);
} else {
 x_52 = x_32;
}
lean_ctor_set(x_52, 0, x_51);
x_10 = x_52;
x_11 = x_36;
goto block_16;
}
}
else
{
lean_object* x_53; 
lean_dec(x_39);
lean_dec(x_32);
lean_dec(x_24);
x_53 = lean_box(0);
x_10 = x_53;
x_11 = x_36;
goto block_16;
}
}
}
else
{
lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_38);
lean_dec(x_37);
x_54 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_55 = 1;
x_56 = lean_box(x_55);
if (lean_is_scalar(x_39)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_39;
}
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
if (lean_is_scalar(x_32)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_32;
}
lean_ctor_set(x_58, 0, x_57);
x_10 = x_58;
x_11 = x_36;
goto block_16;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_125; 
x_100 = lean_ctor_get(x_31, 1);
lean_inc(x_100);
lean_dec(x_31);
x_101 = lean_ctor_get(x_27, 1);
lean_inc(x_101);
lean_dec(x_27);
x_102 = lean_ctor_get(x_100, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_104 = x_100;
} else {
 lean_dec_ref(x_100);
 x_104 = lean_box(0);
}
x_125 = l_Lean_Expr_isFVar(x_103);
if (x_125 == 0)
{
uint8_t x_126; 
lean_dec(x_104);
lean_dec(x_32);
x_126 = l_Lean_Expr_isFVar(x_102);
if (x_126 == 0)
{
lean_object* x_127; 
lean_dec(x_103);
lean_dec(x_102);
lean_free_object(x_21);
lean_dec(x_24);
x_127 = lean_box(0);
x_10 = x_127;
x_11 = x_101;
goto block_16;
}
else
{
lean_object* x_128; uint8_t x_129; lean_object* x_130; uint8_t x_131; 
x_128 = l_Lean_Expr_fvarId_x21(x_102);
lean_dec(x_102);
x_129 = lean_name_eq(x_128, x_1);
lean_dec(x_128);
lean_inc(x_2);
x_130 = l_Lean_MetavarContext_exprDependsOn(x_2, x_103, x_1);
x_131 = lean_unbox(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
if (x_129 == 0)
{
lean_object* x_132; 
lean_free_object(x_21);
lean_dec(x_24);
x_132 = lean_box(0);
x_10 = x_132;
x_11 = x_101;
goto block_16;
}
else
{
lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; 
x_133 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_134 = 0;
x_135 = lean_box(x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
lean_ctor_set(x_21, 0, x_136);
x_10 = x_21;
x_11 = x_101;
goto block_16;
}
}
else
{
lean_object* x_137; 
lean_free_object(x_21);
lean_dec(x_24);
x_137 = lean_box(0);
x_10 = x_137;
x_11 = x_101;
goto block_16;
}
}
}
else
{
lean_object* x_138; uint8_t x_139; lean_object* x_140; uint8_t x_141; 
x_138 = l_Lean_Expr_fvarId_x21(x_103);
x_139 = lean_name_eq(x_138, x_1);
lean_dec(x_138);
lean_inc(x_102);
lean_inc(x_2);
x_140 = l_Lean_MetavarContext_exprDependsOn(x_2, x_102, x_1);
x_141 = lean_unbox(x_140);
lean_dec(x_140);
if (x_141 == 0)
{
if (x_139 == 0)
{
uint8_t x_142; 
lean_dec(x_104);
lean_dec(x_32);
x_142 = l_Lean_Expr_isFVar(x_102);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_103);
lean_dec(x_102);
lean_free_object(x_21);
lean_dec(x_24);
x_143 = lean_box(0);
x_10 = x_143;
x_11 = x_101;
goto block_16;
}
else
{
lean_object* x_144; uint8_t x_145; lean_object* x_146; uint8_t x_147; 
x_144 = l_Lean_Expr_fvarId_x21(x_102);
lean_dec(x_102);
x_145 = lean_name_eq(x_144, x_1);
lean_dec(x_144);
lean_inc(x_2);
x_146 = l_Lean_MetavarContext_exprDependsOn(x_2, x_103, x_1);
x_147 = lean_unbox(x_146);
lean_dec(x_146);
if (x_147 == 0)
{
if (x_145 == 0)
{
lean_object* x_148; 
lean_free_object(x_21);
lean_dec(x_24);
x_148 = lean_box(0);
x_10 = x_148;
x_11 = x_101;
goto block_16;
}
else
{
lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; 
x_149 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_150 = 0;
x_151 = lean_box(x_150);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_151);
lean_ctor_set(x_21, 0, x_152);
x_10 = x_21;
x_11 = x_101;
goto block_16;
}
}
else
{
lean_object* x_153; 
lean_free_object(x_21);
lean_dec(x_24);
x_153 = lean_box(0);
x_10 = x_153;
x_11 = x_101;
goto block_16;
}
}
}
else
{
uint8_t x_154; 
lean_free_object(x_21);
x_154 = 1;
x_105 = x_154;
goto block_124;
}
}
else
{
if (x_139 == 0)
{
uint8_t x_155; 
lean_dec(x_104);
lean_dec(x_32);
x_155 = l_Lean_Expr_isFVar(x_102);
if (x_155 == 0)
{
lean_object* x_156; 
lean_dec(x_103);
lean_dec(x_102);
lean_free_object(x_21);
lean_dec(x_24);
x_156 = lean_box(0);
x_10 = x_156;
x_11 = x_101;
goto block_16;
}
else
{
lean_object* x_157; uint8_t x_158; lean_object* x_159; uint8_t x_160; 
x_157 = l_Lean_Expr_fvarId_x21(x_102);
lean_dec(x_102);
x_158 = lean_name_eq(x_157, x_1);
lean_dec(x_157);
lean_inc(x_2);
x_159 = l_Lean_MetavarContext_exprDependsOn(x_2, x_103, x_1);
x_160 = lean_unbox(x_159);
lean_dec(x_159);
if (x_160 == 0)
{
if (x_158 == 0)
{
lean_object* x_161; 
lean_free_object(x_21);
lean_dec(x_24);
x_161 = lean_box(0);
x_10 = x_161;
x_11 = x_101;
goto block_16;
}
else
{
lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; 
x_162 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_163 = 0;
x_164 = lean_box(x_163);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_164);
lean_ctor_set(x_21, 0, x_165);
x_10 = x_21;
x_11 = x_101;
goto block_16;
}
}
else
{
lean_object* x_166; 
lean_free_object(x_21);
lean_dec(x_24);
x_166 = lean_box(0);
x_10 = x_166;
x_11 = x_101;
goto block_16;
}
}
}
else
{
uint8_t x_167; 
lean_free_object(x_21);
x_167 = 0;
x_105 = x_167;
goto block_124;
}
}
}
block_124:
{
if (x_105 == 0)
{
uint8_t x_106; 
x_106 = l_Lean_Expr_isFVar(x_102);
if (x_106 == 0)
{
lean_object* x_107; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_32);
lean_dec(x_24);
x_107 = lean_box(0);
x_10 = x_107;
x_11 = x_101;
goto block_16;
}
else
{
lean_object* x_108; uint8_t x_109; lean_object* x_110; uint8_t x_111; 
x_108 = l_Lean_Expr_fvarId_x21(x_102);
lean_dec(x_102);
x_109 = lean_name_eq(x_108, x_1);
lean_dec(x_108);
lean_inc(x_2);
x_110 = l_Lean_MetavarContext_exprDependsOn(x_2, x_103, x_1);
x_111 = lean_unbox(x_110);
lean_dec(x_110);
if (x_111 == 0)
{
if (x_109 == 0)
{
lean_object* x_112; 
lean_dec(x_104);
lean_dec(x_32);
lean_dec(x_24);
x_112 = lean_box(0);
x_10 = x_112;
x_11 = x_101;
goto block_16;
}
else
{
lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_113 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_114 = 0;
x_115 = lean_box(x_114);
if (lean_is_scalar(x_104)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_104;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_115);
if (lean_is_scalar(x_32)) {
 x_117 = lean_alloc_ctor(1, 1, 0);
} else {
 x_117 = x_32;
}
lean_ctor_set(x_117, 0, x_116);
x_10 = x_117;
x_11 = x_101;
goto block_16;
}
}
else
{
lean_object* x_118; 
lean_dec(x_104);
lean_dec(x_32);
lean_dec(x_24);
x_118 = lean_box(0);
x_10 = x_118;
x_11 = x_101;
goto block_16;
}
}
}
else
{
lean_object* x_119; uint8_t x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_103);
lean_dec(x_102);
x_119 = l_Lean_LocalDecl_fvarId(x_24);
lean_dec(x_24);
x_120 = 1;
x_121 = lean_box(x_120);
if (lean_is_scalar(x_104)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_104;
}
lean_ctor_set(x_122, 0, x_119);
lean_ctor_set(x_122, 1, x_121);
if (lean_is_scalar(x_32)) {
 x_123 = lean_alloc_ctor(1, 1, 0);
} else {
 x_123 = x_32;
}
lean_ctor_set(x_123, 0, x_122);
x_10 = x_123;
x_11 = x_101;
goto block_16;
}
}
}
}
}
else
{
uint8_t x_168; 
lean_free_object(x_21);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_168 = !lean_is_exclusive(x_27);
if (x_168 == 0)
{
return x_27;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_27, 0);
x_170 = lean_ctor_get(x_27, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_27);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
lean_object* x_172; 
lean_free_object(x_21);
lean_dec(x_24);
x_172 = lean_box(0);
x_10 = x_172;
x_11 = x_9;
goto block_16;
}
}
else
{
lean_object* x_173; uint8_t x_174; 
x_173 = lean_ctor_get(x_21, 0);
lean_inc(x_173);
lean_dec(x_21);
x_174 = l_Lean_LocalDecl_isAuxDecl(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = l_Lean_LocalDecl_type(x_173);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_176 = l_Lean_Meta_matchEq_x3f(x_175, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
if (lean_obj_tag(x_177) == 0)
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_173);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
x_179 = lean_box(0);
x_10 = x_179;
x_11 = x_178;
goto block_16;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; uint8_t x_208; 
x_180 = lean_ctor_get(x_177, 0);
lean_inc(x_180);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 x_181 = x_177;
} else {
 lean_dec_ref(x_177);
 x_181 = lean_box(0);
}
x_182 = lean_ctor_get(x_180, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_183 = x_180;
} else {
 lean_dec_ref(x_180);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_176, 1);
lean_inc(x_184);
lean_dec(x_176);
x_185 = lean_ctor_get(x_182, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_182, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 x_187 = x_182;
} else {
 lean_dec_ref(x_182);
 x_187 = lean_box(0);
}
x_208 = l_Lean_Expr_isFVar(x_186);
if (x_208 == 0)
{
uint8_t x_209; 
lean_dec(x_187);
lean_dec(x_181);
x_209 = l_Lean_Expr_isFVar(x_185);
if (x_209 == 0)
{
lean_object* x_210; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_173);
x_210 = lean_box(0);
x_10 = x_210;
x_11 = x_184;
goto block_16;
}
else
{
lean_object* x_211; uint8_t x_212; lean_object* x_213; uint8_t x_214; 
x_211 = l_Lean_Expr_fvarId_x21(x_185);
lean_dec(x_185);
x_212 = lean_name_eq(x_211, x_1);
lean_dec(x_211);
lean_inc(x_2);
x_213 = l_Lean_MetavarContext_exprDependsOn(x_2, x_186, x_1);
x_214 = lean_unbox(x_213);
lean_dec(x_213);
if (x_214 == 0)
{
if (x_212 == 0)
{
lean_object* x_215; 
lean_dec(x_183);
lean_dec(x_173);
x_215 = lean_box(0);
x_10 = x_215;
x_11 = x_184;
goto block_16;
}
else
{
lean_object* x_216; uint8_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_216 = l_Lean_LocalDecl_fvarId(x_173);
lean_dec(x_173);
x_217 = 0;
x_218 = lean_box(x_217);
if (lean_is_scalar(x_183)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_183;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_219);
x_10 = x_220;
x_11 = x_184;
goto block_16;
}
}
else
{
lean_object* x_221; 
lean_dec(x_183);
lean_dec(x_173);
x_221 = lean_box(0);
x_10 = x_221;
x_11 = x_184;
goto block_16;
}
}
}
else
{
lean_object* x_222; uint8_t x_223; lean_object* x_224; uint8_t x_225; 
x_222 = l_Lean_Expr_fvarId_x21(x_186);
x_223 = lean_name_eq(x_222, x_1);
lean_dec(x_222);
lean_inc(x_185);
lean_inc(x_2);
x_224 = l_Lean_MetavarContext_exprDependsOn(x_2, x_185, x_1);
x_225 = lean_unbox(x_224);
lean_dec(x_224);
if (x_225 == 0)
{
if (x_223 == 0)
{
uint8_t x_226; 
lean_dec(x_187);
lean_dec(x_181);
x_226 = l_Lean_Expr_isFVar(x_185);
if (x_226 == 0)
{
lean_object* x_227; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_173);
x_227 = lean_box(0);
x_10 = x_227;
x_11 = x_184;
goto block_16;
}
else
{
lean_object* x_228; uint8_t x_229; lean_object* x_230; uint8_t x_231; 
x_228 = l_Lean_Expr_fvarId_x21(x_185);
lean_dec(x_185);
x_229 = lean_name_eq(x_228, x_1);
lean_dec(x_228);
lean_inc(x_2);
x_230 = l_Lean_MetavarContext_exprDependsOn(x_2, x_186, x_1);
x_231 = lean_unbox(x_230);
lean_dec(x_230);
if (x_231 == 0)
{
if (x_229 == 0)
{
lean_object* x_232; 
lean_dec(x_183);
lean_dec(x_173);
x_232 = lean_box(0);
x_10 = x_232;
x_11 = x_184;
goto block_16;
}
else
{
lean_object* x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = l_Lean_LocalDecl_fvarId(x_173);
lean_dec(x_173);
x_234 = 0;
x_235 = lean_box(x_234);
if (lean_is_scalar(x_183)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_183;
}
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_236);
x_10 = x_237;
x_11 = x_184;
goto block_16;
}
}
else
{
lean_object* x_238; 
lean_dec(x_183);
lean_dec(x_173);
x_238 = lean_box(0);
x_10 = x_238;
x_11 = x_184;
goto block_16;
}
}
}
else
{
uint8_t x_239; 
lean_dec(x_183);
x_239 = 1;
x_188 = x_239;
goto block_207;
}
}
else
{
if (x_223 == 0)
{
uint8_t x_240; 
lean_dec(x_187);
lean_dec(x_181);
x_240 = l_Lean_Expr_isFVar(x_185);
if (x_240 == 0)
{
lean_object* x_241; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_183);
lean_dec(x_173);
x_241 = lean_box(0);
x_10 = x_241;
x_11 = x_184;
goto block_16;
}
else
{
lean_object* x_242; uint8_t x_243; lean_object* x_244; uint8_t x_245; 
x_242 = l_Lean_Expr_fvarId_x21(x_185);
lean_dec(x_185);
x_243 = lean_name_eq(x_242, x_1);
lean_dec(x_242);
lean_inc(x_2);
x_244 = l_Lean_MetavarContext_exprDependsOn(x_2, x_186, x_1);
x_245 = lean_unbox(x_244);
lean_dec(x_244);
if (x_245 == 0)
{
if (x_243 == 0)
{
lean_object* x_246; 
lean_dec(x_183);
lean_dec(x_173);
x_246 = lean_box(0);
x_10 = x_246;
x_11 = x_184;
goto block_16;
}
else
{
lean_object* x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_247 = l_Lean_LocalDecl_fvarId(x_173);
lean_dec(x_173);
x_248 = 0;
x_249 = lean_box(x_248);
if (lean_is_scalar(x_183)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_183;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_251, 0, x_250);
x_10 = x_251;
x_11 = x_184;
goto block_16;
}
}
else
{
lean_object* x_252; 
lean_dec(x_183);
lean_dec(x_173);
x_252 = lean_box(0);
x_10 = x_252;
x_11 = x_184;
goto block_16;
}
}
}
else
{
uint8_t x_253; 
lean_dec(x_183);
x_253 = 0;
x_188 = x_253;
goto block_207;
}
}
}
block_207:
{
if (x_188 == 0)
{
uint8_t x_189; 
x_189 = l_Lean_Expr_isFVar(x_185);
if (x_189 == 0)
{
lean_object* x_190; 
lean_dec(x_187);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_181);
lean_dec(x_173);
x_190 = lean_box(0);
x_10 = x_190;
x_11 = x_184;
goto block_16;
}
else
{
lean_object* x_191; uint8_t x_192; lean_object* x_193; uint8_t x_194; 
x_191 = l_Lean_Expr_fvarId_x21(x_185);
lean_dec(x_185);
x_192 = lean_name_eq(x_191, x_1);
lean_dec(x_191);
lean_inc(x_2);
x_193 = l_Lean_MetavarContext_exprDependsOn(x_2, x_186, x_1);
x_194 = lean_unbox(x_193);
lean_dec(x_193);
if (x_194 == 0)
{
if (x_192 == 0)
{
lean_object* x_195; 
lean_dec(x_187);
lean_dec(x_181);
lean_dec(x_173);
x_195 = lean_box(0);
x_10 = x_195;
x_11 = x_184;
goto block_16;
}
else
{
lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = l_Lean_LocalDecl_fvarId(x_173);
lean_dec(x_173);
x_197 = 0;
x_198 = lean_box(x_197);
if (lean_is_scalar(x_187)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_187;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_198);
if (lean_is_scalar(x_181)) {
 x_200 = lean_alloc_ctor(1, 1, 0);
} else {
 x_200 = x_181;
}
lean_ctor_set(x_200, 0, x_199);
x_10 = x_200;
x_11 = x_184;
goto block_16;
}
}
else
{
lean_object* x_201; 
lean_dec(x_187);
lean_dec(x_181);
lean_dec(x_173);
x_201 = lean_box(0);
x_10 = x_201;
x_11 = x_184;
goto block_16;
}
}
}
else
{
lean_object* x_202; uint8_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_186);
lean_dec(x_185);
x_202 = l_Lean_LocalDecl_fvarId(x_173);
lean_dec(x_173);
x_203 = 1;
x_204 = lean_box(x_203);
if (lean_is_scalar(x_187)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_187;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_204);
if (lean_is_scalar(x_181)) {
 x_206 = lean_alloc_ctor(1, 1, 0);
} else {
 x_206 = x_181;
}
lean_ctor_set(x_206, 0, x_205);
x_10 = x_206;
x_11 = x_184;
goto block_16;
}
}
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_173);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_254 = lean_ctor_get(x_176, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_176, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_256 = x_176;
} else {
 lean_dec_ref(x_176);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
else
{
lean_object* x_258; 
lean_dec(x_173);
x_258 = lean_box(0);
x_10 = x_258;
x_11 = x_9;
goto block_16;
}
}
}
}
block_16:
{
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_4, x_12);
lean_dec(x_4);
x_4 = x_13;
x_9 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
}
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_10 = l_Std_PersistentArray_findSomeMAux___at_Lean_Meta_subst___spec__3(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_findSomeMAux___at_Lean_Meta_subst___spec__6(x_1, x_2, x_13, x_14, x_4, x_5, x_6, x_7, x_12);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_16 = !lean_is_exclusive(x_10);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_10, 0);
lean_dec(x_17);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 x_23 = x_11;
} else {
 lean_dec_ref(x_11);
 x_23 = lean_box(0);
}
if (lean_is_scalar(x_23)) {
 x_24 = lean_alloc_ctor(1, 1, 0);
} else {
 x_24 = x_23;
}
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_3, 1);
x_10 = l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("did not find equation for eliminating '");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_subst___lambda__1___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid equality proof, it is not of the form (x = t) or (t = x)");
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_subst___lambda__1___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_subst___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_LocalDecl_type(x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_9);
x_10 = l_Lean_Meta_matchEq_x3f(x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_get(x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_18 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(x_1, x_16, x_17, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_mkFVar(x_1);
x_22 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_Meta_subst___lambda__1___closed__2;
x_24 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_throwUnknownConstant___rarg___closed__3;
x_26 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Meta_substCore___lambda__13___closed__2;
x_28 = lean_box(0);
x_29 = l_Lean_Meta_throwTacticEx___rarg(x_27, x_2, x_26, x_28, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
lean_dec(x_1);
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_ctor_get(x_18, 1);
lean_inc(x_31);
lean_dec(x_18);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_box(0);
x_35 = 1;
x_36 = lean_unbox(x_33);
lean_dec(x_33);
x_37 = l_Lean_Meta_substCore(x_2, x_32, x_36, x_34, x_35, x_4, x_5, x_6, x_7, x_31);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_37, 0);
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_37);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_18);
if (x_49 == 0)
{
return x_18;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_18, 0);
x_51 = lean_ctor_get(x_18, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_18);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_11, 0);
lean_inc(x_53);
lean_dec(x_11);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_ctor_get(x_10, 1);
lean_inc(x_55);
lean_dec(x_10);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_58 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_57, x_4, x_5, x_6, x_7, x_55);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Expr_isFVar(x_59);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_62 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassExpensive_x3f___spec__2(x_56, x_4, x_5, x_6, x_7, x_60);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_Lean_Expr_isFVar(x_63);
lean_dec(x_63);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_1);
x_66 = l_Lean_indentExpr(x_9);
x_67 = l_Lean_Meta_subst___lambda__1___closed__4;
x_68 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_66);
x_69 = l_Array_iterateMAux___at_Lean_withNestedTraces___spec__5___closed__1;
x_70 = lean_alloc_ctor(10, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Meta_substCore___lambda__13___closed__2;
x_72 = lean_box(0);
x_73 = l_Lean_Meta_throwTacticEx___rarg(x_71, x_2, x_70, x_72, x_4, x_5, x_6, x_7, x_64);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_73;
}
else
{
lean_object* x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; 
lean_dec(x_9);
x_74 = lean_box(0);
x_75 = 0;
x_76 = 1;
x_77 = l_Lean_Meta_substCore(x_2, x_1, x_75, x_74, x_76, x_4, x_5, x_6, x_7, x_64);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
lean_ctor_set(x_77, 0, x_80);
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_77, 0);
x_82 = lean_ctor_get(x_77, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_77);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_77);
if (x_85 == 0)
{
return x_77;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_77, 0);
x_87 = lean_ctor_get(x_77, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_77);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_62);
if (x_89 == 0)
{
return x_62;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_62, 0);
x_91 = lean_ctor_get(x_62, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_62);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; uint8_t x_94; lean_object* x_95; 
lean_dec(x_56);
lean_dec(x_9);
x_93 = lean_box(0);
x_94 = 1;
x_95 = l_Lean_Meta_substCore(x_2, x_1, x_94, x_93, x_94, x_4, x_5, x_6, x_7, x_60);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
lean_ctor_set(x_95, 0, x_98);
return x_95;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_95, 0);
x_100 = lean_ctor_get(x_95, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_95);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
return x_102;
}
}
else
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_95);
if (x_103 == 0)
{
return x_95;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_95, 0);
x_105 = lean_ctor_get(x_95, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_95);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_56);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_58);
if (x_107 == 0)
{
return x_58;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_58, 0);
x_109 = lean_ctor_get(x_58, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_58);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_10);
if (x_111 == 0)
{
return x_10;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_10, 0);
x_113 = lean_ctor_get(x_10, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_10);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
lean_object* l_Lean_Meta_subst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1___boxed), 6, 1);
lean_closure_set(x_8, 0, x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_subst___lambda__1___boxed), 8, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_1);
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_Meta_Basic___instance__8___spec__2___rarg), 7, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_Meta_withMVarContext___at_Lean_Meta_admit___spec__2___rarg(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
lean_object* l_Array_findSomeMAux___at_Lean_Meta_subst___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_findSomeMAux___at_Lean_Meta_subst___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_findSomeMAux___at_Lean_Meta_subst___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_findSomeMAux___at_Lean_Meta_subst___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Std_PersistentArray_findSomeMAux___at_Lean_Meta_subst___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_PersistentArray_findSomeMAux___at_Lean_Meta_subst___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Array_findSomeMAux___at_Lean_Meta_subst___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_findSomeMAux___at_Lean_Meta_subst___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
lean_object* l_Lean_Meta_subst___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_subst___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_1147_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_substCore___lambda__13___closed__18;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(lean_object*);
lean_object* initialize_Lean_Meta_MatchUtil(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Revert(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Subst(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Revert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_FVarSubst(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_substCore___lambda__11___closed__1 = _init_l_Lean_Meta_substCore___lambda__11___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__11___closed__1);
l_Lean_Meta_substCore___lambda__11___closed__2 = _init_l_Lean_Meta_substCore___lambda__11___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__11___closed__2);
l_Lean_Meta_substCore___lambda__11___closed__3 = _init_l_Lean_Meta_substCore___lambda__11___closed__3();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__11___closed__3);
l_Lean_Meta_substCore___lambda__11___closed__4 = _init_l_Lean_Meta_substCore___lambda__11___closed__4();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__11___closed__4);
l_Lean_Meta_substCore___lambda__11___closed__5 = _init_l_Lean_Meta_substCore___lambda__11___closed__5();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__11___closed__5);
l_Lean_Meta_substCore___lambda__12___closed__1 = _init_l_Lean_Meta_substCore___lambda__12___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__12___closed__1);
l_Lean_Meta_substCore___lambda__12___closed__2 = _init_l_Lean_Meta_substCore___lambda__12___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__12___closed__2);
l_Lean_Meta_substCore___lambda__13___closed__1 = _init_l_Lean_Meta_substCore___lambda__13___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__1);
l_Lean_Meta_substCore___lambda__13___closed__2 = _init_l_Lean_Meta_substCore___lambda__13___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__2);
l_Lean_Meta_substCore___lambda__13___closed__3 = _init_l_Lean_Meta_substCore___lambda__13___closed__3();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__3);
l_Lean_Meta_substCore___lambda__13___closed__4 = _init_l_Lean_Meta_substCore___lambda__13___closed__4();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__4);
l_Lean_Meta_substCore___lambda__13___closed__5 = _init_l_Lean_Meta_substCore___lambda__13___closed__5();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__5);
l_Lean_Meta_substCore___lambda__13___closed__6 = _init_l_Lean_Meta_substCore___lambda__13___closed__6();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__6);
l_Lean_Meta_substCore___lambda__13___closed__7 = _init_l_Lean_Meta_substCore___lambda__13___closed__7();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__7);
l_Lean_Meta_substCore___lambda__13___closed__8 = _init_l_Lean_Meta_substCore___lambda__13___closed__8();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__8);
l_Lean_Meta_substCore___lambda__13___closed__9 = _init_l_Lean_Meta_substCore___lambda__13___closed__9();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__9);
l_Lean_Meta_substCore___lambda__13___closed__10 = _init_l_Lean_Meta_substCore___lambda__13___closed__10();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__10);
l_Lean_Meta_substCore___lambda__13___closed__11 = _init_l_Lean_Meta_substCore___lambda__13___closed__11();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__11);
l_Lean_Meta_substCore___lambda__13___closed__12 = _init_l_Lean_Meta_substCore___lambda__13___closed__12();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__12);
l_Lean_Meta_substCore___lambda__13___closed__13 = _init_l_Lean_Meta_substCore___lambda__13___closed__13();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__13);
l_Lean_Meta_substCore___lambda__13___closed__14 = _init_l_Lean_Meta_substCore___lambda__13___closed__14();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__14);
l_Lean_Meta_substCore___lambda__13___closed__15 = _init_l_Lean_Meta_substCore___lambda__13___closed__15();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__15);
l_Lean_Meta_substCore___lambda__13___closed__16 = _init_l_Lean_Meta_substCore___lambda__13___closed__16();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__16);
l_Lean_Meta_substCore___lambda__13___closed__17 = _init_l_Lean_Meta_substCore___lambda__13___closed__17();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__17);
l_Lean_Meta_substCore___lambda__13___closed__18 = _init_l_Lean_Meta_substCore___lambda__13___closed__18();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__18);
l_Lean_Meta_substCore___lambda__13___closed__19 = _init_l_Lean_Meta_substCore___lambda__13___closed__19();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__19);
l_Lean_Meta_substCore___lambda__13___closed__20 = _init_l_Lean_Meta_substCore___lambda__13___closed__20();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__20);
l_Lean_Meta_substCore___lambda__13___closed__21 = _init_l_Lean_Meta_substCore___lambda__13___closed__21();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__21);
l_Lean_Meta_substCore___lambda__13___closed__22 = _init_l_Lean_Meta_substCore___lambda__13___closed__22();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__22);
l_Lean_Meta_substCore___lambda__13___closed__23 = _init_l_Lean_Meta_substCore___lambda__13___closed__23();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__23);
l_Lean_Meta_substCore___lambda__13___closed__24 = _init_l_Lean_Meta_substCore___lambda__13___closed__24();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__24);
l_Lean_Meta_substCore___lambda__13___closed__25 = _init_l_Lean_Meta_substCore___lambda__13___closed__25();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__25);
l_Lean_Meta_substCore___lambda__13___closed__26 = _init_l_Lean_Meta_substCore___lambda__13___closed__26();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__13___closed__26);
l_Lean_Meta_subst___lambda__1___closed__1 = _init_l_Lean_Meta_subst___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__1);
l_Lean_Meta_subst___lambda__1___closed__2 = _init_l_Lean_Meta_subst___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__2);
l_Lean_Meta_subst___lambda__1___closed__3 = _init_l_Lean_Meta_subst___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__3);
l_Lean_Meta_subst___lambda__1___closed__4 = _init_l_Lean_Meta_subst___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__4);
res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Subst___hyg_1147_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
