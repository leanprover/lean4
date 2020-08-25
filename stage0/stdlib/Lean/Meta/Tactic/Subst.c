// Lean compiler output
// Module: Lean.Meta.Tactic.Subst
// Imports: Init Lean.Meta.AppBuilder Lean.Meta.Tactic.Util Lean.Meta.Tactic.Revert Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Clear Lean.Meta.Tactic.FVarSubst
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
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__2;
lean_object* l_Lean_Meta_substCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Meta_introN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__17;
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__27;
lean_object* l_Lean_getLocalDecl___at_Lean_getFVarLocalDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__4;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__4;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__1;
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__8;
lean_object* l_Lean_Meta_subst___lambda__1___closed__2;
lean_object* l_List_toStringAux___main___at_Lean_Meta_substCore___spec__6___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2___boxed(lean_object**);
lean_object* l_Lean_Meta_mkEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__6;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__23;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__13;
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Meta_substCore___lambda__2___closed__1;
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_assignExprMVar___at_Lean_Meta_getLevel___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__21;
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__34;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__31;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__11;
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__12;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2___closed__2;
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_22__withLocalDeclImpl___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Meta_substCore___spec__5(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
lean_object* l_Lean_Meta_substCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__9;
lean_object* l_Lean_Meta_subst___lambda__1___closed__6;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__19;
lean_object* l_Lean_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_Lean_whnf___at___private_Lean_Meta_Basic_14__isClassExpensive_x3f___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__35;
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__10;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__32;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__20;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__24;
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__7;
lean_object* l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__16;
lean_object* l_List_toStringAux___main___at_Lean_Meta_substCore___spec__6(uint8_t, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withLocalDeclD___at_Lean_Meta_substCore___spec__2(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__3;
lean_object* l_Lean_Meta_substCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__26;
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__5;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__22;
uint8_t l_Lean_Expr_isFVar(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__33;
lean_object* l_Lean_withLocalDeclD___at_Lean_Meta_substCore___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__5;
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__14;
lean_object* l_Lean_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__25;
extern lean_object* l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
lean_object* l___private_Lean_Meta_Tactic_Subst_1__regTraceClasses(lean_object*);
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__29;
lean_object* l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_System_FilePath_dirName___closed__1;
extern lean_object* l___private_Lean_Meta_Basic_8__isClassQuick_x3f___main___closed__1;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__28;
lean_object* l_Lean_getLocalDecl___at_Lean_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__1;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__30;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_getMVarTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getMCtx___at_Lean_getMVarDecl___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__3;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__18;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__15;
lean_object* l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_19 = l_Lean_Name_inhabited;
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
lean_object* l_Lean_withLocalDeclD___at_Lean_Meta_substCore___spec__2___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
x_10 = l___private_Lean_Meta_Basic_22__withLocalDeclImpl___rarg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
lean_object* l_Lean_withLocalDeclD___at_Lean_Meta_substCore___spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_withLocalDeclD___at_Lean_Meta_substCore___spec__2___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_19 = l_Lean_Name_inhabited;
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
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_19 = l_Lean_Name_inhabited;
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
lean_object* l_List_toStringAux___main___at_Lean_Meta_substCore___spec__6(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l_String_splitAux___main___closed__1;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_System_FilePath_dirName___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_4);
x_8 = l_List_reprAux___main___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_List_toStringAux___main___at_Lean_Meta_substCore___spec__6(x_1, x_5);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
return x_11;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; 
x_12 = l_String_splitAux___main___closed__1;
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_System_FilePath_dirName___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_13);
x_17 = 0;
x_18 = l_List_toStringAux___main___at_Lean_Meta_substCore___spec__6(x_17, x_14);
x_19 = lean_string_append(x_16, x_18);
lean_dec(x_18);
return x_19;
}
}
}
}
lean_object* l_List_toString___at_Lean_Meta_substCore___spec__5(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = l_List_repr___rarg___closed__1;
return x_2;
}
else
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = 1;
x_4 = l_List_toStringAux___main___at_Lean_Meta_substCore___spec__6(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l_Lean_Meta_mkEqSymm(x_5, x_6, x_7, x_8, x_9, x_10);
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
x_17 = l_Lean_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_16, x_14, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
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
lean_object* _init_l_Lean_Meta_substCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_h");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_substCore___lambda__2___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_substCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12, uint8_t x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 2);
lean_inc(x_22);
lean_dec(x_16);
lean_inc(x_1);
x_23 = l_Lean_getLocalDecl___at_Lean_getFVarLocalDecl___spec__1(x_1, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_350; lean_object* x_351; uint8_t x_352; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_350 = l_Lean_LocalDecl_type(x_24);
lean_dec(x_24);
x_351 = lean_unsigned_to_nat(3u);
x_352 = l_Lean_Expr_isAppOfArity___main(x_350, x_15, x_351);
if (x_352 == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_350);
lean_dec(x_22);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_353 = l___private_Lean_Meta_Basic_8__isClassQuick_x3f___main___closed__1;
x_354 = l_unreachable_x21___rarg(x_353);
x_355 = lean_apply_5(x_354, x_17, x_18, x_19, x_20, x_25);
return x_355;
}
else
{
if (x_13 == 0)
{
lean_object* x_356; 
x_356 = l_Lean_Expr_appArg_x21(x_350);
lean_dec(x_350);
x_26 = x_356;
goto block_349;
}
else
{
lean_object* x_357; lean_object* x_358; 
x_357 = l_Lean_Expr_appFn_x21(x_350);
lean_dec(x_350);
x_358 = l_Lean_Expr_appArg_x21(x_357);
lean_dec(x_357);
x_26 = x_358;
goto block_349;
}
}
block_349:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = l_Lean_getMCtx___at_Lean_getMVarDecl___spec__1___rarg(x_18, x_19, x_20, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_22);
x_30 = l_Lean_MetavarContext_exprDependsOn(x_28, x_22, x_1);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_14);
x_32 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2);
x_33 = lean_array_push(x_32, x_2);
lean_inc(x_22);
x_34 = l_Lean_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_33, x_22, x_17, x_18, x_19, x_20, x_29);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_2);
x_37 = l_Lean_Expr_replaceFVar(x_22, x_2, x_26);
lean_dec(x_22);
if (x_13 == 0)
{
lean_object* x_126; 
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_10);
x_126 = l_Lean_Meta_mkEqSymm(x_10, x_17, x_18, x_19, x_20, x_36);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_38 = x_127;
x_39 = x_128;
goto block_125;
}
else
{
uint8_t x_129; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_126);
if (x_129 == 0)
{
return x_126;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_126, 0);
x_131 = lean_ctor_get(x_126, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_126);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
lean_inc(x_10);
x_38 = x_10;
x_39 = x_36;
goto block_125;
}
block_125:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_37, x_3, x_17, x_18, x_19, x_20, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_41);
x_43 = l_Lean_Meta_mkEqNDRec(x_35, x_41, x_38, x_17, x_18, x_19, x_20, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_assignExprMVar___at_Lean_Meta_getLevel___spec__3(x_4, x_44, x_17, x_18, x_19, x_20, x_45);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Expr_mvarId_x21(x_41);
lean_dec(x_41);
if (x_12 == 0)
{
uint8_t x_119; 
x_119 = 0;
x_49 = x_119;
goto block_118;
}
else
{
uint8_t x_120; 
x_120 = 1;
x_49 = x_120;
goto block_118;
}
block_118:
{
lean_object* x_50; lean_object* x_51; 
if (x_49 == 0)
{
lean_dec(x_11);
lean_dec(x_1);
x_50 = x_48;
x_51 = x_47;
goto block_103;
}
else
{
lean_object* x_104; 
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_104 = l_Lean_Meta_clear(x_48, x_1, x_17, x_18, x_19, x_20, x_47);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_107 = l_Lean_Meta_clear(x_105, x_11, x_17, x_18, x_19, x_20, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_50 = x_108;
x_51 = x_109;
goto block_103;
}
else
{
uint8_t x_110; 
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_110 = !lean_is_exclusive(x_107);
if (x_110 == 0)
{
return x_107;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_107, 0);
x_112 = lean_ctor_get(x_107, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_107);
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
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_104);
if (x_114 == 0)
{
return x_104;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_104, 0);
x_116 = lean_ctor_get(x_104, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_104);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
block_103:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_52 = lean_array_get_size(x_5);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_nat_sub(x_52, x_53);
lean_dec(x_52);
x_55 = 0;
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_56 = l_Lean_Meta_introN(x_50, x_54, x_6, x_55, x_17, x_18, x_19, x_20, x_51);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_57, 0);
x_61 = lean_array_get_size(x_60);
lean_inc(x_61);
x_62 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1(x_5, x_60, x_61, x_61, x_7, x_17, x_18, x_19, x_20, x_58);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_61);
lean_dec(x_60);
if (x_49 == 0)
{
uint8_t x_63; 
lean_dec(x_26);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = l_Lean_Meta_FVarSubst_insert(x_64, x_8, x_2);
x_66 = l_Lean_Meta_FVarSubst_insert(x_65, x_9, x_10);
lean_ctor_set(x_57, 0, x_66);
lean_ctor_set(x_62, 0, x_57);
return x_62;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_62, 0);
x_68 = lean_ctor_get(x_62, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_62);
x_69 = l_Lean_Meta_FVarSubst_insert(x_67, x_8, x_2);
x_70 = l_Lean_Meta_FVarSubst_insert(x_69, x_9, x_10);
lean_ctor_set(x_57, 0, x_70);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_57);
lean_ctor_set(x_71, 1, x_68);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_2);
x_72 = !lean_is_exclusive(x_62);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_62, 0);
x_74 = l_Lean_Meta_FVarSubst_insert(x_73, x_8, x_26);
x_75 = l_Lean_Meta_FVarSubst_insert(x_74, x_9, x_10);
lean_ctor_set(x_57, 0, x_75);
lean_ctor_set(x_62, 0, x_57);
return x_62;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_62, 0);
x_77 = lean_ctor_get(x_62, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_62);
x_78 = l_Lean_Meta_FVarSubst_insert(x_76, x_8, x_26);
x_79 = l_Lean_Meta_FVarSubst_insert(x_78, x_9, x_10);
lean_ctor_set(x_57, 0, x_79);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_57);
lean_ctor_set(x_80, 1, x_77);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_57, 0);
x_82 = lean_ctor_get(x_57, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_57);
x_83 = lean_array_get_size(x_81);
lean_inc(x_83);
x_84 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1(x_5, x_81, x_83, x_83, x_7, x_17, x_18, x_19, x_20, x_58);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_83);
lean_dec(x_81);
if (x_49 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_26);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_87 = x_84;
} else {
 lean_dec_ref(x_84);
 x_87 = lean_box(0);
}
x_88 = l_Lean_Meta_FVarSubst_insert(x_85, x_8, x_2);
x_89 = l_Lean_Meta_FVarSubst_insert(x_88, x_9, x_10);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_82);
if (lean_is_scalar(x_87)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_87;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_86);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_2);
x_92 = lean_ctor_get(x_84, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_84, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_94 = x_84;
} else {
 lean_dec_ref(x_84);
 x_94 = lean_box(0);
}
x_95 = l_Lean_Meta_FVarSubst_insert(x_92, x_8, x_26);
x_96 = l_Lean_Meta_FVarSubst_insert(x_95, x_9, x_10);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_82);
if (lean_is_scalar(x_94)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_94;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_93);
return x_98;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_99 = !lean_is_exclusive(x_56);
if (x_99 == 0)
{
return x_56;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_56, 0);
x_101 = lean_ctor_get(x_56, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_56);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_41);
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_43);
if (x_121 == 0)
{
return x_43;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_43, 0);
x_123 = lean_ctor_get(x_43, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_43);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_34);
if (x_133 == 0)
{
return x_34;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_34, 0);
x_135 = lean_ctor_get(x_34, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_34);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_inc(x_2);
x_137 = l_Lean_Expr_replaceFVar(x_22, x_2, x_26);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_26);
x_138 = l_Lean_Meta_mkEqRefl(x_26, x_17, x_18, x_19, x_20, x_29);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
lean_inc(x_10);
x_141 = l_Lean_Expr_replaceFVar(x_137, x_10, x_139);
lean_dec(x_139);
lean_dec(x_137);
if (x_13 == 0)
{
lean_object* x_142; 
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_2);
lean_inc(x_26);
x_142 = l_Lean_Meta_mkEq(x_26, x_2, x_17, x_18, x_19, x_20, x_140);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; lean_object* x_148; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
lean_inc(x_2);
lean_inc(x_10);
x_145 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__1___boxed), 10, 4);
lean_closure_set(x_145, 0, x_22);
lean_closure_set(x_145, 1, x_10);
lean_closure_set(x_145, 2, x_14);
lean_closure_set(x_145, 3, x_2);
x_146 = l_Lean_Meta_substCore___lambda__2___closed__2;
x_147 = 0;
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_148 = l___private_Lean_Meta_Basic_22__withLocalDeclImpl___rarg(x_146, x_147, x_143, x_145, x_17, x_18, x_19, x_20, x_144);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
lean_dec(x_148);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_10);
x_151 = l_Lean_Meta_mkEqSymm(x_10, x_17, x_18, x_19, x_20, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_141, x_3, x_17, x_18, x_19, x_20, x_153);
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_155);
x_157 = l_Lean_Meta_mkEqRec(x_149, x_155, x_152, x_17, x_18, x_19, x_20, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l_Lean_assignExprMVar___at_Lean_Meta_getLevel___spec__3(x_4, x_158, x_17, x_18, x_19, x_20, x_159);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = l_Lean_Expr_mvarId_x21(x_155);
lean_dec(x_155);
if (x_12 == 0)
{
uint8_t x_233; 
x_233 = 0;
x_163 = x_233;
goto block_232;
}
else
{
uint8_t x_234; 
x_234 = 1;
x_163 = x_234;
goto block_232;
}
block_232:
{
lean_object* x_164; lean_object* x_165; 
if (x_163 == 0)
{
lean_dec(x_11);
lean_dec(x_1);
x_164 = x_162;
x_165 = x_161;
goto block_217;
}
else
{
lean_object* x_218; 
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_218 = l_Lean_Meta_clear(x_162, x_1, x_17, x_18, x_19, x_20, x_161);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
lean_dec(x_218);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_221 = l_Lean_Meta_clear(x_219, x_11, x_17, x_18, x_19, x_20, x_220);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; 
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_221, 1);
lean_inc(x_223);
lean_dec(x_221);
x_164 = x_222;
x_165 = x_223;
goto block_217;
}
else
{
uint8_t x_224; 
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_224 = !lean_is_exclusive(x_221);
if (x_224 == 0)
{
return x_221;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_221, 0);
x_226 = lean_ctor_get(x_221, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_221);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
uint8_t x_228; 
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_228 = !lean_is_exclusive(x_218);
if (x_228 == 0)
{
return x_218;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_218, 0);
x_230 = lean_ctor_get(x_218, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_218);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
block_217:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; 
x_166 = lean_array_get_size(x_5);
x_167 = lean_unsigned_to_nat(2u);
x_168 = lean_nat_sub(x_166, x_167);
lean_dec(x_166);
x_169 = 0;
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_170 = l_Lean_Meta_introN(x_164, x_168, x_6, x_169, x_17, x_18, x_19, x_20, x_165);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = !lean_is_exclusive(x_171);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_171, 0);
x_175 = lean_array_get_size(x_174);
lean_inc(x_175);
x_176 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3(x_5, x_174, x_175, x_175, x_7, x_17, x_18, x_19, x_20, x_172);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_175);
lean_dec(x_174);
if (x_163 == 0)
{
uint8_t x_177; 
lean_dec(x_26);
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_176, 0);
x_179 = l_Lean_Meta_FVarSubst_insert(x_178, x_8, x_2);
x_180 = l_Lean_Meta_FVarSubst_insert(x_179, x_9, x_10);
lean_ctor_set(x_171, 0, x_180);
lean_ctor_set(x_176, 0, x_171);
return x_176;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_181 = lean_ctor_get(x_176, 0);
x_182 = lean_ctor_get(x_176, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_176);
x_183 = l_Lean_Meta_FVarSubst_insert(x_181, x_8, x_2);
x_184 = l_Lean_Meta_FVarSubst_insert(x_183, x_9, x_10);
lean_ctor_set(x_171, 0, x_184);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_171);
lean_ctor_set(x_185, 1, x_182);
return x_185;
}
}
else
{
uint8_t x_186; 
lean_dec(x_2);
x_186 = !lean_is_exclusive(x_176);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_176, 0);
x_188 = l_Lean_Meta_FVarSubst_insert(x_187, x_8, x_26);
x_189 = l_Lean_Meta_FVarSubst_insert(x_188, x_9, x_10);
lean_ctor_set(x_171, 0, x_189);
lean_ctor_set(x_176, 0, x_171);
return x_176;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_190 = lean_ctor_get(x_176, 0);
x_191 = lean_ctor_get(x_176, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_176);
x_192 = l_Lean_Meta_FVarSubst_insert(x_190, x_8, x_26);
x_193 = l_Lean_Meta_FVarSubst_insert(x_192, x_9, x_10);
lean_ctor_set(x_171, 0, x_193);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_171);
lean_ctor_set(x_194, 1, x_191);
return x_194;
}
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_195 = lean_ctor_get(x_171, 0);
x_196 = lean_ctor_get(x_171, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_171);
x_197 = lean_array_get_size(x_195);
lean_inc(x_197);
x_198 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3(x_5, x_195, x_197, x_197, x_7, x_17, x_18, x_19, x_20, x_172);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_197);
lean_dec(x_195);
if (x_163 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_26);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_201 = x_198;
} else {
 lean_dec_ref(x_198);
 x_201 = lean_box(0);
}
x_202 = l_Lean_Meta_FVarSubst_insert(x_199, x_8, x_2);
x_203 = l_Lean_Meta_FVarSubst_insert(x_202, x_9, x_10);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_196);
if (lean_is_scalar(x_201)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_201;
}
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_200);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_2);
x_206 = lean_ctor_get(x_198, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_198, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_208 = x_198;
} else {
 lean_dec_ref(x_198);
 x_208 = lean_box(0);
}
x_209 = l_Lean_Meta_FVarSubst_insert(x_206, x_8, x_26);
x_210 = l_Lean_Meta_FVarSubst_insert(x_209, x_9, x_10);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_196);
if (lean_is_scalar(x_208)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_208;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_207);
return x_212;
}
}
}
else
{
uint8_t x_213; 
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_213 = !lean_is_exclusive(x_170);
if (x_213 == 0)
{
return x_170;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_170, 0);
x_215 = lean_ctor_get(x_170, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_170);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
}
}
else
{
uint8_t x_235; 
lean_dec(x_155);
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_235 = !lean_is_exclusive(x_157);
if (x_235 == 0)
{
return x_157;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_157, 0);
x_237 = lean_ctor_get(x_157, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_157);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
}
else
{
uint8_t x_239; 
lean_dec(x_149);
lean_dec(x_141);
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_239 = !lean_is_exclusive(x_151);
if (x_239 == 0)
{
return x_151;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_151, 0);
x_241 = lean_ctor_get(x_151, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_151);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
else
{
uint8_t x_243; 
lean_dec(x_141);
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_243 = !lean_is_exclusive(x_148);
if (x_243 == 0)
{
return x_148;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_148, 0);
x_245 = lean_ctor_get(x_148, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_148);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
else
{
uint8_t x_247; 
lean_dec(x_141);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_247 = !lean_is_exclusive(x_142);
if (x_247 == 0)
{
return x_142;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_142, 0);
x_249 = lean_ctor_get(x_142, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_142);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_inc(x_2);
x_251 = lean_array_push(x_14, x_2);
lean_inc(x_10);
x_252 = lean_array_push(x_251, x_10);
x_253 = l_Lean_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_252, x_22, x_17, x_18, x_19, x_20, x_140);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
x_256 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_141, x_3, x_17, x_18, x_19, x_20, x_255);
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_10);
lean_inc(x_257);
x_259 = l_Lean_Meta_mkEqRec(x_254, x_257, x_10, x_17, x_18, x_19, x_20, x_258);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = l_Lean_assignExprMVar___at_Lean_Meta_getLevel___spec__3(x_4, x_260, x_17, x_18, x_19, x_20, x_261);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_264 = l_Lean_Expr_mvarId_x21(x_257);
lean_dec(x_257);
if (x_12 == 0)
{
uint8_t x_335; 
x_335 = 0;
x_265 = x_335;
goto block_334;
}
else
{
uint8_t x_336; 
x_336 = 1;
x_265 = x_336;
goto block_334;
}
block_334:
{
lean_object* x_266; lean_object* x_267; 
if (x_265 == 0)
{
lean_dec(x_11);
lean_dec(x_1);
x_266 = x_264;
x_267 = x_263;
goto block_319;
}
else
{
lean_object* x_320; 
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_320 = l_Lean_Meta_clear(x_264, x_1, x_17, x_18, x_19, x_20, x_263);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_323 = l_Lean_Meta_clear(x_321, x_11, x_17, x_18, x_19, x_20, x_322);
if (lean_obj_tag(x_323) == 0)
{
lean_object* x_324; lean_object* x_325; 
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
x_266 = x_324;
x_267 = x_325;
goto block_319;
}
else
{
uint8_t x_326; 
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_326 = !lean_is_exclusive(x_323);
if (x_326 == 0)
{
return x_323;
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_327 = lean_ctor_get(x_323, 0);
x_328 = lean_ctor_get(x_323, 1);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_323);
x_329 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_329, 0, x_327);
lean_ctor_set(x_329, 1, x_328);
return x_329;
}
}
}
else
{
uint8_t x_330; 
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_330 = !lean_is_exclusive(x_320);
if (x_330 == 0)
{
return x_320;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_320, 0);
x_332 = lean_ctor_get(x_320, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_320);
x_333 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_333, 0, x_331);
lean_ctor_set(x_333, 1, x_332);
return x_333;
}
}
}
block_319:
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; lean_object* x_272; 
x_268 = lean_array_get_size(x_5);
x_269 = lean_unsigned_to_nat(2u);
x_270 = lean_nat_sub(x_268, x_269);
lean_dec(x_268);
x_271 = 0;
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_272 = l_Lean_Meta_introN(x_266, x_270, x_6, x_271, x_17, x_18, x_19, x_20, x_267);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
x_275 = !lean_is_exclusive(x_273);
if (x_275 == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_273, 0);
x_277 = lean_array_get_size(x_276);
lean_inc(x_277);
x_278 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__4(x_5, x_276, x_277, x_277, x_7, x_17, x_18, x_19, x_20, x_274);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_277);
lean_dec(x_276);
if (x_265 == 0)
{
uint8_t x_279; 
lean_dec(x_26);
x_279 = !lean_is_exclusive(x_278);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_278, 0);
x_281 = l_Lean_Meta_FVarSubst_insert(x_280, x_8, x_2);
x_282 = l_Lean_Meta_FVarSubst_insert(x_281, x_9, x_10);
lean_ctor_set(x_273, 0, x_282);
lean_ctor_set(x_278, 0, x_273);
return x_278;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_283 = lean_ctor_get(x_278, 0);
x_284 = lean_ctor_get(x_278, 1);
lean_inc(x_284);
lean_inc(x_283);
lean_dec(x_278);
x_285 = l_Lean_Meta_FVarSubst_insert(x_283, x_8, x_2);
x_286 = l_Lean_Meta_FVarSubst_insert(x_285, x_9, x_10);
lean_ctor_set(x_273, 0, x_286);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_273);
lean_ctor_set(x_287, 1, x_284);
return x_287;
}
}
else
{
uint8_t x_288; 
lean_dec(x_2);
x_288 = !lean_is_exclusive(x_278);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_278, 0);
x_290 = l_Lean_Meta_FVarSubst_insert(x_289, x_8, x_26);
x_291 = l_Lean_Meta_FVarSubst_insert(x_290, x_9, x_10);
lean_ctor_set(x_273, 0, x_291);
lean_ctor_set(x_278, 0, x_273);
return x_278;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_292 = lean_ctor_get(x_278, 0);
x_293 = lean_ctor_get(x_278, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_278);
x_294 = l_Lean_Meta_FVarSubst_insert(x_292, x_8, x_26);
x_295 = l_Lean_Meta_FVarSubst_insert(x_294, x_9, x_10);
lean_ctor_set(x_273, 0, x_295);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_273);
lean_ctor_set(x_296, 1, x_293);
return x_296;
}
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_297 = lean_ctor_get(x_273, 0);
x_298 = lean_ctor_get(x_273, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_273);
x_299 = lean_array_get_size(x_297);
lean_inc(x_299);
x_300 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__4(x_5, x_297, x_299, x_299, x_7, x_17, x_18, x_19, x_20, x_274);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_299);
lean_dec(x_297);
if (x_265 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_26);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_303 = x_300;
} else {
 lean_dec_ref(x_300);
 x_303 = lean_box(0);
}
x_304 = l_Lean_Meta_FVarSubst_insert(x_301, x_8, x_2);
x_305 = l_Lean_Meta_FVarSubst_insert(x_304, x_9, x_10);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_298);
if (lean_is_scalar(x_303)) {
 x_307 = lean_alloc_ctor(0, 2, 0);
} else {
 x_307 = x_303;
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_302);
return x_307;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_2);
x_308 = lean_ctor_get(x_300, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_300, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_300)) {
 lean_ctor_release(x_300, 0);
 lean_ctor_release(x_300, 1);
 x_310 = x_300;
} else {
 lean_dec_ref(x_300);
 x_310 = lean_box(0);
}
x_311 = l_Lean_Meta_FVarSubst_insert(x_308, x_8, x_26);
x_312 = l_Lean_Meta_FVarSubst_insert(x_311, x_9, x_10);
x_313 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_313, 0, x_312);
lean_ctor_set(x_313, 1, x_298);
if (lean_is_scalar(x_310)) {
 x_314 = lean_alloc_ctor(0, 2, 0);
} else {
 x_314 = x_310;
}
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_309);
return x_314;
}
}
}
else
{
uint8_t x_315; 
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_315 = !lean_is_exclusive(x_272);
if (x_315 == 0)
{
return x_272;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_272, 0);
x_317 = lean_ctor_get(x_272, 1);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_272);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
return x_318;
}
}
}
}
}
else
{
uint8_t x_337; 
lean_dec(x_257);
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_337 = !lean_is_exclusive(x_259);
if (x_337 == 0)
{
return x_259;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_259, 0);
x_339 = lean_ctor_get(x_259, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_259);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
return x_340;
}
}
}
else
{
uint8_t x_341; 
lean_dec(x_141);
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_341 = !lean_is_exclusive(x_253);
if (x_341 == 0)
{
return x_253;
}
else
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_253, 0);
x_343 = lean_ctor_get(x_253, 1);
lean_inc(x_343);
lean_inc(x_342);
lean_dec(x_253);
x_344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_344, 0, x_342);
lean_ctor_set(x_344, 1, x_343);
return x_344;
}
}
}
}
else
{
uint8_t x_345; 
lean_dec(x_137);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_345 = !lean_is_exclusive(x_138);
if (x_345 == 0)
{
return x_138;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_138, 0);
x_347 = lean_ctor_get(x_138, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_138);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
return x_348;
}
}
}
}
}
else
{
uint8_t x_359; 
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_359 = !lean_is_exclusive(x_23);
if (x_359 == 0)
{
return x_23;
}
else
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_360 = lean_ctor_get(x_23, 0);
x_361 = lean_ctor_get(x_23, 1);
lean_inc(x_361);
lean_inc(x_360);
lean_dec(x_23);
x_362 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_362, 0, x_360);
lean_ctor_set(x_362, 1, x_361);
return x_362;
}
}
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("subst");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_substCore___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("argument must be an equality proof");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid equality proof, it is not of the form ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after WHNF, variable expected, but obtained");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(x = t)");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__12;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__8;
x_2 = l_Lean_Meta_substCore___lambda__3___closed__14;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(t = x)");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__8;
x_2 = l_Lean_Meta_substCore___lambda__3___closed__18;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_substCore___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reverted variables ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__21;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__22;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__24() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' occurs at");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__25() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__24;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__26() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__25;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__27() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("substituting ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__28() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__27;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__29() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__28;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__30() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" (id: ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__31() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__30;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__32() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__31;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__33() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(") with ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__34() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__33;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__35() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__34;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Meta_substCore___lambda__3___closed__2;
lean_inc(x_1);
x_13 = l_Lean_Meta_checkNotAssigned(x_1, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_2);
x_15 = l_Lean_getLocalDecl___at_Lean_getFVarLocalDecl___spec__1(x_2, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_LocalDecl_type(x_16);
lean_dec(x_16);
x_19 = l_Lean_Expr_eq_x3f___closed__2;
x_20 = lean_unsigned_to_nat(3u);
x_21 = l_Lean_Expr_isAppOfArity___main(x_18, x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_22 = l_Lean_Meta_substCore___lambda__3___closed__5;
x_23 = lean_box(0);
x_24 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_22, x_23, x_7, x_8, x_9, x_10, x_17);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_25 = l_Lean_Expr_appFn_x21(x_18);
x_26 = l_Lean_Expr_appArg_x21(x_25);
lean_dec(x_25);
x_27 = l_Lean_Expr_appArg_x21(x_18);
if (x_5 == 0)
{
uint8_t x_209; 
x_209 = 0;
x_28 = x_209;
goto block_208;
}
else
{
uint8_t x_210; 
x_210 = 1;
x_28 = x_210;
goto block_208;
}
block_208:
{
lean_object* x_29; 
if (x_28 == 0)
{
lean_inc(x_26);
x_29 = x_26;
goto block_207;
}
else
{
lean_inc(x_27);
x_29 = x_27;
goto block_207;
}
block_207:
{
lean_object* x_30; 
if (x_28 == 0)
{
lean_dec(x_26);
x_30 = x_27;
goto block_206;
}
else
{
lean_dec(x_27);
x_30 = x_26;
goto block_206;
}
block_206:
{
lean_object* x_31; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_whnf___at___private_Lean_Meta_Basic_14__isClassExpensive_x3f___main___spec__2(x_29, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 1)
{
lean_object* x_58; lean_object* x_59; uint8_t x_167; lean_object* x_168; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_18);
x_58 = lean_ctor_get(x_32, 0);
lean_inc(x_58);
x_184 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_185 = lean_ctor_get(x_184, 2);
lean_inc(x_185);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_186 = lean_apply_5(x_185, x_7, x_8, x_9, x_10, x_33);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; uint8_t x_188; 
x_187 = lean_ctor_get(x_186, 0);
lean_inc(x_187);
x_188 = lean_ctor_get_uint8(x_187, sizeof(void*)*1);
lean_dec(x_187);
if (x_188 == 0)
{
lean_object* x_189; uint8_t x_190; 
x_189 = lean_ctor_get(x_186, 1);
lean_inc(x_189);
lean_dec(x_186);
x_190 = 0;
x_167 = x_190;
x_168 = x_189;
goto block_183;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_191 = lean_ctor_get(x_186, 1);
lean_inc(x_191);
lean_dec(x_186);
x_192 = l_Lean_Meta_substCore___lambda__3___closed__20;
x_193 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_192, x_7, x_8, x_9, x_10, x_191);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = lean_unbox(x_194);
lean_dec(x_194);
x_167 = x_196;
x_168 = x_195;
goto block_183;
}
}
else
{
uint8_t x_197; 
lean_dec(x_58);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_197 = !lean_is_exclusive(x_186);
if (x_197 == 0)
{
return x_186;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_186, 0);
x_199 = lean_ctor_get(x_186, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_186);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
block_166:
{
lean_object* x_60; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_147 = l_Lean_getMCtx___at_Lean_getMVarDecl___spec__1___rarg(x_8, x_9, x_10, x_59);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
lean_inc(x_30);
x_150 = l_Lean_MetavarContext_exprDependsOn(x_148, x_30, x_58);
x_151 = lean_unbox(x_150);
lean_dec(x_150);
if (x_151 == 0)
{
lean_dec(x_32);
lean_dec(x_30);
x_60 = x_149;
goto block_146;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_58);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_152 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_152, 0, x_32);
x_153 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_154 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
x_155 = l_Lean_Meta_substCore___lambda__3___closed__26;
x_156 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_157, 0, x_30);
x_158 = l_Lean_indentExpr(x_157);
x_159 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_box(0);
x_161 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_159, x_160, x_7, x_8, x_9, x_10, x_149);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
return x_161;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_161, 0);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_161);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
block_146:
{
lean_object* x_61; 
lean_inc(x_58);
x_61 = l_Lean_getLocalDecl___at_Lean_getFVarLocalDecl___spec__1(x_58, x_7, x_8, x_9, x_10, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_63 = l_Lean_mkAppStx___closed__9;
lean_inc(x_58);
x_64 = lean_array_push(x_63, x_58);
lean_inc(x_2);
x_65 = lean_array_push(x_64, x_2);
x_66 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_67 = l_Lean_Meta_revert(x_1, x_65, x_66, x_7, x_8, x_9, x_10, x_62);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = lean_box(0);
x_73 = lean_unsigned_to_nat(2u);
x_74 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_75 = l_Lean_Meta_introN(x_71, x_73, x_72, x_74, x_7, x_8, x_9, x_10, x_69);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_104; lean_object* x_105; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_118 = l_Lean_Meta_Lean_SimpleMonadTracerAdapter___closed__4;
x_119 = lean_ctor_get(x_118, 2);
lean_inc(x_119);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_120 = lean_apply_5(x_119, x_7, x_8, x_9, x_10, x_77);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; uint8_t x_122; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get_uint8(x_121, sizeof(void*)*1);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; 
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
x_104 = x_74;
x_105 = x_123;
goto block_117;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
lean_dec(x_120);
x_125 = l_Lean_Meta_substCore___lambda__3___closed__20;
x_126 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_check___spec__3(x_125, x_7, x_8, x_9, x_10, x_124);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_unbox(x_127);
lean_dec(x_127);
x_104 = x_129;
x_105 = x_128;
goto block_117;
}
}
else
{
uint8_t x_130; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_70);
lean_dec(x_58);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_130 = !lean_is_exclusive(x_120);
if (x_130 == 0)
{
return x_120;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_120, 0);
x_132 = lean_ctor_get(x_120, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_120);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
block_103:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_81 = l_Lean_Name_inhabited;
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_array_get(x_81, x_78, x_82);
lean_inc(x_83);
x_84 = l_Lean_mkFVar(x_83);
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_array_get(x_81, x_78, x_85);
lean_dec(x_78);
lean_inc(x_86);
x_87 = l_Lean_mkFVar(x_86);
lean_inc(x_79);
x_88 = lean_alloc_closure((void*)(l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1___boxed), 6, 1);
lean_closure_set(x_88, 0, x_79);
x_89 = lean_box(x_4);
x_90 = lean_box(x_28);
lean_inc(x_79);
x_91 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__2___boxed), 21, 15);
lean_closure_set(x_91, 0, x_86);
lean_closure_set(x_91, 1, x_84);
lean_closure_set(x_91, 2, x_6);
lean_closure_set(x_91, 3, x_79);
lean_closure_set(x_91, 4, x_70);
lean_closure_set(x_91, 5, x_72);
lean_closure_set(x_91, 6, x_3);
lean_closure_set(x_91, 7, x_58);
lean_closure_set(x_91, 8, x_2);
lean_closure_set(x_91, 9, x_87);
lean_closure_set(x_91, 10, x_83);
lean_closure_set(x_91, 11, x_89);
lean_closure_set(x_91, 12, x_90);
lean_closure_set(x_91, 13, x_63);
lean_closure_set(x_91, 14, x_19);
x_92 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_92, 0, x_88);
lean_closure_set(x_92, 1, x_91);
x_93 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_79, x_7, x_8, x_9, x_10, x_80);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 4);
lean_inc(x_97);
lean_dec(x_94);
x_98 = l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(x_96, x_97, x_92, x_7, x_8, x_9, x_10, x_95);
return x_98;
}
else
{
uint8_t x_99; 
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_99 = !lean_is_exclusive(x_93);
if (x_99 == 0)
{
return x_93;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_93, 0);
x_101 = lean_ctor_get(x_93, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_93);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
block_117:
{
if (x_104 == 0)
{
x_80 = x_105;
goto block_103;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_106 = l_Array_toList___rarg(x_70);
x_107 = l_List_toString___at_Lean_Meta_substCore___spec__5(x_106);
x_108 = l_Array_HasRepr___rarg___closed__1;
x_109 = lean_string_append(x_108, x_107);
lean_dec(x_107);
x_110 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_110, 0, x_109);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = l_Lean_Meta_substCore___lambda__3___closed__23;
x_113 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
x_114 = l_Lean_Meta_substCore___lambda__3___closed__20;
x_115 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_114, x_113, x_7, x_8, x_9, x_10, x_105);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_80 = x_116;
goto block_103;
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_70);
lean_dec(x_58);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_134 = !lean_is_exclusive(x_75);
if (x_134 == 0)
{
return x_75;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_75, 0);
x_136 = lean_ctor_get(x_75, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_75);
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
lean_dec(x_58);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_138 = !lean_is_exclusive(x_67);
if (x_138 == 0)
{
return x_67;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_67, 0);
x_140 = lean_ctor_get(x_67, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_67);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_58);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_61);
if (x_142 == 0)
{
return x_61;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_61, 0);
x_144 = lean_ctor_get(x_61, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_61);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
}
block_183:
{
if (x_167 == 0)
{
x_59 = x_168;
goto block_166;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_inc(x_32);
x_169 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_169, 0, x_32);
x_170 = l_Lean_Meta_substCore___lambda__3___closed__29;
x_171 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_169);
x_172 = l_Lean_Meta_substCore___lambda__3___closed__32;
x_173 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
lean_inc(x_58);
x_174 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_174, 0, x_58);
x_175 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = l_Lean_Meta_substCore___lambda__3___closed__35;
x_177 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
lean_inc(x_30);
x_178 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_178, 0, x_30);
x_179 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
x_180 = l_Lean_Meta_substCore___lambda__3___closed__20;
x_181 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isTypeCorrect___spec__1(x_180, x_179, x_7, x_8, x_9, x_10, x_168);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_59 = x_182;
goto block_166;
}
}
}
else
{
lean_object* x_201; 
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_201 = lean_box(0);
x_34 = x_201;
goto block_57;
}
block_57:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
x_35 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_35, 0, x_18);
x_36 = l_Lean_indentExpr(x_35);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_38 = l_Lean_indentExpr(x_37);
if (x_28 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_39 = l_Lean_Meta_substCore___lambda__3___closed__15;
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
x_41 = l_Lean_MessageData_ofList___closed__3;
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Meta_substCore___lambda__3___closed__11;
x_44 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_38);
x_46 = lean_box(0);
x_47 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_45, x_46, x_7, x_8, x_9, x_10, x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_48 = l_Lean_Meta_substCore___lambda__3___closed__19;
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_36);
x_50 = l_Lean_MessageData_ofList___closed__3;
x_51 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Meta_substCore___lambda__3___closed__11;
x_53 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_38);
x_55 = lean_box(0);
x_56 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_54, x_55, x_7, x_8, x_9, x_10, x_33);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_56;
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_30);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_202 = !lean_is_exclusive(x_31);
if (x_202 == 0)
{
return x_31;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_31, 0);
x_204 = lean_ctor_get(x_31, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_31);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
}
}
}
}
else
{
uint8_t x_211; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_211 = !lean_is_exclusive(x_15);
if (x_211 == 0)
{
return x_15;
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_212 = lean_ctor_get(x_15, 0);
x_213 = lean_ctor_get(x_15, 1);
lean_inc(x_213);
lean_inc(x_212);
lean_dec(x_15);
x_214 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_214, 0, x_212);
lean_ctor_set(x_214, 1, x_213);
return x_214;
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_215 = !lean_is_exclusive(x_13);
if (x_215 == 0)
{
return x_13;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_13, 0);
x_217 = lean_ctor_get(x_13, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_13);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
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
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__3___boxed), 11, 5);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_4);
lean_closure_set(x_14, 3, x_12);
lean_closure_set(x_14, 4, x_13);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 4);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(x_19, x_20, x_15, x_6, x_7, x_8, x_9, x_18);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_16, 0);
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_16);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_List_toStringAux___main___at_Lean_Meta_substCore___spec__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at_Lean_Meta_substCore___spec__6(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_substCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_substCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
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
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_unbox(x_12);
lean_dec(x_12);
x_23 = lean_unbox(x_13);
lean_dec(x_13);
x_24 = l_Lean_Meta_substCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22, x_23, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_15);
lean_dec(x_5);
return x_24;
}
}
lean_object* l_Lean_Meta_substCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Meta_substCore___lambda__3(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_4);
x_12 = lean_nat_dec_lt(x_5, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_fget(x_4, x_5);
lean_inc(x_3);
x_16 = l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(x_1, x_2, x_3, x_15, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_5, x_19);
lean_dec(x_5);
x_5 = x_20;
x_10 = x_18;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_5);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_16);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_16, 0);
lean_dec(x_23);
return x_16;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_16, 1);
lean_inc(x_24);
lean_dec(x_16);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_4);
x_12 = lean_nat_dec_lt(x_5, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_array_fget(x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_5, x_16);
lean_dec(x_5);
x_5 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_20 = x_15;
} else {
 lean_dec_ref(x_15);
 x_20 = lean_box(0);
}
x_21 = l_Lean_LocalDecl_type(x_19);
x_22 = lean_unsigned_to_nat(3u);
x_23 = l_Lean_Expr_isAppOfArity___main(x_21, x_2, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_5 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_52; 
x_27 = l_Lean_Expr_appFn_x21(x_21);
x_28 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_29 = l_Lean_Expr_appArg_x21(x_21);
lean_dec(x_21);
x_52 = l_Lean_Expr_isFVar(x_29);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_box(0);
x_30 = x_53;
goto block_51;
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Expr_fvarId_x21(x_29);
x_55 = lean_name_eq(x_54, x_1);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_box(0);
x_30 = x_56;
goto block_51;
}
else
{
lean_object* x_57; uint8_t x_58; 
lean_inc(x_28);
lean_inc(x_3);
x_57 = l_Lean_MetavarContext_exprDependsOn(x_3, x_28, x_1);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_3);
x_59 = l_Lean_LocalDecl_fvarId(x_19);
lean_dec(x_19);
x_60 = 1;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_10);
return x_64;
}
else
{
lean_object* x_65; 
x_65 = lean_box(0);
x_30 = x_65;
goto block_51;
}
}
}
block_51:
{
uint8_t x_31; 
lean_dec(x_30);
x_31 = l_Lean_Expr_isFVar(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_20);
lean_dec(x_19);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_5, x_32);
lean_dec(x_5);
x_5 = x_33;
goto _start;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Expr_fvarId_x21(x_28);
lean_dec(x_28);
x_36 = lean_name_eq(x_35, x_1);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_19);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_5, x_37);
lean_dec(x_5);
x_5 = x_38;
goto _start;
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_inc(x_3);
x_40 = l_Lean_MetavarContext_exprDependsOn(x_3, x_29, x_1);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_5);
lean_dec(x_3);
x_42 = l_Lean_LocalDecl_fvarId(x_19);
lean_dec(x_19);
x_43 = 0;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
if (lean_is_scalar(x_20)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_20;
}
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_10);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_20);
lean_dec(x_19);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_5, x_48);
lean_dec(x_5);
x_5 = x_49;
goto _start;
}
}
}
}
}
}
}
}
}
lean_object* l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4(x_1, x_2, x_3, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5(x_1, x_2, x_3, x_13, x_14, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_4);
x_12 = lean_nat_dec_lt(x_5, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_3);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_array_fget(x_4, x_5);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_5, x_16);
lean_dec(x_5);
x_5 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_20 = x_15;
} else {
 lean_dec_ref(x_15);
 x_20 = lean_box(0);
}
x_21 = l_Lean_LocalDecl_type(x_19);
x_22 = lean_unsigned_to_nat(3u);
x_23 = l_Lean_Expr_isAppOfArity___main(x_21, x_2, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_5 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_52; 
x_27 = l_Lean_Expr_appFn_x21(x_21);
x_28 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_29 = l_Lean_Expr_appArg_x21(x_21);
lean_dec(x_21);
x_52 = l_Lean_Expr_isFVar(x_29);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_box(0);
x_30 = x_53;
goto block_51;
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = l_Lean_Expr_fvarId_x21(x_29);
x_55 = lean_name_eq(x_54, x_1);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_box(0);
x_30 = x_56;
goto block_51;
}
else
{
lean_object* x_57; uint8_t x_58; 
lean_inc(x_28);
lean_inc(x_3);
x_57 = l_Lean_MetavarContext_exprDependsOn(x_3, x_28, x_1);
x_58 = lean_unbox(x_57);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_3);
x_59 = l_Lean_LocalDecl_fvarId(x_19);
lean_dec(x_19);
x_60 = 1;
x_61 = lean_box(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_10);
return x_64;
}
else
{
lean_object* x_65; 
x_65 = lean_box(0);
x_30 = x_65;
goto block_51;
}
}
}
block_51:
{
uint8_t x_31; 
lean_dec(x_30);
x_31 = l_Lean_Expr_isFVar(x_28);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_20);
lean_dec(x_19);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_5, x_32);
lean_dec(x_5);
x_5 = x_33;
goto _start;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = l_Lean_Expr_fvarId_x21(x_28);
lean_dec(x_28);
x_36 = lean_name_eq(x_35, x_1);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_29);
lean_dec(x_20);
lean_dec(x_19);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_5, x_37);
lean_dec(x_5);
x_5 = x_38;
goto _start;
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_inc(x_3);
x_40 = l_Lean_MetavarContext_exprDependsOn(x_3, x_29, x_1);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_5);
lean_dec(x_3);
x_42 = l_Lean_LocalDecl_fvarId(x_19);
lean_dec(x_19);
x_43 = 0;
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
if (lean_is_scalar(x_20)) {
 x_46 = lean_alloc_ctor(1, 1, 0);
} else {
 x_46 = x_20;
}
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_10);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_20);
lean_dec(x_19);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_5, x_48);
lean_dec(x_5);
x_5 = x_49;
goto _start;
}
}
}
}
}
}
}
}
}
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_3);
x_11 = l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6(x_1, x_2, x_3, x_14, x_15, x_5, x_6, x_7, x_8, x_13);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_11, 0);
lean_dec(x_18);
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_4, 1);
x_11 = l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("did not find equation for eliminating '");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_subst___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_subst___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid equality proof, it is not of the form (x = t) or (t = x)");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_subst___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_subst___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_subst___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_subst___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = l_Lean_LocalDecl_type(x_3);
x_10 = l_Lean_Expr_eq_x3f___closed__2;
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Expr_isAppOfArity___main(x_9, x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_9);
x_13 = l_Lean_getMCtx___at_Lean_getMVarDecl___spec__1___rarg(x_5, x_6, x_7, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_getLCtx___at___private_Lean_Meta_Basic_3__mkFreshExprMVarCore___spec__1(x_4, x_5, x_6, x_7, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(x_1, x_10, x_14, x_17, x_4, x_5, x_6, x_7, x_18);
lean_dec(x_17);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_mkFVar(x_1);
x_23 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = l_Lean_Meta_subst___lambda__1___closed__3;
x_25 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_27 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_Meta_substCore___lambda__3___closed__2;
x_29 = lean_box(0);
x_30 = l_Lean_Meta_throwTacticEx___rarg(x_28, x_2, x_27, x_29, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; 
lean_dec(x_1);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_dec(x_19);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_box(0);
x_36 = 1;
x_37 = lean_unbox(x_34);
lean_dec(x_34);
x_38 = l_Lean_Meta_substCore(x_2, x_33, x_37, x_35, x_36, x_4, x_5, x_6, x_7, x_32);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_38, 0);
x_43 = lean_ctor_get(x_38, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_38);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_38);
if (x_46 == 0)
{
return x_38;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_38, 0);
x_48 = lean_ctor_get(x_38, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_38);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = l_Lean_Expr_appFn_x21(x_9);
x_51 = l_Lean_Expr_appArg_x21(x_50);
lean_dec(x_50);
x_52 = l_Lean_Expr_appArg_x21(x_9);
x_53 = l_Lean_Expr_isFVar(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = l_Lean_Expr_isFVar(x_51);
lean_dec(x_51);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_1);
x_55 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_55, 0, x_9);
x_56 = l_Lean_indentExpr(x_55);
x_57 = l_Lean_Meta_subst___lambda__1___closed__6;
x_58 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_56);
x_59 = l_Lean_Meta_substCore___lambda__3___closed__2;
x_60 = lean_box(0);
x_61 = l_Lean_Meta_throwTacticEx___rarg(x_59, x_2, x_58, x_60, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_61;
}
else
{
lean_object* x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; 
lean_dec(x_9);
x_62 = lean_box(0);
x_63 = 0;
x_64 = 1;
x_65 = l_Lean_Meta_substCore(x_2, x_1, x_63, x_62, x_64, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
x_66 = !lean_is_exclusive(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_65, 0);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
lean_ctor_set(x_65, 0, x_68);
return x_65;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_65, 0);
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_65);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
uint8_t x_73; 
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
}
else
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; 
lean_dec(x_51);
lean_dec(x_9);
x_77 = lean_box(0);
x_78 = 1;
x_79 = l_Lean_Meta_substCore(x_2, x_1, x_78, x_77, x_78, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
lean_ctor_set(x_79, 0, x_82);
return x_79;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_79, 0);
x_84 = lean_ctor_get(x_79, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_79);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
uint8_t x_87; 
x_87 = !lean_is_exclusive(x_79);
if (x_87 == 0)
{
return x_79;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_79, 0);
x_89 = lean_ctor_get(x_79, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_79);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
}
}
lean_object* l_Lean_Meta_subst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_getLocalDecl___at_Lean_getFVarLocalDecl___spec__1___boxed), 6, 1);
lean_closure_set(x_8, 0, x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_subst___lambda__1___boxed), 8, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_1);
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_getLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_getMVarDecl___at_Lean_isReadOnlyExprMVar___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 4);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l___private_Lean_Meta_Basic_26__withLocalContextImpl___rarg(x_14, x_15, x_10, x_3, x_4, x_5, x_6, x_13);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
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
lean_object* l___private_Lean_Meta_Tactic_Subst_1__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_substCore___lambda__3___closed__20;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Revert(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_Tactic_Subst(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(lean_io_mk_world());
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
l_Lean_Meta_substCore___lambda__2___closed__1 = _init_l_Lean_Meta_substCore___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__2___closed__1);
l_Lean_Meta_substCore___lambda__2___closed__2 = _init_l_Lean_Meta_substCore___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__2___closed__2);
l_Lean_Meta_substCore___lambda__3___closed__1 = _init_l_Lean_Meta_substCore___lambda__3___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__1);
l_Lean_Meta_substCore___lambda__3___closed__2 = _init_l_Lean_Meta_substCore___lambda__3___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__2);
l_Lean_Meta_substCore___lambda__3___closed__3 = _init_l_Lean_Meta_substCore___lambda__3___closed__3();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__3);
l_Lean_Meta_substCore___lambda__3___closed__4 = _init_l_Lean_Meta_substCore___lambda__3___closed__4();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__4);
l_Lean_Meta_substCore___lambda__3___closed__5 = _init_l_Lean_Meta_substCore___lambda__3___closed__5();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__5);
l_Lean_Meta_substCore___lambda__3___closed__6 = _init_l_Lean_Meta_substCore___lambda__3___closed__6();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__6);
l_Lean_Meta_substCore___lambda__3___closed__7 = _init_l_Lean_Meta_substCore___lambda__3___closed__7();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__7);
l_Lean_Meta_substCore___lambda__3___closed__8 = _init_l_Lean_Meta_substCore___lambda__3___closed__8();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__8);
l_Lean_Meta_substCore___lambda__3___closed__9 = _init_l_Lean_Meta_substCore___lambda__3___closed__9();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__9);
l_Lean_Meta_substCore___lambda__3___closed__10 = _init_l_Lean_Meta_substCore___lambda__3___closed__10();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__10);
l_Lean_Meta_substCore___lambda__3___closed__11 = _init_l_Lean_Meta_substCore___lambda__3___closed__11();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__11);
l_Lean_Meta_substCore___lambda__3___closed__12 = _init_l_Lean_Meta_substCore___lambda__3___closed__12();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__12);
l_Lean_Meta_substCore___lambda__3___closed__13 = _init_l_Lean_Meta_substCore___lambda__3___closed__13();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__13);
l_Lean_Meta_substCore___lambda__3___closed__14 = _init_l_Lean_Meta_substCore___lambda__3___closed__14();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__14);
l_Lean_Meta_substCore___lambda__3___closed__15 = _init_l_Lean_Meta_substCore___lambda__3___closed__15();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__15);
l_Lean_Meta_substCore___lambda__3___closed__16 = _init_l_Lean_Meta_substCore___lambda__3___closed__16();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__16);
l_Lean_Meta_substCore___lambda__3___closed__17 = _init_l_Lean_Meta_substCore___lambda__3___closed__17();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__17);
l_Lean_Meta_substCore___lambda__3___closed__18 = _init_l_Lean_Meta_substCore___lambda__3___closed__18();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__18);
l_Lean_Meta_substCore___lambda__3___closed__19 = _init_l_Lean_Meta_substCore___lambda__3___closed__19();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__19);
l_Lean_Meta_substCore___lambda__3___closed__20 = _init_l_Lean_Meta_substCore___lambda__3___closed__20();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__20);
l_Lean_Meta_substCore___lambda__3___closed__21 = _init_l_Lean_Meta_substCore___lambda__3___closed__21();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__21);
l_Lean_Meta_substCore___lambda__3___closed__22 = _init_l_Lean_Meta_substCore___lambda__3___closed__22();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__22);
l_Lean_Meta_substCore___lambda__3___closed__23 = _init_l_Lean_Meta_substCore___lambda__3___closed__23();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__23);
l_Lean_Meta_substCore___lambda__3___closed__24 = _init_l_Lean_Meta_substCore___lambda__3___closed__24();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__24);
l_Lean_Meta_substCore___lambda__3___closed__25 = _init_l_Lean_Meta_substCore___lambda__3___closed__25();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__25);
l_Lean_Meta_substCore___lambda__3___closed__26 = _init_l_Lean_Meta_substCore___lambda__3___closed__26();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__26);
l_Lean_Meta_substCore___lambda__3___closed__27 = _init_l_Lean_Meta_substCore___lambda__3___closed__27();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__27);
l_Lean_Meta_substCore___lambda__3___closed__28 = _init_l_Lean_Meta_substCore___lambda__3___closed__28();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__28);
l_Lean_Meta_substCore___lambda__3___closed__29 = _init_l_Lean_Meta_substCore___lambda__3___closed__29();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__29);
l_Lean_Meta_substCore___lambda__3___closed__30 = _init_l_Lean_Meta_substCore___lambda__3___closed__30();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__30);
l_Lean_Meta_substCore___lambda__3___closed__31 = _init_l_Lean_Meta_substCore___lambda__3___closed__31();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__31);
l_Lean_Meta_substCore___lambda__3___closed__32 = _init_l_Lean_Meta_substCore___lambda__3___closed__32();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__32);
l_Lean_Meta_substCore___lambda__3___closed__33 = _init_l_Lean_Meta_substCore___lambda__3___closed__33();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__33);
l_Lean_Meta_substCore___lambda__3___closed__34 = _init_l_Lean_Meta_substCore___lambda__3___closed__34();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__34);
l_Lean_Meta_substCore___lambda__3___closed__35 = _init_l_Lean_Meta_substCore___lambda__3___closed__35();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__3___closed__35);
l_Lean_Meta_subst___lambda__1___closed__1 = _init_l_Lean_Meta_subst___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__1);
l_Lean_Meta_subst___lambda__1___closed__2 = _init_l_Lean_Meta_subst___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__2);
l_Lean_Meta_subst___lambda__1___closed__3 = _init_l_Lean_Meta_subst___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__3);
l_Lean_Meta_subst___lambda__1___closed__4 = _init_l_Lean_Meta_subst___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__4);
l_Lean_Meta_subst___lambda__1___closed__5 = _init_l_Lean_Meta_subst___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__5);
l_Lean_Meta_subst___lambda__1___closed__6 = _init_l_Lean_Meta_subst___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_subst___lambda__1___closed__6);
res = l___private_Lean_Meta_Tactic_Subst_1__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
