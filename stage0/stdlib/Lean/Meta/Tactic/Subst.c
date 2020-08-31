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
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5___closed__5;
lean_object* l_Lean_Meta_introN(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_MessageData_ofList___closed__3;
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5___closed__15;
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l_Lean_Meta_substCore___lambda__5___closed__18;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__1___closed__7;
lean_object* l_Lean_Meta_subst___lambda__1___closed__4;
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5___closed__7;
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__2;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_23__mkEqRecImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2___boxed(lean_object*, lean_object*);
lean_object* l_List_toString___at_Lean_Meta_substCore___spec__1(lean_object*);
lean_object* l_Lean_Meta_subst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5___closed__16;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_substCore___spec__2___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5___closed__12;
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Meta_substCore___lambda__5___closed__3;
lean_object* l_Lean_Meta_substCore___lambda__2___closed__1;
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5___closed__11;
lean_object* l_Lean_Meta_substCore___lambda__5___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__4___closed__1;
lean_object* l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__4___closed__2;
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Meta_substCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2___closed__2;
lean_object* l_List_toStringAux___main___at_Lean_Meta_substCore___spec__2(uint8_t, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5___closed__17;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___at_Lean_Meta_substCore___spec__6(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5___closed__8;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l___private_Lean_Meta_Basic_23__withLocalDeclImpl___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_getConstInfo___rarg___lambda__1___closed__5;
lean_object* l_Lean_Meta_substCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5___closed__9;
lean_object* l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__6;
lean_object* l_Lean_Meta_substCore___lambda__5___closed__4;
lean_object* l_Lean_Meta_substCore___lambda__5___closed__2;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__4___boxed(lean_object**);
lean_object* l_Lean_Meta_substCore___lambda__1___closed__8;
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5___closed__19;
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__1___closed__9;
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__1___closed__4;
lean_object* l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__3;
lean_object* l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5___closed__22;
lean_object* l_Lean_Meta_substCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
lean_object* l_Lean_Meta_subst___lambda__1___closed__5;
lean_object* l_Lean_Meta_substCore___lambda__5___closed__14;
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Meta_substCore___lambda__5___closed__23;
lean_object* l___private_Lean_Meta_AppBuilder_3__mkEqImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___at_Lean_Meta_substCore___spec__6___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5___closed__13;
lean_object* l_Lean_Meta_substCore___lambda__5___closed__20;
lean_object* l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5___closed__21;
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Meta_substCore___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5___closed__6;
lean_object* l_Lean_Meta_substCore___lambda__1___closed__1;
lean_object* l___private_Lean_Meta_Tactic_Subst_1__regTraceClasses(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5___closed__10;
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_substCore___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkEqRec___at_Lean_Meta_substCore___spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2___closed__3;
extern lean_object* l_System_FilePath_dirName___closed__1;
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__1___closed__3;
lean_object* l_Lean_Meta_subst___lambda__1___closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_getMVarTag___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__5(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__1___closed__5;
lean_object* l_Lean_Meta_substCore___lambda__1___closed__6;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_substCore___spec__2(uint8_t x_1, lean_object* x_2) {
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
x_10 = l_List_toStringAux___main___at_Lean_Meta_substCore___spec__2(x_1, x_5);
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
x_18 = l_List_toStringAux___main___at_Lean_Meta_substCore___spec__2(x_17, x_14);
x_19 = lean_string_append(x_16, x_18);
lean_dec(x_18);
return x_19;
}
}
}
}
lean_object* l_List_toString___at_Lean_Meta_substCore___spec__1(lean_object* x_1) {
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
x_4 = l_List_toStringAux___main___at_Lean_Meta_substCore___spec__2(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Meta_mkEqNDRec___at_Lean_Meta_substCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
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
lean_object* l_Lean_Meta_mkEqSymm___at_Lean_Meta_substCore___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at_Lean_Meta_substCore___spec__6___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = 0;
x_10 = l___private_Lean_Meta_Basic_23__withLocalDeclImpl___rarg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
lean_object* l_Lean_Meta_withLocalDeclD___at_Lean_Meta_substCore___spec__6(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDeclD___at_Lean_Meta_substCore___spec__6___rarg), 8, 0);
return x_2;
}
}
lean_object* l_Lean_Meta_mkEqRec___at_Lean_Meta_substCore___spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_AppBuilder_23__mkEqRecImp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* _init_l_Lean_Meta_substCore___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("substituting ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__1___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(" (id: ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__1___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__1___closed__4;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__1___closed__5;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__1___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string(") with ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__1___closed__7;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__1___closed__8;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_5, 0, x_1);
x_6 = l_Lean_Meta_substCore___lambda__1___closed__3;
x_7 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
x_8 = l_Lean_Meta_substCore___lambda__1___closed__6;
x_9 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_10, 0, x_2);
x_11 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = l_Lean_Meta_substCore___lambda__1___closed__9;
x_13 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_14, 0, x_3);
x_15 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__2___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reverted variables ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__2___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__2___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__2___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__2___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore___lambda__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = l_Array_toList___rarg(x_1);
x_4 = l_List_toString___at_Lean_Meta_substCore___spec__1(x_3);
x_5 = l_Array_HasRepr___rarg___closed__1;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_Meta_substCore___lambda__2___closed__3;
x_10 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
lean_object* l_Lean_Meta_substCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_11 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp(x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* _init_l_Lean_Meta_substCore___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("_h");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__4___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_substCore___lambda__4___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_substCore___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, uint8_t x_12, uint8_t x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_16, 2);
lean_inc(x_22);
lean_dec(x_16);
lean_inc(x_17);
lean_inc(x_1);
x_23 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_1, x_17, x_18, x_19, x_20, x_21);
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
x_353 = l___private_Lean_Meta_Basic_9__isClassQuick_x3f___main___closed__1;
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
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_st_ref_get(x_18, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_22);
x_31 = l_Lean_MetavarContext_exprDependsOn(x_30, x_22, x_1);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_14);
x_33 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2);
x_34 = lean_array_push(x_33, x_2);
lean_inc(x_17);
lean_inc(x_22);
x_35 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_34, x_22, x_17, x_18, x_19, x_20, x_29);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_2);
x_38 = l_Lean_Expr_replaceFVar(x_22, x_2, x_26);
lean_dec(x_22);
if (x_13 == 0)
{
lean_object* x_127; 
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_10);
x_127 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp(x_10, x_17, x_18, x_19, x_20, x_37);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
x_39 = x_128;
x_40 = x_129;
goto block_126;
}
else
{
uint8_t x_130; 
lean_dec(x_38);
lean_dec(x_36);
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
x_130 = !lean_is_exclusive(x_127);
if (x_130 == 0)
{
return x_127;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_127, 0);
x_132 = lean_ctor_get(x_127, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_127);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
lean_inc(x_10);
x_39 = x_10;
x_40 = x_37;
goto block_126;
}
block_126:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_17);
x_41 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_38, x_3, x_17, x_18, x_19, x_20, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_42);
x_44 = l___private_Lean_Meta_AppBuilder_22__mkEqNDRecImp(x_36, x_42, x_39, x_17, x_18, x_19, x_20, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(x_4, x_45, x_17, x_18, x_19, x_20, x_46);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_Expr_mvarId_x21(x_42);
lean_dec(x_42);
if (x_12 == 0)
{
uint8_t x_120; 
x_120 = 0;
x_50 = x_120;
goto block_119;
}
else
{
uint8_t x_121; 
x_121 = 1;
x_50 = x_121;
goto block_119;
}
block_119:
{
lean_object* x_51; lean_object* x_52; 
if (x_50 == 0)
{
lean_dec(x_11);
lean_dec(x_1);
x_51 = x_49;
x_52 = x_48;
goto block_104;
}
else
{
lean_object* x_105; 
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_105 = l_Lean_Meta_clear(x_49, x_1, x_17, x_18, x_19, x_20, x_48);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_108 = l_Lean_Meta_clear(x_106, x_11, x_17, x_18, x_19, x_20, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_51 = x_109;
x_52 = x_110;
goto block_104;
}
else
{
uint8_t x_111; 
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
x_111 = !lean_is_exclusive(x_108);
if (x_111 == 0)
{
return x_108;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_108, 0);
x_113 = lean_ctor_get(x_108, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_108);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
uint8_t x_115; 
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
x_115 = !lean_is_exclusive(x_105);
if (x_115 == 0)
{
return x_105;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_105, 0);
x_117 = lean_ctor_get(x_105, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_105);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
block_104:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_53 = lean_array_get_size(x_5);
x_54 = lean_unsigned_to_nat(2u);
x_55 = lean_nat_sub(x_53, x_54);
lean_dec(x_53);
x_56 = 0;
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_57 = l_Lean_Meta_introN(x_51, x_55, x_6, x_56, x_17, x_18, x_19, x_20, x_52);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_58, 0);
x_62 = lean_array_get_size(x_61);
lean_inc(x_62);
x_63 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__4(x_5, x_61, x_62, x_62, x_7, x_17, x_18, x_19, x_20, x_59);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_62);
lean_dec(x_61);
if (x_50 == 0)
{
uint8_t x_64; 
lean_dec(x_26);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_63, 0);
x_66 = l_Lean_Meta_FVarSubst_insert(x_65, x_8, x_2);
x_67 = l_Lean_Meta_FVarSubst_insert(x_66, x_9, x_10);
lean_ctor_set(x_58, 0, x_67);
lean_ctor_set(x_63, 0, x_58);
return x_63;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_68 = lean_ctor_get(x_63, 0);
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_63);
x_70 = l_Lean_Meta_FVarSubst_insert(x_68, x_8, x_2);
x_71 = l_Lean_Meta_FVarSubst_insert(x_70, x_9, x_10);
lean_ctor_set(x_58, 0, x_71);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_58);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
else
{
uint8_t x_73; 
lean_dec(x_2);
x_73 = !lean_is_exclusive(x_63);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_63, 0);
x_75 = l_Lean_Meta_FVarSubst_insert(x_74, x_8, x_26);
x_76 = l_Lean_Meta_FVarSubst_insert(x_75, x_9, x_10);
lean_ctor_set(x_58, 0, x_76);
lean_ctor_set(x_63, 0, x_58);
return x_63;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_63, 0);
x_78 = lean_ctor_get(x_63, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_63);
x_79 = l_Lean_Meta_FVarSubst_insert(x_77, x_8, x_26);
x_80 = l_Lean_Meta_FVarSubst_insert(x_79, x_9, x_10);
lean_ctor_set(x_58, 0, x_80);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_58);
lean_ctor_set(x_81, 1, x_78);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_58, 0);
x_83 = lean_ctor_get(x_58, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_58);
x_84 = lean_array_get_size(x_82);
lean_inc(x_84);
x_85 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__4(x_5, x_82, x_84, x_84, x_7, x_17, x_18, x_19, x_20, x_59);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_84);
lean_dec(x_82);
if (x_50 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_26);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_88 = x_85;
} else {
 lean_dec_ref(x_85);
 x_88 = lean_box(0);
}
x_89 = l_Lean_Meta_FVarSubst_insert(x_86, x_8, x_2);
x_90 = l_Lean_Meta_FVarSubst_insert(x_89, x_9, x_10);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_83);
if (lean_is_scalar(x_88)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_88;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_87);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_2);
x_93 = lean_ctor_get(x_85, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_85, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_95 = x_85;
} else {
 lean_dec_ref(x_85);
 x_95 = lean_box(0);
}
x_96 = l_Lean_Meta_FVarSubst_insert(x_93, x_8, x_26);
x_97 = l_Lean_Meta_FVarSubst_insert(x_96, x_9, x_10);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_83);
if (lean_is_scalar(x_95)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_95;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_94);
return x_99;
}
}
}
else
{
uint8_t x_100; 
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
x_100 = !lean_is_exclusive(x_57);
if (x_100 == 0)
{
return x_57;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_57, 0);
x_102 = lean_ctor_get(x_57, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_57);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_42);
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
x_122 = !lean_is_exclusive(x_44);
if (x_122 == 0)
{
return x_44;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_44, 0);
x_124 = lean_ctor_get(x_44, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_44);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
else
{
uint8_t x_134; 
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
x_134 = !lean_is_exclusive(x_35);
if (x_134 == 0)
{
return x_35;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_35, 0);
x_136 = lean_ctor_get(x_35, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_35);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; 
lean_inc(x_2);
x_138 = l_Lean_Expr_replaceFVar(x_22, x_2, x_26);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_26);
x_139 = l___private_Lean_Meta_AppBuilder_5__mkEqReflImp(x_26, x_17, x_18, x_19, x_20, x_29);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
lean_inc(x_10);
x_142 = l_Lean_Expr_replaceFVar(x_138, x_10, x_140);
lean_dec(x_140);
lean_dec(x_138);
if (x_13 == 0)
{
lean_object* x_143; 
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_2);
lean_inc(x_26);
x_143 = l___private_Lean_Meta_AppBuilder_3__mkEqImp(x_26, x_2, x_17, x_18, x_19, x_20, x_141);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
lean_inc(x_2);
lean_inc(x_10);
x_146 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__3___boxed), 10, 4);
lean_closure_set(x_146, 0, x_22);
lean_closure_set(x_146, 1, x_10);
lean_closure_set(x_146, 2, x_14);
lean_closure_set(x_146, 3, x_2);
x_147 = l_Lean_Meta_substCore___lambda__4___closed__2;
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_148 = l_Lean_Meta_withLocalDeclD___at_Lean_Meta_substCore___spec__6___rarg(x_147, x_144, x_146, x_17, x_18, x_19, x_20, x_145);
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
x_151 = l___private_Lean_Meta_AppBuilder_10__mkEqSymmImp(x_10, x_17, x_18, x_19, x_20, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
lean_inc(x_17);
x_154 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_142, x_3, x_17, x_18, x_19, x_20, x_153);
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
x_157 = l___private_Lean_Meta_AppBuilder_23__mkEqRecImp(x_149, x_155, x_152, x_17, x_18, x_19, x_20, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(x_4, x_158, x_17, x_18, x_19, x_20, x_159);
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
x_176 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__8(x_5, x_174, x_175, x_175, x_7, x_17, x_18, x_19, x_20, x_172);
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
x_198 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__8(x_5, x_195, x_197, x_197, x_7, x_17, x_18, x_19, x_20, x_172);
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
lean_dec(x_142);
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
lean_dec(x_142);
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
lean_dec(x_142);
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
x_247 = !lean_is_exclusive(x_143);
if (x_247 == 0)
{
return x_143;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_143, 0);
x_249 = lean_ctor_get(x_143, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_143);
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
lean_inc(x_17);
x_253 = l_Lean_Meta_mkLambdaFVars___at_Lean_Meta_SynthInstance_tryResolveCore___spec__1(x_252, x_22, x_17, x_18, x_19, x_20, x_141);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
lean_inc(x_17);
x_256 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_142, x_3, x_17, x_18, x_19, x_20, x_255);
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
x_259 = l___private_Lean_Meta_AppBuilder_23__mkEqRecImp(x_254, x_257, x_10, x_17, x_18, x_19, x_20, x_258);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_ctor_get(x_259, 1);
lean_inc(x_261);
lean_dec(x_259);
x_262 = l_Lean_Meta_assignExprMVar___at___private_Lean_Meta_InferType_4__getLevelImp___spec__3(x_4, x_260, x_17, x_18, x_19, x_20, x_261);
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
x_278 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__9(x_5, x_276, x_277, x_277, x_7, x_17, x_18, x_19, x_20, x_274);
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
x_300 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__9(x_5, x_297, x_299, x_299, x_7, x_17, x_18, x_19, x_20, x_274);
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
lean_dec(x_142);
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
lean_dec(x_138);
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
x_345 = !lean_is_exclusive(x_139);
if (x_345 == 0)
{
return x_139;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_139, 0);
x_347 = lean_ctor_get(x_139, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_139);
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
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("subst");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_substCore___lambda__5___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("argument must be an equality proof");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__5___closed__3;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__5___closed__4;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("invalid equality proof, it is not of the form ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__5___closed__6;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__5___closed__7;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("after WHNF, variable expected, but obtained");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__5___closed__9;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__5___closed__10;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__12() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(x = t)");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__5___closed__12;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__5___closed__13;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__5___closed__8;
x_2 = l_Lean_Meta_substCore___lambda__5___closed__14;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(t = x)");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__5___closed__16;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__5___closed__17;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__5___closed__8;
x_2 = l_Lean_Meta_substCore___lambda__5___closed__18;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_substCore___lambda__5___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' occurs at");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__5___closed__21;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__5___closed__23() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__5___closed__22;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore___lambda__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Meta_substCore___lambda__5___closed__2;
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
x_22 = l_Lean_Meta_substCore___lambda__5___closed__5;
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
uint8_t x_157; 
x_157 = 0;
x_28 = x_157;
goto block_156;
}
else
{
uint8_t x_158; 
x_158 = 1;
x_28 = x_158;
goto block_156;
}
block_156:
{
lean_object* x_29; 
if (x_28 == 0)
{
lean_inc(x_26);
x_29 = x_26;
goto block_155;
}
else
{
lean_inc(x_27);
x_29 = x_27;
goto block_155;
}
block_155:
{
lean_object* x_30; 
if (x_28 == 0)
{
lean_dec(x_26);
x_30 = x_27;
goto block_154;
}
else
{
lean_dec(x_27);
x_30 = x_26;
goto block_154;
}
block_154:
{
lean_object* x_31; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_31 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_29, x_7, x_8, x_9, x_10, x_17);
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
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
lean_dec(x_18);
x_58 = lean_ctor_get(x_32, 0);
lean_inc(x_58);
lean_inc(x_30);
lean_inc(x_58);
lean_inc(x_32);
x_59 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__1___boxed), 4, 3);
lean_closure_set(x_59, 0, x_32);
lean_closure_set(x_59, 1, x_58);
lean_closure_set(x_59, 2, x_30);
x_60 = l_Lean_Meta_substCore___lambda__5___closed__20;
x_61 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_60, x_59, x_7, x_8, x_9, x_10, x_33);
x_62 = lean_ctor_get(x_61, 1);
lean_inc(x_62);
lean_dec(x_61);
x_129 = lean_st_ref_get(x_8, x_62);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
lean_dec(x_130);
lean_inc(x_30);
x_133 = l_Lean_MetavarContext_exprDependsOn(x_132, x_30, x_58);
x_134 = lean_unbox(x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_dec(x_32);
lean_dec(x_30);
x_63 = x_131;
goto block_128;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
lean_dec(x_58);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_135 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_135, 0, x_32);
x_136 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_137 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_135);
x_138 = l_Lean_Meta_substCore___lambda__5___closed__23;
x_139 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_140, 0, x_30);
x_141 = l_Lean_indentExpr(x_140);
x_142 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_box(0);
x_144 = l_Lean_Meta_throwTacticEx___rarg(x_12, x_1, x_142, x_143, x_7, x_8, x_9, x_10, x_131);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
return x_144;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_144, 0);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_144);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
block_128:
{
lean_object* x_64; 
lean_inc(x_7);
lean_inc(x_58);
x_64 = l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1(x_58, x_7, x_8, x_9, x_10, x_63);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = l_Lean_mkAppStx___closed__9;
lean_inc(x_58);
x_67 = lean_array_push(x_66, x_58);
lean_inc(x_2);
x_68 = lean_array_push(x_67, x_2);
x_69 = 1;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_70 = l_Lean_Meta_revert(x_1, x_68, x_69, x_7, x_8, x_9, x_10, x_65);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_dec(x_71);
x_75 = lean_box(0);
x_76 = lean_unsigned_to_nat(2u);
x_77 = 0;
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_78 = l_Lean_Meta_introN(x_74, x_76, x_75, x_77, x_7, x_8, x_9, x_10, x_72);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
lean_inc(x_73);
x_83 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__2___boxed), 2, 1);
lean_closure_set(x_83, 0, x_73);
x_84 = l_Lean_MonadTracer_trace___at_Lean_Meta_isTypeCorrect___spec__1(x_60, x_83, x_7, x_8, x_9, x_10, x_80);
x_85 = lean_ctor_get(x_84, 1);
lean_inc(x_85);
lean_dec(x_84);
x_86 = l_Lean_Name_inhabited;
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_array_get(x_86, x_81, x_87);
lean_inc(x_88);
x_89 = l_Lean_mkFVar(x_88);
x_90 = lean_unsigned_to_nat(1u);
x_91 = lean_array_get(x_86, x_81, x_90);
lean_dec(x_81);
lean_inc(x_91);
x_92 = l_Lean_mkFVar(x_91);
lean_inc(x_82);
x_93 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1___boxed), 6, 1);
lean_closure_set(x_93, 0, x_82);
x_94 = lean_box(x_4);
x_95 = lean_box(x_28);
lean_inc(x_82);
x_96 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__4___boxed), 21, 15);
lean_closure_set(x_96, 0, x_91);
lean_closure_set(x_96, 1, x_89);
lean_closure_set(x_96, 2, x_6);
lean_closure_set(x_96, 3, x_82);
lean_closure_set(x_96, 4, x_73);
lean_closure_set(x_96, 5, x_75);
lean_closure_set(x_96, 6, x_3);
lean_closure_set(x_96, 7, x_58);
lean_closure_set(x_96, 8, x_2);
lean_closure_set(x_96, 9, x_92);
lean_closure_set(x_96, 10, x_88);
lean_closure_set(x_96, 11, x_94);
lean_closure_set(x_96, 12, x_95);
lean_closure_set(x_96, 13, x_66);
lean_closure_set(x_96, 14, x_19);
x_97 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_97, 0, x_93);
lean_closure_set(x_97, 1, x_96);
x_98 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_82, x_7, x_8, x_9, x_10, x_85);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 4);
lean_inc(x_102);
lean_dec(x_99);
x_103 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_101, x_102, x_97, x_7, x_8, x_9, x_10, x_100);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
return x_103;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_103, 0);
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_103);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
else
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_103);
if (x_108 == 0)
{
return x_103;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_103, 0);
x_110 = lean_ctor_get(x_103, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_103);
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
lean_dec(x_97);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_112 = !lean_is_exclusive(x_98);
if (x_112 == 0)
{
return x_98;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_98, 0);
x_114 = lean_ctor_get(x_98, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_98);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_73);
lean_dec(x_58);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_116 = !lean_is_exclusive(x_78);
if (x_116 == 0)
{
return x_78;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_78, 0);
x_118 = lean_ctor_get(x_78, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_78);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
uint8_t x_120; 
lean_dec(x_58);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_120 = !lean_is_exclusive(x_70);
if (x_120 == 0)
{
return x_70;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_70, 0);
x_122 = lean_ctor_get(x_70, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_70);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
else
{
uint8_t x_124; 
lean_dec(x_58);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_64);
if (x_124 == 0)
{
return x_64;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_64, 0);
x_126 = lean_ctor_get(x_64, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_64);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
else
{
lean_object* x_149; 
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_149 = lean_box(0);
x_34 = x_149;
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
x_39 = l_Lean_Meta_substCore___lambda__5___closed__15;
x_40 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
x_41 = l_Lean_MessageData_ofList___closed__3;
x_42 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Meta_substCore___lambda__5___closed__11;
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
x_48 = l_Lean_Meta_substCore___lambda__5___closed__19;
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_36);
x_50 = l_Lean_MessageData_ofList___closed__3;
x_51 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_Meta_substCore___lambda__5___closed__11;
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
uint8_t x_150; 
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
x_150 = !lean_is_exclusive(x_31);
if (x_150 == 0)
{
return x_31;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_31, 0);
x_152 = lean_ctor_get(x_31, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_31);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
}
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_15);
if (x_159 == 0)
{
return x_15;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_15, 0);
x_161 = lean_ctor_get(x_15, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_15);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_163 = !lean_is_exclusive(x_13);
if (x_163 == 0)
{
return x_13;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_13, 0);
x_165 = lean_ctor_get(x_13, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_13);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
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
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__5___boxed), 11, 5);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_4);
lean_closure_set(x_14, 3, x_12);
lean_closure_set(x_14, 4, x_13);
x_15 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_15, 0, x_11);
lean_closure_set(x_15, 1, x_14);
x_16 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_1, x_6, x_7, x_8, x_9, x_10);
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
x_21 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_19, x_20, x_15, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
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
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_21);
if (x_26 == 0)
{
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_30 = !lean_is_exclusive(x_16);
if (x_30 == 0)
{
return x_16;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_16, 0);
x_32 = lean_ctor_get(x_16, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_16);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
lean_object* l_List_toStringAux___main___at_Lean_Meta_substCore___spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at_Lean_Meta_substCore___spec__2(x_3, x_2);
return x_4;
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
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* l_Lean_Meta_substCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_substCore___lambda__1(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* l_Lean_Meta_substCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_substCore___lambda__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* l_Lean_Meta_substCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_substCore___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
lean_object* l_Lean_Meta_substCore___lambda__4___boxed(lean_object** _args) {
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
x_24 = l_Lean_Meta_substCore___lambda__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22, x_23, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_15);
lean_dec(x_5);
return x_24;
}
}
lean_object* l_Lean_Meta_substCore___lambda__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Meta_substCore___lambda__5(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
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
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_9);
x_13 = lean_st_ref_get(x_5, x_8);
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
x_18 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(x_1, x_10, x_16, x_17, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_17);
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
x_23 = l_Lean_Meta_subst___lambda__1___closed__3;
x_24 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
x_25 = l_Lean_getConstInfo___rarg___lambda__1___closed__5;
x_26 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_Meta_substCore___lambda__5___closed__2;
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
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = l_Lean_Expr_appFn_x21(x_9);
x_50 = l_Lean_Expr_appArg_x21(x_49);
lean_dec(x_49);
x_51 = l_Lean_Expr_appArg_x21(x_9);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_52 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_51, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = l_Lean_Expr_isFVar(x_53);
lean_dec(x_53);
if (x_55 == 0)
{
lean_object* x_56; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_56 = l_Lean_Meta_whnf___at___private_Lean_Meta_Basic_15__isClassExpensive_x3f___main___spec__2(x_50, x_4, x_5, x_6, x_7, x_54);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = l_Lean_Expr_isFVar(x_57);
lean_dec(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_1);
x_60 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_60, 0, x_9);
x_61 = l_Lean_indentExpr(x_60);
x_62 = l_Lean_Meta_subst___lambda__1___closed__6;
x_63 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = l_Lean_Meta_substCore___lambda__5___closed__2;
x_65 = lean_box(0);
x_66 = l_Lean_Meta_throwTacticEx___rarg(x_64, x_2, x_63, x_65, x_4, x_5, x_6, x_7, x_58);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_66;
}
else
{
lean_object* x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; 
lean_dec(x_9);
x_67 = lean_box(0);
x_68 = 0;
x_69 = 1;
x_70 = l_Lean_Meta_substCore(x_2, x_1, x_68, x_67, x_69, x_4, x_5, x_6, x_7, x_58);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
lean_ctor_set(x_70, 0, x_73);
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_70, 0);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_70);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_70);
if (x_78 == 0)
{
return x_70;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_70, 0);
x_80 = lean_ctor_get(x_70, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_70);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_56);
if (x_82 == 0)
{
return x_56;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_56, 0);
x_84 = lean_ctor_get(x_56, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_56);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
lean_object* x_86; uint8_t x_87; lean_object* x_88; 
lean_dec(x_50);
lean_dec(x_9);
x_86 = lean_box(0);
x_87 = 1;
x_88 = l_Lean_Meta_substCore(x_2, x_1, x_87, x_86, x_87, x_4, x_5, x_6, x_7, x_54);
if (lean_obj_tag(x_88) == 0)
{
uint8_t x_89; 
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
lean_ctor_set(x_88, 0, x_91);
return x_88;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_88, 0);
x_93 = lean_ctor_get(x_88, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_88);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_88);
if (x_96 == 0)
{
return x_88;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_88, 0);
x_98 = lean_ctor_get(x_88, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_88);
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
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_52);
if (x_100 == 0)
{
return x_52;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_52, 0);
x_102 = lean_ctor_get(x_52, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_52);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
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
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl___at_Lean_Meta_getFVarLocalDecl___spec__1___boxed), 6, 1);
lean_closure_set(x_8, 0, x_2);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_subst___lambda__1___boxed), 8, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_1);
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_Lean_MonadLCtx___spec__2___rarg), 7, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_Meta_getMVarDecl___at_Lean_Meta_isReadOnlyExprMVar___spec__1(x_1, x_3, x_4, x_5, x_6, x_7);
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
x_16 = l___private_Lean_Meta_Basic_27__withLocalContextImpl___rarg(x_14, x_15, x_10, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
return x_16;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_16);
if (x_21 == 0)
{
return x_16;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_16, 0);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_16);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
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
x_2 = l_Lean_Meta_substCore___lambda__5___closed__20;
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
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
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
l_Lean_Meta_substCore___lambda__1___closed__1 = _init_l_Lean_Meta_substCore___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__1___closed__1);
l_Lean_Meta_substCore___lambda__1___closed__2 = _init_l_Lean_Meta_substCore___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__1___closed__2);
l_Lean_Meta_substCore___lambda__1___closed__3 = _init_l_Lean_Meta_substCore___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__1___closed__3);
l_Lean_Meta_substCore___lambda__1___closed__4 = _init_l_Lean_Meta_substCore___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__1___closed__4);
l_Lean_Meta_substCore___lambda__1___closed__5 = _init_l_Lean_Meta_substCore___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__1___closed__5);
l_Lean_Meta_substCore___lambda__1___closed__6 = _init_l_Lean_Meta_substCore___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__1___closed__6);
l_Lean_Meta_substCore___lambda__1___closed__7 = _init_l_Lean_Meta_substCore___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__1___closed__7);
l_Lean_Meta_substCore___lambda__1___closed__8 = _init_l_Lean_Meta_substCore___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__1___closed__8);
l_Lean_Meta_substCore___lambda__1___closed__9 = _init_l_Lean_Meta_substCore___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__1___closed__9);
l_Lean_Meta_substCore___lambda__2___closed__1 = _init_l_Lean_Meta_substCore___lambda__2___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__2___closed__1);
l_Lean_Meta_substCore___lambda__2___closed__2 = _init_l_Lean_Meta_substCore___lambda__2___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__2___closed__2);
l_Lean_Meta_substCore___lambda__2___closed__3 = _init_l_Lean_Meta_substCore___lambda__2___closed__3();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__2___closed__3);
l_Lean_Meta_substCore___lambda__4___closed__1 = _init_l_Lean_Meta_substCore___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__4___closed__1);
l_Lean_Meta_substCore___lambda__4___closed__2 = _init_l_Lean_Meta_substCore___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__4___closed__2);
l_Lean_Meta_substCore___lambda__5___closed__1 = _init_l_Lean_Meta_substCore___lambda__5___closed__1();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__1);
l_Lean_Meta_substCore___lambda__5___closed__2 = _init_l_Lean_Meta_substCore___lambda__5___closed__2();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__2);
l_Lean_Meta_substCore___lambda__5___closed__3 = _init_l_Lean_Meta_substCore___lambda__5___closed__3();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__3);
l_Lean_Meta_substCore___lambda__5___closed__4 = _init_l_Lean_Meta_substCore___lambda__5___closed__4();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__4);
l_Lean_Meta_substCore___lambda__5___closed__5 = _init_l_Lean_Meta_substCore___lambda__5___closed__5();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__5);
l_Lean_Meta_substCore___lambda__5___closed__6 = _init_l_Lean_Meta_substCore___lambda__5___closed__6();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__6);
l_Lean_Meta_substCore___lambda__5___closed__7 = _init_l_Lean_Meta_substCore___lambda__5___closed__7();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__7);
l_Lean_Meta_substCore___lambda__5___closed__8 = _init_l_Lean_Meta_substCore___lambda__5___closed__8();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__8);
l_Lean_Meta_substCore___lambda__5___closed__9 = _init_l_Lean_Meta_substCore___lambda__5___closed__9();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__9);
l_Lean_Meta_substCore___lambda__5___closed__10 = _init_l_Lean_Meta_substCore___lambda__5___closed__10();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__10);
l_Lean_Meta_substCore___lambda__5___closed__11 = _init_l_Lean_Meta_substCore___lambda__5___closed__11();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__11);
l_Lean_Meta_substCore___lambda__5___closed__12 = _init_l_Lean_Meta_substCore___lambda__5___closed__12();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__12);
l_Lean_Meta_substCore___lambda__5___closed__13 = _init_l_Lean_Meta_substCore___lambda__5___closed__13();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__13);
l_Lean_Meta_substCore___lambda__5___closed__14 = _init_l_Lean_Meta_substCore___lambda__5___closed__14();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__14);
l_Lean_Meta_substCore___lambda__5___closed__15 = _init_l_Lean_Meta_substCore___lambda__5___closed__15();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__15);
l_Lean_Meta_substCore___lambda__5___closed__16 = _init_l_Lean_Meta_substCore___lambda__5___closed__16();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__16);
l_Lean_Meta_substCore___lambda__5___closed__17 = _init_l_Lean_Meta_substCore___lambda__5___closed__17();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__17);
l_Lean_Meta_substCore___lambda__5___closed__18 = _init_l_Lean_Meta_substCore___lambda__5___closed__18();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__18);
l_Lean_Meta_substCore___lambda__5___closed__19 = _init_l_Lean_Meta_substCore___lambda__5___closed__19();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__19);
l_Lean_Meta_substCore___lambda__5___closed__20 = _init_l_Lean_Meta_substCore___lambda__5___closed__20();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__20);
l_Lean_Meta_substCore___lambda__5___closed__21 = _init_l_Lean_Meta_substCore___lambda__5___closed__21();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__21);
l_Lean_Meta_substCore___lambda__5___closed__22 = _init_l_Lean_Meta_substCore___lambda__5___closed__22();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__22);
l_Lean_Meta_substCore___lambda__5___closed__23 = _init_l_Lean_Meta_substCore___lambda__5___closed__23();
lean_mark_persistent(l_Lean_Meta_substCore___lambda__5___closed__23);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
