// Lean compiler output
// Module: Lean.Meta.Tactic.Subst
// Imports: Init Lean.Meta.AppBuilder Lean.Meta.Message Lean.Meta.Tactic.Util Lean.Meta.Tactic.Revert Lean.Meta.Tactic.Intro Lean.Meta.Tactic.Clear Lean.Meta.Tactic.FVarSubst
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
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_toString___closed__1;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__2;
lean_object* l_Lean_Meta_substCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__17;
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__1;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__27;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__4;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__4;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__1;
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__8;
lean_object* l_Lean_Meta_subst___lambda__1___closed__2;
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__6;
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__23;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__13;
extern lean_object* l_Lean_Name_inhabited;
extern lean_object* l_String_splitAux___main___closed__1;
lean_object* l_Lean_Meta_substCore___lambda__2___closed__1;
extern lean_object* l_List_repr___rarg___closed__3;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__21;
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__31;
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__11;
extern lean_object* l_Array_HasRepr___rarg___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__12;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2___closed__2;
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_clear(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__9;
lean_object* l_Lean_Meta_subst___lambda__1___closed__6;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__19;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_List_repr___rarg___closed__2;
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
extern lean_object* l_List_reprAux___main___rarg___closed__1;
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__10;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__32;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__20;
lean_object* l_Lean_Meta_subst___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__24;
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_substCore___spec__5___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnf(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__7;
lean_object* l_Lean_Meta_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__16;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__3;
lean_object* l_Lean_Meta_substCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__26;
lean_object* l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__5;
lean_object* l_List_toString___at_Lean_Meta_substCore___spec__4(lean_object*);
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__22;
uint8_t l_Lean_Expr_isFVar(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__5;
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toList___rarg(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__14;
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__25;
extern lean_object* l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
lean_object* l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Tactic_Subst_1__regTraceClasses(lean_object*);
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_mkOptionalNode___closed__2;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__29;
extern lean_object* l_Lean_Meta_isClassQuick___main___closed__1;
lean_object* l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_toStringAux___main___at_Lean_Meta_substCore___spec__5(uint8_t, lean_object*);
lean_object* l_Lean_Name_toStringWithSep___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__28;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__1;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__30;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_getMVarTag___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__3;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__18;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__15;
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_add(x_13, x_14);
x_16 = l_Lean_Name_inhabited;
x_17 = lean_array_get(x_16, x_1, x_15);
lean_dec(x_15);
x_18 = lean_array_get(x_16, x_2, x_13);
lean_dec(x_13);
x_19 = l_Lean_mkFVar(x_18);
x_20 = l_Lean_Meta_FVarSubst_insert(x_5, x_17, x_19);
x_4 = x_11;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_4);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_add(x_13, x_14);
x_16 = l_Lean_Name_inhabited;
x_17 = lean_array_get(x_16, x_1, x_15);
lean_dec(x_15);
x_18 = lean_array_get(x_16, x_2, x_13);
lean_dec(x_13);
x_19 = l_Lean_mkFVar(x_18);
x_20 = l_Lean_Meta_FVarSubst_insert(x_5, x_17, x_19);
x_4 = x_11;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_4);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_12 = lean_nat_sub(x_3, x_11);
x_13 = lean_nat_sub(x_12, x_10);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_add(x_13, x_14);
x_16 = l_Lean_Name_inhabited;
x_17 = lean_array_get(x_16, x_1, x_15);
lean_dec(x_15);
x_18 = lean_array_get(x_16, x_2, x_13);
lean_dec(x_13);
x_19 = l_Lean_mkFVar(x_18);
x_20 = l_Lean_Meta_FVarSubst_insert(x_5, x_17, x_19);
x_4 = x_11;
x_5 = x_20;
goto _start;
}
else
{
lean_object* x_22; 
lean_dec(x_4);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
}
}
lean_object* l_List_toStringAux___main___at_Lean_Meta_substCore___spec__5(uint8_t x_1, lean_object* x_2) {
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
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Name_toStringWithSep___main(x_6, x_4);
x_8 = l_List_reprAux___main___rarg___closed__1;
x_9 = lean_string_append(x_8, x_7);
lean_dec(x_7);
x_10 = l_List_toStringAux___main___at_Lean_Meta_substCore___spec__5(x_1, x_5);
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
x_15 = l_Lean_Name_toString___closed__1;
x_16 = l_Lean_Name_toStringWithSep___main(x_15, x_13);
x_17 = 0;
x_18 = l_List_toStringAux___main___at_Lean_Meta_substCore___spec__5(x_17, x_14);
x_19 = lean_string_append(x_16, x_18);
lean_dec(x_18);
return x_19;
}
}
}
}
lean_object* l_List_toString___at_Lean_Meta_substCore___spec__4(lean_object* x_1) {
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
x_4 = l_List_toStringAux___main___at_Lean_Meta_substCore___spec__5(x_3, x_1);
x_5 = l_List_repr___rarg___closed__2;
x_6 = lean_string_append(x_5, x_4);
lean_dec(x_4);
x_7 = l_List_repr___rarg___closed__3;
x_8 = lean_string_append(x_6, x_7);
return x_8;
}
}
}
lean_object* l_Lean_Meta_substCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = l_Lean_Meta_mkEqSymm(x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Expr_replaceFVar(x_1, x_2, x_9);
lean_dec(x_9);
x_12 = lean_array_push(x_3, x_4);
x_13 = lean_array_push(x_12, x_5);
x_14 = l_Lean_Meta_mkLambda(x_13, x_11, x_6, x_10);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_8);
if (x_15 == 0)
{
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
return x_18;
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
lean_object* l_Lean_Meta_substCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
lean_dec(x_14);
lean_inc(x_15);
lean_inc(x_1);
x_18 = l_Lean_Meta_getLocalDecl(x_1, x_15, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_280 = l_Lean_LocalDecl_type(x_19);
lean_dec(x_19);
x_281 = lean_unsigned_to_nat(3u);
x_282 = l_Lean_Expr_isAppOfArity___main(x_280, x_13, x_281);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_280);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_283 = l_Lean_Meta_isClassQuick___main___closed__1;
x_284 = l_unreachable_x21___rarg(x_283);
x_285 = lean_apply_2(x_284, x_15, x_20);
return x_285;
}
else
{
if (x_10 == 0)
{
lean_object* x_286; 
x_286 = l_Lean_Expr_appArg_x21(x_280);
lean_dec(x_280);
x_21 = x_286;
goto block_279;
}
else
{
lean_object* x_287; lean_object* x_288; 
x_287 = l_Lean_Expr_appFn_x21(x_280);
lean_dec(x_280);
x_288 = l_Lean_Expr_appArg_x21(x_287);
lean_dec(x_287);
x_21 = x_288;
goto block_279;
}
}
block_279:
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_inc(x_17);
x_23 = l_Lean_MetavarContext_exprDependsOn(x_22, x_17, x_1);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_12);
x_25 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2);
x_26 = lean_array_push(x_25, x_2);
lean_inc(x_15);
lean_inc(x_17);
x_27 = l_Lean_Meta_mkLambda(x_26, x_17, x_15, x_20);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_replaceFVar(x_17, x_2, x_21);
lean_dec(x_17);
if (x_10 == 0)
{
lean_object* x_98; 
lean_inc(x_15);
x_98 = l_Lean_Meta_mkEqSymm(x_11, x_15, x_29);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_31 = x_99;
x_32 = x_100;
goto block_97;
}
else
{
uint8_t x_101; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_101 = !lean_is_exclusive(x_98);
if (x_101 == 0)
{
return x_98;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_98, 0);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_98);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
x_31 = x_11;
x_32 = x_29;
goto block_97;
}
block_97:
{
uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = 2;
lean_inc(x_15);
x_34 = l_Lean_Meta_mkFreshExprMVar(x_30, x_3, x_33, x_15, x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_15);
lean_inc(x_35);
x_37 = l_Lean_Meta_mkEqNDRec(x_28, x_35, x_31, x_15, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Expr_mvarId_x21(x_35);
lean_dec(x_35);
x_41 = l_Lean_Meta_assignExprMVar(x_4, x_38, x_15, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Meta_clear(x_40, x_1, x_15, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Meta_clear(x_44, x_5, x_15, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_array_get_size(x_6);
x_50 = lean_unsigned_to_nat(2u);
x_51 = lean_nat_sub(x_49, x_50);
lean_dec(x_49);
x_52 = 0;
x_53 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_52, x_47, x_51, x_7, x_15, x_48);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = !lean_is_exclusive(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_57 = lean_ctor_get(x_54, 0);
x_58 = lean_array_get_size(x_57);
lean_inc(x_58);
x_59 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1(x_6, x_57, x_58, x_58, x_8, x_15, x_55);
lean_dec(x_15);
lean_dec(x_58);
lean_dec(x_57);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = l_Lean_Meta_FVarSubst_insert(x_61, x_9, x_21);
lean_ctor_set(x_54, 0, x_62);
lean_ctor_set(x_59, 0, x_54);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
x_65 = l_Lean_Meta_FVarSubst_insert(x_63, x_9, x_21);
lean_ctor_set(x_54, 0, x_65);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_54, 0);
x_68 = lean_ctor_get(x_54, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_54);
x_69 = lean_array_get_size(x_67);
lean_inc(x_69);
x_70 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1(x_6, x_67, x_69, x_69, x_8, x_15, x_55);
lean_dec(x_15);
lean_dec(x_69);
lean_dec(x_67);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = l_Lean_Meta_FVarSubst_insert(x_71, x_9, x_21);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_68);
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_73;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
x_77 = !lean_is_exclusive(x_53);
if (x_77 == 0)
{
return x_53;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_53, 0);
x_79 = lean_ctor_get(x_53, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_53);
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
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_81 = !lean_is_exclusive(x_46);
if (x_81 == 0)
{
return x_46;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_46, 0);
x_83 = lean_ctor_get(x_46, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_46);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_85 = !lean_is_exclusive(x_43);
if (x_85 == 0)
{
return x_43;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_43, 0);
x_87 = lean_ctor_get(x_43, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_43);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
uint8_t x_89; 
lean_dec(x_40);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_89 = !lean_is_exclusive(x_41);
if (x_89 == 0)
{
return x_41;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_41, 0);
x_91 = lean_ctor_get(x_41, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_41);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_35);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_37);
if (x_93 == 0)
{
return x_37;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_37, 0);
x_95 = lean_ctor_get(x_37, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_37);
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
uint8_t x_105; 
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_27);
if (x_105 == 0)
{
return x_27;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_27, 0);
x_107 = lean_ctor_get(x_27, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_27);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; 
lean_inc(x_2);
x_109 = l_Lean_Expr_replaceFVar(x_17, x_2, x_21);
lean_inc(x_15);
lean_inc(x_21);
x_110 = l_Lean_Meta_mkEqRefl(x_21, x_15, x_20);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
lean_inc(x_11);
x_113 = l_Lean_Expr_replaceFVar(x_109, x_11, x_111);
lean_dec(x_111);
lean_dec(x_109);
if (x_10 == 0)
{
lean_object* x_114; 
lean_inc(x_15);
lean_inc(x_2);
lean_inc(x_21);
x_114 = l_Lean_Meta_mkEq(x_21, x_2, x_15, x_112);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
lean_inc(x_11);
x_117 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__1___boxed), 7, 4);
lean_closure_set(x_117, 0, x_17);
lean_closure_set(x_117, 1, x_11);
lean_closure_set(x_117, 2, x_12);
lean_closure_set(x_117, 3, x_2);
x_118 = l_Lean_Meta_substCore___lambda__2___closed__2;
x_119 = 0;
lean_inc(x_15);
x_120 = l_Lean_Meta_withLocalDecl___rarg(x_118, x_115, x_119, x_117, x_15, x_116);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
lean_inc(x_15);
x_123 = l_Lean_Meta_mkEqSymm(x_11, x_15, x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = 2;
lean_inc(x_15);
x_127 = l_Lean_Meta_mkFreshExprMVar(x_113, x_3, x_126, x_15, x_125);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
lean_inc(x_15);
lean_inc(x_128);
x_130 = l_Lean_Meta_mkEqRec(x_121, x_128, x_124, x_15, x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = l_Lean_Expr_mvarId_x21(x_128);
lean_dec(x_128);
x_134 = l_Lean_Meta_assignExprMVar(x_4, x_131, x_15, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_ctor_get(x_134, 1);
lean_inc(x_135);
lean_dec(x_134);
x_136 = l_Lean_Meta_clear(x_133, x_1, x_15, x_135);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_136, 1);
lean_inc(x_138);
lean_dec(x_136);
x_139 = l_Lean_Meta_clear(x_137, x_5, x_15, x_138);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = lean_array_get_size(x_6);
x_143 = lean_unsigned_to_nat(2u);
x_144 = lean_nat_sub(x_142, x_143);
lean_dec(x_142);
x_145 = 0;
x_146 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_145, x_140, x_144, x_7, x_15, x_141);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
lean_dec(x_146);
x_149 = !lean_is_exclusive(x_147);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_150 = lean_ctor_get(x_147, 0);
x_151 = lean_array_get_size(x_150);
lean_inc(x_151);
x_152 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__2(x_6, x_150, x_151, x_151, x_8, x_15, x_148);
lean_dec(x_15);
lean_dec(x_151);
lean_dec(x_150);
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_152, 0);
x_155 = l_Lean_Meta_FVarSubst_insert(x_154, x_9, x_21);
lean_ctor_set(x_147, 0, x_155);
lean_ctor_set(x_152, 0, x_147);
return x_152;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_152, 0);
x_157 = lean_ctor_get(x_152, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_152);
x_158 = l_Lean_Meta_FVarSubst_insert(x_156, x_9, x_21);
lean_ctor_set(x_147, 0, x_158);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_147);
lean_ctor_set(x_159, 1, x_157);
return x_159;
}
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_160 = lean_ctor_get(x_147, 0);
x_161 = lean_ctor_get(x_147, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_147);
x_162 = lean_array_get_size(x_160);
lean_inc(x_162);
x_163 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__2(x_6, x_160, x_162, x_162, x_8, x_15, x_148);
lean_dec(x_15);
lean_dec(x_162);
lean_dec(x_160);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_166 = x_163;
} else {
 lean_dec_ref(x_163);
 x_166 = lean_box(0);
}
x_167 = l_Lean_Meta_FVarSubst_insert(x_164, x_9, x_21);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_161);
if (lean_is_scalar(x_166)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_166;
}
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_165);
return x_169;
}
}
else
{
uint8_t x_170; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
x_170 = !lean_is_exclusive(x_146);
if (x_170 == 0)
{
return x_146;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_146, 0);
x_172 = lean_ctor_get(x_146, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_146);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_174 = !lean_is_exclusive(x_139);
if (x_174 == 0)
{
return x_139;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_139, 0);
x_176 = lean_ctor_get(x_139, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_139);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
uint8_t x_178; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_178 = !lean_is_exclusive(x_136);
if (x_178 == 0)
{
return x_136;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_136, 0);
x_180 = lean_ctor_get(x_136, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_136);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_133);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_134);
if (x_182 == 0)
{
return x_134;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_134, 0);
x_184 = lean_ctor_get(x_134, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_134);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_128);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_186 = !lean_is_exclusive(x_130);
if (x_186 == 0)
{
return x_130;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_130, 0);
x_188 = lean_ctor_get(x_130, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_130);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
else
{
uint8_t x_190; 
lean_dec(x_121);
lean_dec(x_113);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_190 = !lean_is_exclusive(x_123);
if (x_190 == 0)
{
return x_123;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_123, 0);
x_192 = lean_ctor_get(x_123, 1);
lean_inc(x_192);
lean_inc(x_191);
lean_dec(x_123);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_191);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
}
}
else
{
uint8_t x_194; 
lean_dec(x_113);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_194 = !lean_is_exclusive(x_120);
if (x_194 == 0)
{
return x_120;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_120, 0);
x_196 = lean_ctor_get(x_120, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_120);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_113);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_198 = !lean_is_exclusive(x_114);
if (x_198 == 0)
{
return x_114;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_114, 0);
x_200 = lean_ctor_get(x_114, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_114);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_array_push(x_12, x_2);
lean_inc(x_11);
x_203 = lean_array_push(x_202, x_11);
lean_inc(x_15);
x_204 = l_Lean_Meta_mkLambda(x_203, x_17, x_15, x_112);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = 2;
lean_inc(x_15);
x_208 = l_Lean_Meta_mkFreshExprMVar(x_113, x_3, x_207, x_15, x_206);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
lean_inc(x_15);
lean_inc(x_209);
x_211 = l_Lean_Meta_mkEqRec(x_205, x_209, x_11, x_15, x_210);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_214 = l_Lean_Expr_mvarId_x21(x_209);
lean_dec(x_209);
x_215 = l_Lean_Meta_assignExprMVar(x_4, x_212, x_15, x_213);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = l_Lean_Meta_clear(x_214, x_1, x_15, x_216);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = l_Lean_Meta_clear(x_218, x_5, x_15, x_219);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; uint8_t x_226; lean_object* x_227; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_array_get_size(x_6);
x_224 = lean_unsigned_to_nat(2u);
x_225 = lean_nat_sub(x_223, x_224);
lean_dec(x_223);
x_226 = 0;
x_227 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_226, x_221, x_225, x_7, x_15, x_222);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; uint8_t x_230; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = !lean_is_exclusive(x_228);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; 
x_231 = lean_ctor_get(x_228, 0);
x_232 = lean_array_get_size(x_231);
lean_inc(x_232);
x_233 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3(x_6, x_231, x_232, x_232, x_8, x_15, x_229);
lean_dec(x_15);
lean_dec(x_232);
lean_dec(x_231);
x_234 = !lean_is_exclusive(x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; 
x_235 = lean_ctor_get(x_233, 0);
x_236 = l_Lean_Meta_FVarSubst_insert(x_235, x_9, x_21);
lean_ctor_set(x_228, 0, x_236);
lean_ctor_set(x_233, 0, x_228);
return x_233;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_237 = lean_ctor_get(x_233, 0);
x_238 = lean_ctor_get(x_233, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_233);
x_239 = l_Lean_Meta_FVarSubst_insert(x_237, x_9, x_21);
lean_ctor_set(x_228, 0, x_239);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_228);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_241 = lean_ctor_get(x_228, 0);
x_242 = lean_ctor_get(x_228, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_228);
x_243 = lean_array_get_size(x_241);
lean_inc(x_243);
x_244 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3(x_6, x_241, x_243, x_243, x_8, x_15, x_229);
lean_dec(x_15);
lean_dec(x_243);
lean_dec(x_241);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_247 = x_244;
} else {
 lean_dec_ref(x_244);
 x_247 = lean_box(0);
}
x_248 = l_Lean_Meta_FVarSubst_insert(x_245, x_9, x_21);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_248);
lean_ctor_set(x_249, 1, x_242);
if (lean_is_scalar(x_247)) {
 x_250 = lean_alloc_ctor(0, 2, 0);
} else {
 x_250 = x_247;
}
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_246);
return x_250;
}
}
else
{
uint8_t x_251; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
x_251 = !lean_is_exclusive(x_227);
if (x_251 == 0)
{
return x_227;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_227, 0);
x_253 = lean_ctor_get(x_227, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_227);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
else
{
uint8_t x_255; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_255 = !lean_is_exclusive(x_220);
if (x_255 == 0)
{
return x_220;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_220, 0);
x_257 = lean_ctor_get(x_220, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_220);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
else
{
uint8_t x_259; 
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_259 = !lean_is_exclusive(x_217);
if (x_259 == 0)
{
return x_217;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_217, 0);
x_261 = lean_ctor_get(x_217, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_217);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
else
{
uint8_t x_263; 
lean_dec(x_214);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_263 = !lean_is_exclusive(x_215);
if (x_263 == 0)
{
return x_215;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_215, 0);
x_265 = lean_ctor_get(x_215, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_215);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
}
else
{
uint8_t x_267; 
lean_dec(x_209);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_267 = !lean_is_exclusive(x_211);
if (x_267 == 0)
{
return x_211;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_211, 0);
x_269 = lean_ctor_get(x_211, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_211);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
else
{
uint8_t x_271; 
lean_dec(x_113);
lean_dec(x_21);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_271 = !lean_is_exclusive(x_204);
if (x_271 == 0)
{
return x_204;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_204, 0);
x_273 = lean_ctor_get(x_204, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_204);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
}
else
{
uint8_t x_275; 
lean_dec(x_109);
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_275 = !lean_is_exclusive(x_110);
if (x_275 == 0)
{
return x_110;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_110, 0);
x_277 = lean_ctor_get(x_110, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_110);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
}
}
}
else
{
uint8_t x_289; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_289 = !lean_is_exclusive(x_18);
if (x_289 == 0)
{
return x_18;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_18, 0);
x_291 = lean_ctor_get(x_18, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_18);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
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
x_1 = lean_mk_string("(x = t)");
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
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__8;
x_2 = l_Lean_Meta_substCore___lambda__3___closed__11;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("(t = x)");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__13;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__14;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__8;
x_2 = l_Lean_Meta_substCore___lambda__3___closed__15;
x_3 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_substCore___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__18() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("reverted variables ");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__18;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__19;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__21() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("' occurs at");
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
x_1 = lean_mk_string("substituting ");
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
x_1 = lean_mk_string(" (id: ");
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
x_1 = lean_mk_string(") with ");
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
lean_object* l_Lean_Meta_substCore___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Meta_substCore___lambda__3___closed__2;
lean_inc(x_1);
x_9 = l_Lean_Meta_checkNotAssigned(x_1, x_8, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_2);
x_11 = l_Lean_Meta_getLocalDecl(x_2, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_LocalDecl_type(x_12);
lean_dec(x_12);
x_15 = l_Lean_Expr_eq_x3f___closed__2;
x_16 = lean_unsigned_to_nat(3u);
x_17 = l_Lean_Expr_isAppOfArity___main(x_14, x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_18 = l_Lean_Meta_substCore___lambda__3___closed__5;
x_19 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_1, x_18, x_6, x_13);
lean_dec(x_6);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = l_Lean_Expr_appFn_x21(x_14);
x_21 = l_Lean_Expr_appArg_x21(x_20);
lean_dec(x_20);
x_22 = l_Lean_Expr_appArg_x21(x_14);
if (x_4 == 0)
{
uint8_t x_172; 
x_172 = 0;
x_23 = x_172;
goto block_171;
}
else
{
uint8_t x_173; 
x_173 = 1;
x_23 = x_173;
goto block_171;
}
block_171:
{
lean_object* x_24; 
if (x_23 == 0)
{
lean_inc(x_21);
x_24 = x_21;
goto block_170;
}
else
{
lean_inc(x_22);
x_24 = x_22;
goto block_170;
}
block_170:
{
lean_object* x_25; 
if (x_23 == 0)
{
lean_dec(x_21);
x_25 = x_22;
goto block_169;
}
else
{
lean_dec(x_22);
x_25 = x_21;
goto block_169;
}
block_169:
{
lean_object* x_26; 
lean_inc(x_6);
x_26 = l_Lean_Meta_whnf(x_24, x_6, x_13);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 1)
{
lean_object* x_39; lean_object* x_40; lean_object* x_143; uint8_t x_144; 
lean_dec(x_14);
x_39 = lean_ctor_get(x_27, 0);
lean_inc(x_39);
x_143 = lean_ctor_get(x_28, 4);
lean_inc(x_143);
x_144 = lean_ctor_get_uint8(x_143, sizeof(void*)*1);
lean_dec(x_143);
if (x_144 == 0)
{
x_40 = x_28;
goto block_142;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_145 = l_Lean_Meta_substCore___lambda__3___closed__17;
x_146 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_145, x_6, x_28);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_unbox(x_147);
lean_dec(x_147);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_dec(x_146);
x_40 = x_149;
goto block_142;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_150 = lean_ctor_get(x_146, 1);
lean_inc(x_150);
lean_dec(x_146);
lean_inc(x_27);
x_151 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_151, 0, x_27);
x_152 = l_Lean_Meta_substCore___lambda__3___closed__26;
x_153 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
x_154 = l_Lean_Meta_substCore___lambda__3___closed__29;
x_155 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
lean_inc(x_39);
x_156 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_156, 0, x_39);
x_157 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
x_158 = l_Lean_Meta_substCore___lambda__3___closed__32;
x_159 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
lean_inc(x_25);
x_160 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_160, 0, x_25);
x_161 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_145, x_161, x_6, x_150);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
lean_dec(x_162);
x_40 = x_163;
goto block_142;
}
}
block_142:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_inc(x_25);
x_42 = l_Lean_MetavarContext_exprDependsOn(x_41, x_25, x_39);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_dec(x_27);
lean_dec(x_25);
x_44 = x_40;
goto block_128;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
lean_dec(x_39);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_129 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_129, 0, x_27);
x_130 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_131 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
x_132 = l_Lean_Meta_substCore___lambda__3___closed__23;
x_133 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_134, 0, x_25);
x_135 = l_Lean_indentExpr(x_134);
x_136 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_1, x_136, x_6, x_40);
lean_dec(x_6);
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
return x_137;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = lean_ctor_get(x_137, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_137);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
block_128:
{
lean_object* x_45; 
lean_inc(x_6);
lean_inc(x_39);
x_45 = l_Lean_Meta_getLocalDecl(x_39, x_6, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_mkAppStx___closed__9;
lean_inc(x_39);
x_48 = lean_array_push(x_47, x_39);
x_49 = lean_array_push(x_48, x_2);
x_50 = 1;
x_51 = l_Lean_Meta_revert(x_1, x_49, x_50, x_6, x_46);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_box(0);
x_57 = 0;
x_58 = lean_unsigned_to_nat(2u);
x_59 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_57, x_55, x_58, x_56, x_6, x_53);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_109; uint8_t x_110; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = l_Lean_Name_inhabited;
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_array_get(x_64, x_62, x_65);
lean_inc(x_66);
x_67 = l_Lean_mkFVar(x_66);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_array_get(x_64, x_62, x_68);
lean_dec(x_62);
lean_inc(x_69);
x_70 = l_Lean_mkFVar(x_69);
lean_inc(x_63);
x_71 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarDecl___boxed), 3, 1);
lean_closure_set(x_71, 0, x_63);
x_72 = lean_box(x_23);
lean_inc(x_54);
lean_inc(x_63);
x_73 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__2___boxed), 16, 13);
lean_closure_set(x_73, 0, x_69);
lean_closure_set(x_73, 1, x_67);
lean_closure_set(x_73, 2, x_5);
lean_closure_set(x_73, 3, x_63);
lean_closure_set(x_73, 4, x_66);
lean_closure_set(x_73, 5, x_54);
lean_closure_set(x_73, 6, x_56);
lean_closure_set(x_73, 7, x_3);
lean_closure_set(x_73, 8, x_39);
lean_closure_set(x_73, 9, x_72);
lean_closure_set(x_73, 10, x_70);
lean_closure_set(x_73, 11, x_47);
lean_closure_set(x_73, 12, x_15);
x_74 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_74, 0, x_71);
lean_closure_set(x_74, 1, x_73);
x_109 = lean_ctor_get(x_61, 4);
lean_inc(x_109);
x_110 = lean_ctor_get_uint8(x_109, sizeof(void*)*1);
lean_dec(x_109);
if (x_110 == 0)
{
x_75 = x_57;
x_76 = x_61;
goto block_108;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_111 = l_Lean_Meta_substCore___lambda__3___closed__17;
x_112 = l___private_Lean_Util_Trace_5__checkTraceOptionM___at_Lean_Meta_isLevelDefEqAux___main___spec__2(x_111, x_6, x_61);
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_unbox(x_113);
lean_dec(x_113);
x_75 = x_115;
x_76 = x_114;
goto block_108;
}
block_108:
{
if (x_75 == 0)
{
lean_object* x_77; 
lean_dec(x_54);
x_77 = l_Lean_Meta_getMVarDecl(x_63, x_6, x_76);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 4);
lean_inc(x_81);
lean_dec(x_78);
x_82 = l_Lean_Meta_withLocalContext___rarg(x_80, x_81, x_74, x_6, x_79);
lean_dec(x_6);
return x_82;
}
else
{
uint8_t x_83; 
lean_dec(x_74);
lean_dec(x_6);
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
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_87 = l_Array_toList___rarg(x_54);
lean_dec(x_54);
x_88 = l_List_toString___at_Lean_Meta_substCore___spec__4(x_87);
x_89 = l_Array_HasRepr___rarg___closed__1;
x_90 = lean_string_append(x_89, x_88);
lean_dec(x_88);
x_91 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = l_Lean_Meta_substCore___lambda__3___closed__20;
x_94 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = l_Lean_Meta_substCore___lambda__3___closed__17;
x_96 = l_Lean_MonadTracerAdapter_addTrace___at_Lean_Meta_isLevelDefEqAux___main___spec__1(x_95, x_94, x_6, x_76);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = l_Lean_Meta_getMVarDecl(x_63, x_6, x_97);
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
x_103 = l_Lean_Meta_withLocalContext___rarg(x_101, x_102, x_74, x_6, x_100);
lean_dec(x_6);
return x_103;
}
else
{
uint8_t x_104; 
lean_dec(x_74);
lean_dec(x_6);
x_104 = !lean_is_exclusive(x_98);
if (x_104 == 0)
{
return x_98;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_98, 0);
x_106 = lean_ctor_get(x_98, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_98);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
}
else
{
uint8_t x_116; 
lean_dec(x_54);
lean_dec(x_39);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_116 = !lean_is_exclusive(x_59);
if (x_116 == 0)
{
return x_59;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_59, 0);
x_118 = lean_ctor_get(x_59, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_59);
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
lean_dec(x_39);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_120 = !lean_is_exclusive(x_51);
if (x_120 == 0)
{
return x_51;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_51, 0);
x_122 = lean_ctor_get(x_51, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_51);
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
lean_dec(x_39);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_124 = !lean_is_exclusive(x_45);
if (x_124 == 0)
{
return x_45;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_45, 0);
x_126 = lean_ctor_get(x_45, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_45);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
}
else
{
lean_object* x_164; 
lean_dec(x_27);
lean_dec(x_25);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_164 = lean_box(0);
x_29 = x_164;
goto block_38;
}
block_38:
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_29);
x_30 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_30, 0, x_14);
x_31 = l_Lean_indentExpr(x_30);
if (x_23 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = l_Lean_Meta_substCore___lambda__3___closed__12;
x_33 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_1, x_33, x_6, x_28);
lean_dec(x_6);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = l_Lean_Meta_substCore___lambda__3___closed__16;
x_36 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
x_37 = l_Lean_Meta_throwTacticEx___rarg(x_8, x_1, x_36, x_6, x_28);
lean_dec(x_6);
return x_37;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_25);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_165 = !lean_is_exclusive(x_26);
if (x_165 == 0)
{
return x_26;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_26, 0);
x_167 = lean_ctor_get(x_26, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_26);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
}
}
}
else
{
uint8_t x_174; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_174 = !lean_is_exclusive(x_11);
if (x_174 == 0)
{
return x_11;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_11, 0);
x_176 = lean_ctor_get(x_11, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_11);
x_177 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_177, 0, x_175);
lean_ctor_set(x_177, 1, x_176);
return x_177;
}
}
}
else
{
uint8_t x_178; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_178 = !lean_is_exclusive(x_9);
if (x_178 == 0)
{
return x_9;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_9, 0);
x_180 = lean_ctor_get(x_9, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_9);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
}
lean_object* l_Lean_Meta_substCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarTag___boxed), 3, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_box(x_3);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__3___boxed), 7, 4);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_4);
lean_closure_set(x_9, 3, x_8);
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_Meta_getMVarDecl(x_1, x_5, x_6);
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
x_16 = l_Lean_Meta_withLocalContext___rarg(x_14, x_15, x_10, x_5, x_13);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_10);
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
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Nat_foldMAux___main___at_Lean_Meta_substCore___spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_List_toStringAux___main___at_Lean_Meta_substCore___spec__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_List_toStringAux___main___at_Lean_Meta_substCore___spec__5(x_3, x_2);
return x_4;
}
}
lean_object* l_Lean_Meta_substCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_substCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_substCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_10);
lean_dec(x_10);
x_18 = l_Lean_Meta_substCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_13);
lean_dec(x_6);
return x_18;
}
}
lean_object* l_Lean_Meta_substCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Meta_substCore___lambda__3(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
return x_9;
}
}
lean_object* l_Lean_Meta_substCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Meta_substCore(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
return x_8;
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_fget(x_4, x_5);
lean_inc(x_3);
x_13 = l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(x_1, x_2, x_3, x_12, x_6, x_7);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_5, x_16);
lean_dec(x_5);
x_5 = x_17;
x_7 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_3);
x_19 = !lean_is_exclusive(x_13);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_13, 0);
lean_dec(x_20);
return x_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 1);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_array_fget(x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
x_18 = l_Lean_LocalDecl_type(x_16);
x_19 = lean_unsigned_to_nat(3u);
x_20 = l_Lean_Expr_isAppOfArity___main(x_18, x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_5, x_21);
lean_dec(x_5);
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_49; 
x_24 = l_Lean_Expr_appFn_x21(x_18);
x_25 = l_Lean_Expr_appArg_x21(x_24);
lean_dec(x_24);
x_26 = l_Lean_Expr_appArg_x21(x_18);
lean_dec(x_18);
x_49 = l_Lean_Expr_isFVar(x_26);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_box(0);
x_27 = x_50;
goto block_48;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = l_Lean_Expr_fvarId_x21(x_26);
x_52 = lean_name_eq(x_51, x_1);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_box(0);
x_27 = x_53;
goto block_48;
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_inc(x_25);
lean_inc(x_3);
x_54 = l_Lean_MetavarContext_exprDependsOn(x_3, x_25, x_1);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_3);
x_56 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_57 = 1;
x_58 = lean_box(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_7);
return x_61;
}
else
{
lean_object* x_62; 
x_62 = lean_box(0);
x_27 = x_62;
goto block_48;
}
}
}
block_48:
{
uint8_t x_28; 
lean_dec(x_27);
x_28 = l_Lean_Expr_isFVar(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_16);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_5, x_29);
lean_dec(x_5);
x_5 = x_30;
goto _start;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Expr_fvarId_x21(x_25);
lean_dec(x_25);
x_33 = lean_name_eq(x_32, x_1);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_16);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_5, x_34);
lean_dec(x_5);
x_5 = x_35;
goto _start;
}
else
{
lean_object* x_37; uint8_t x_38; 
lean_inc(x_3);
x_37 = l_Lean_MetavarContext_exprDependsOn(x_3, x_26, x_1);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_5);
lean_dec(x_3);
x_39 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_40 = 0;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
if (lean_is_scalar(x_17)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_17;
}
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_7);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_17);
lean_dec(x_16);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_5, x_45);
lean_dec(x_5);
x_5 = x_46;
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
lean_object* l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4(x_1, x_2, x_3, x_7, x_8, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5(x_1, x_2, x_3, x_10, x_11, x_5, x_6);
return x_12;
}
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_get_size(x_4);
x_9 = lean_nat_dec_lt(x_5, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
lean_dec(x_3);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_array_fget(x_4, x_5);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_5 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_12, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 x_17 = x_12;
} else {
 lean_dec_ref(x_12);
 x_17 = lean_box(0);
}
x_18 = l_Lean_LocalDecl_type(x_16);
x_19 = lean_unsigned_to_nat(3u);
x_20 = l_Lean_Expr_isAppOfArity___main(x_18, x_2, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_5, x_21);
lean_dec(x_5);
x_5 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_49; 
x_24 = l_Lean_Expr_appFn_x21(x_18);
x_25 = l_Lean_Expr_appArg_x21(x_24);
lean_dec(x_24);
x_26 = l_Lean_Expr_appArg_x21(x_18);
lean_dec(x_18);
x_49 = l_Lean_Expr_isFVar(x_26);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_box(0);
x_27 = x_50;
goto block_48;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = l_Lean_Expr_fvarId_x21(x_26);
x_52 = lean_name_eq(x_51, x_1);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = lean_box(0);
x_27 = x_53;
goto block_48;
}
else
{
lean_object* x_54; uint8_t x_55; 
lean_inc(x_25);
lean_inc(x_3);
x_54 = l_Lean_MetavarContext_exprDependsOn(x_3, x_25, x_1);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_3);
x_56 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_57 = 1;
x_58 = lean_box(x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_56);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_7);
return x_61;
}
else
{
lean_object* x_62; 
x_62 = lean_box(0);
x_27 = x_62;
goto block_48;
}
}
}
block_48:
{
uint8_t x_28; 
lean_dec(x_27);
x_28 = l_Lean_Expr_isFVar(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_17);
lean_dec(x_16);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_5, x_29);
lean_dec(x_5);
x_5 = x_30;
goto _start;
}
else
{
lean_object* x_32; uint8_t x_33; 
x_32 = l_Lean_Expr_fvarId_x21(x_25);
lean_dec(x_25);
x_33 = lean_name_eq(x_32, x_1);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_26);
lean_dec(x_17);
lean_dec(x_16);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_5, x_34);
lean_dec(x_5);
x_5 = x_35;
goto _start;
}
else
{
lean_object* x_37; uint8_t x_38; 
lean_inc(x_3);
x_37 = l_Lean_MetavarContext_exprDependsOn(x_3, x_26, x_1);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_5);
lean_dec(x_3);
x_39 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_40 = 0;
x_41 = lean_box(x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
if (lean_is_scalar(x_17)) {
 x_43 = lean_alloc_ctor(1, 1, 0);
} else {
 x_43 = x_17;
}
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_7);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_17);
lean_dec(x_16);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_add(x_5, x_45);
lean_dec(x_5);
x_5 = x_46;
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
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_3);
x_8 = l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(x_1, x_2, x_3, x_7, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_4, 1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6(x_1, x_2, x_3, x_11, x_12, x_5, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_8, 0);
lean_dec(x_15);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 1);
x_8 = l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
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
lean_object* l_Lean_Meta_subst___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_LocalDecl_type(x_3);
x_7 = l_Lean_Expr_eq_x3f___closed__2;
x_8 = lean_unsigned_to_nat(3u);
x_9 = l_Lean_Expr_isAppOfArity___main(x_6, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_4, 1);
x_12 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(x_1, x_7, x_10, x_11, x_4, x_5);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_mkFVar(x_1);
x_16 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Meta_subst___lambda__1___closed__3;
x_18 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_20 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Meta_substCore___lambda__3___closed__2;
x_22 = l_Lean_Meta_throwTacticEx___rarg(x_21, x_2, x_20, x_4, x_14);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_box(0);
x_28 = lean_unbox(x_26);
lean_dec(x_26);
x_29 = l_Lean_Meta_substCore(x_2, x_25, x_28, x_27, x_4, x_24);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_29);
if (x_37 == 0)
{
return x_29;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 0);
x_39 = lean_ctor_get(x_29, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_29);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = l_Lean_Expr_appFn_x21(x_6);
x_42 = l_Lean_Expr_appArg_x21(x_41);
lean_dec(x_41);
x_43 = l_Lean_Expr_appArg_x21(x_6);
x_44 = l_Lean_Expr_isFVar(x_43);
lean_dec(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = l_Lean_Expr_isFVar(x_42);
lean_dec(x_42);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_6);
x_47 = l_Lean_indentExpr(x_46);
x_48 = l_Lean_Meta_subst___lambda__1___closed__6;
x_49 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = l_Lean_Meta_substCore___lambda__3___closed__2;
x_51 = l_Lean_Meta_throwTacticEx___rarg(x_50, x_2, x_49, x_4, x_5);
return x_51;
}
else
{
lean_object* x_52; uint8_t x_53; lean_object* x_54; 
lean_dec(x_6);
x_52 = lean_box(0);
x_53 = 0;
x_54 = l_Lean_Meta_substCore(x_2, x_1, x_53, x_52, x_4, x_5);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_56, 1);
lean_inc(x_57);
lean_dec(x_56);
lean_ctor_set(x_54, 0, x_57);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_54, 0);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_54);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_54);
if (x_62 == 0)
{
return x_54;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_54, 0);
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_54);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
else
{
lean_object* x_66; uint8_t x_67; lean_object* x_68; 
lean_dec(x_42);
lean_dec(x_6);
x_66 = lean_box(0);
x_67 = 1;
x_68 = l_Lean_Meta_substCore(x_2, x_1, x_67, x_66, x_4, x_5);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
lean_ctor_set(x_68, 0, x_71);
return x_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_ctor_get(x_68, 0);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_68);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_68);
if (x_76 == 0)
{
return x_68;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_68, 0);
x_78 = lean_ctor_get(x_68, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_68);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
}
}
lean_object* l_Lean_Meta_subst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_getLocalDecl), 3, 1);
lean_closure_set(x_5, 0, x_2);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_subst___lambda__1___boxed), 5, 2);
lean_closure_set(x_6, 0, x_2);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
x_8 = l_Lean_Meta_getMVarDecl(x_1, x_3, x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 4);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Meta_withLocalContext___rarg(x_11, x_12, x_7, x_3, x_10);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_8);
if (x_14 == 0)
{
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get(x_8, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_8);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* l_Lean_Meta_subst___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_subst___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
lean_object* l_Lean_Meta_subst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_subst(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
lean_object* l___private_Lean_Meta_Tactic_Subst_1__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_substCore___lambda__3___closed__17;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(lean_object*);
lean_object* initialize_Lean_Meta_Message(lean_object*);
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
res = initialize_Lean_Meta_Message(lean_io_mk_world());
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
