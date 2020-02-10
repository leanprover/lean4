// Lean compiler output
// Module: Init.Lean.Meta.Tactic.Subst
// Imports: Init.Lean.Meta.AppBuilder Init.Lean.Meta.Message Init.Lean.Meta.Tactic.Util Init.Lean.Meta.Tactic.Revert Init.Lean.Meta.Tactic.Intro Init.Lean.Meta.Tactic.Clear Init.Lean.Meta.Tactic.FVarSubst
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
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__2;
lean_object* l_Lean_Meta_substCore___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_eq_x3f___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_unreachable_x21___rarg(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__17;
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__4;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__4;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__1;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__8;
lean_object* l_Lean_Meta_subst___lambda__1___closed__2;
lean_object* l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__6;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__13;
extern lean_object* l_Lean_Name_inhabited;
lean_object* l_Lean_Meta_substCore___lambda__2___closed__1;
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_findDeclM_x3f___at_Lean_Meta_subst___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__11;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__12;
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2___closed__2;
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Meta_clear(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__9;
lean_object* l_Lean_Meta_subst___lambda__1___closed__6;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__19;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__10;
lean_object* l_Lean_Meta_subst___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity___main(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__7;
lean_object* l_Lean_Meta_getMVarDecl___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__16;
lean_object* l___private_Init_Lean_Meta_Tactic_Subst_1__regTraceClasses___closed__1;
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_MetavarContext_exprDependsOn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_assignExprMVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDecl___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__3;
lean_object* l_Lean_Meta_substCore___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21___main(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVar(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withMVarContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__5;
lean_object* l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
extern lean_object* l_Lean_mkAppStx___closed__9;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__5;
lean_object* l_Lean_Meta_mkLambda(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__14;
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Array_findSomeMAux___main___at_Lean_Meta_subst___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
extern lean_object* l_Lean_mkOptionalNode___closed__2;
extern lean_object* l_Lean_Meta_isClassQuick___main___closed__1;
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_subst___lambda__1___closed__1;
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_getMVarTag___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__3___closed__3;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__18;
lean_object* l_Lean_Meta_substCore___lambda__3___closed__15;
lean_object* l___private_Init_Lean_Meta_Tactic_Subst_1__regTraceClasses(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
x_8 = l_Lean_Meta_mkEqSymm(x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_expr_abstract(x_1, x_2);
x_12 = lean_expr_instantiate1(x_11, x_9);
lean_dec(x_9);
lean_dec(x_11);
x_13 = lean_array_push(x_3, x_4);
x_14 = lean_array_push(x_13, x_5);
x_15 = l_Lean_Meta_mkLambda(x_14, x_12, x_6, x_10);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
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
lean_object* l_Lean_Meta_substCore___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
lean_dec(x_12);
lean_inc(x_13);
lean_inc(x_1);
x_16 = l_Lean_Meta_getLocalDecl(x_1, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_260 = l_Lean_LocalDecl_type(x_17);
lean_dec(x_17);
x_261 = lean_unsigned_to_nat(3u);
x_262 = l_Lean_Expr_isAppOfArity___main(x_260, x_11, x_261);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_dec(x_260);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_263 = l_Lean_Meta_isClassQuick___main___closed__1;
x_264 = l_unreachable_x21___rarg(x_263);
x_265 = lean_apply_2(x_264, x_13, x_18);
return x_265;
}
else
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_unsigned_to_nat(0u);
x_267 = l_Lean_Expr_getAppNumArgsAux___main(x_260, x_266);
if (x_8 == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_268 = lean_unsigned_to_nat(2u);
x_269 = lean_nat_sub(x_267, x_268);
lean_dec(x_267);
x_270 = lean_unsigned_to_nat(1u);
x_271 = lean_nat_sub(x_269, x_270);
lean_dec(x_269);
x_272 = l_Lean_Expr_getRevArg_x21___main(x_260, x_271);
lean_dec(x_260);
x_19 = x_272;
goto block_259;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_273 = lean_unsigned_to_nat(1u);
x_274 = lean_nat_sub(x_267, x_273);
lean_dec(x_267);
x_275 = lean_nat_sub(x_274, x_273);
lean_dec(x_274);
x_276 = l_Lean_Expr_getRevArg_x21___main(x_260, x_275);
lean_dec(x_260);
x_19 = x_276;
goto block_259;
}
}
block_259:
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_inc(x_15);
x_21 = l_Lean_MetavarContext_exprDependsOn(x_20, x_15, x_1);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
x_23 = l_Lean_mkOptionalNode___closed__2;
x_24 = lean_array_push(x_23, x_2);
lean_inc(x_13);
lean_inc(x_15);
lean_inc(x_24);
x_25 = l_Lean_Meta_mkLambda(x_24, x_15, x_13, x_18);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_expr_abstract(x_15, x_24);
lean_dec(x_24);
lean_dec(x_15);
x_29 = lean_expr_instantiate1(x_28, x_19);
lean_dec(x_19);
lean_dec(x_28);
if (x_8 == 0)
{
lean_object* x_89; 
lean_inc(x_13);
x_89 = l_Lean_Meta_mkEqSymm(x_9, x_13, x_27);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_30 = x_90;
x_31 = x_91;
goto block_88;
}
else
{
uint8_t x_92; 
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_89);
if (x_92 == 0)
{
return x_89;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_89, 0);
x_94 = lean_ctor_get(x_89, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_89);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
x_30 = x_9;
x_31 = x_27;
goto block_88;
}
block_88:
{
uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = 2;
lean_inc(x_13);
x_33 = l_Lean_Meta_mkFreshExprMVar(x_29, x_3, x_32, x_13, x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_13);
lean_inc(x_34);
x_36 = l_Lean_Meta_mkEqNDRec(x_26, x_34, x_30, x_13, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Meta_assignExprMVar(x_4, x_37, x_13, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = l_Lean_Expr_mvarId_x21(x_34);
lean_dec(x_34);
x_42 = l_Lean_Meta_clear(x_41, x_1, x_13, x_40);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = l_Lean_Meta_clear(x_43, x_5, x_13, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_array_get_size(x_6);
x_49 = lean_unsigned_to_nat(2u);
x_50 = lean_nat_sub(x_48, x_49);
lean_dec(x_48);
x_51 = 0;
x_52 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_51, x_46, x_50, x_7, x_13, x_47);
lean_dec(x_13);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
x_57 = lean_box(0);
lean_ctor_set(x_54, 0, x_57);
return x_52;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
lean_ctor_set(x_52, 0, x_60);
return x_52;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_52, 0);
x_62 = lean_ctor_get(x_52, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_52);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_62);
return x_67;
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_52);
if (x_68 == 0)
{
return x_52;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_52, 0);
x_70 = lean_ctor_get(x_52, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_52);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
uint8_t x_72; 
lean_dec(x_13);
lean_dec(x_7);
x_72 = !lean_is_exclusive(x_45);
if (x_72 == 0)
{
return x_45;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_45, 0);
x_74 = lean_ctor_get(x_45, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_45);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
x_76 = !lean_is_exclusive(x_42);
if (x_76 == 0)
{
return x_42;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_42, 0);
x_78 = lean_ctor_get(x_42, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_42);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_34);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_39);
if (x_80 == 0)
{
return x_39;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_39, 0);
x_82 = lean_ctor_get(x_39, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_39);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_34);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_36);
if (x_84 == 0)
{
return x_36;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_36, 0);
x_86 = lean_ctor_get(x_36, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_36);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
}
else
{
uint8_t x_96; 
lean_dec(x_24);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_25);
if (x_96 == 0)
{
return x_25;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_25, 0);
x_98 = lean_ctor_get(x_25, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_25);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = l_Lean_mkOptionalNode___closed__2;
lean_inc(x_2);
x_101 = lean_array_push(x_100, x_2);
x_102 = lean_expr_abstract(x_15, x_101);
lean_dec(x_101);
x_103 = lean_expr_instantiate1(x_102, x_19);
lean_dec(x_102);
lean_inc(x_13);
lean_inc(x_19);
x_104 = l_Lean_Meta_mkEqRefl(x_19, x_13, x_18);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_9);
x_107 = lean_array_push(x_100, x_9);
x_108 = lean_expr_abstract(x_103, x_107);
lean_dec(x_103);
x_109 = lean_expr_instantiate1(x_108, x_105);
lean_dec(x_105);
lean_dec(x_108);
if (x_8 == 0)
{
lean_object* x_110; 
lean_inc(x_13);
lean_inc(x_2);
x_110 = l_Lean_Meta_mkEq(x_19, x_2, x_13, x_106);
if (lean_obj_tag(x_110) == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__1___boxed), 7, 4);
lean_closure_set(x_113, 0, x_15);
lean_closure_set(x_113, 1, x_107);
lean_closure_set(x_113, 2, x_10);
lean_closure_set(x_113, 3, x_2);
x_114 = l_Lean_Meta_substCore___lambda__2___closed__2;
x_115 = 0;
lean_inc(x_13);
x_116 = l_Lean_Meta_withLocalDecl___rarg(x_114, x_111, x_115, x_113, x_13, x_112);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_13);
x_119 = l_Lean_Meta_mkEqSymm(x_9, x_13, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = 2;
lean_inc(x_13);
x_123 = l_Lean_Meta_mkFreshExprMVar(x_109, x_3, x_122, x_13, x_121);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
lean_inc(x_13);
lean_inc(x_124);
x_126 = l_Lean_Meta_mkEqRec(x_117, x_124, x_120, x_13, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = l_Lean_Meta_assignExprMVar(x_4, x_127, x_13, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
lean_dec(x_129);
x_131 = l_Lean_Expr_mvarId_x21(x_124);
lean_dec(x_124);
x_132 = l_Lean_Meta_clear(x_131, x_1, x_13, x_130);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = l_Lean_Meta_clear(x_133, x_5, x_13, x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_array_get_size(x_6);
x_139 = lean_unsigned_to_nat(2u);
x_140 = lean_nat_sub(x_138, x_139);
lean_dec(x_138);
x_141 = 0;
x_142 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_141, x_136, x_140, x_7, x_13, x_137);
lean_dec(x_13);
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_144, 0);
lean_dec(x_146);
x_147 = lean_box(0);
lean_ctor_set(x_144, 0, x_147);
return x_142;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_144, 1);
lean_inc(x_148);
lean_dec(x_144);
x_149 = lean_box(0);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_148);
lean_ctor_set(x_142, 0, x_150);
return x_142;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_151 = lean_ctor_get(x_142, 0);
x_152 = lean_ctor_get(x_142, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_142);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_154 = x_151;
} else {
 lean_dec_ref(x_151);
 x_154 = lean_box(0);
}
x_155 = lean_box(0);
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_154;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_152);
return x_157;
}
}
else
{
uint8_t x_158; 
x_158 = !lean_is_exclusive(x_142);
if (x_158 == 0)
{
return x_142;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_142, 0);
x_160 = lean_ctor_get(x_142, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_142);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_13);
lean_dec(x_7);
x_162 = !lean_is_exclusive(x_135);
if (x_162 == 0)
{
return x_135;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_135, 0);
x_164 = lean_ctor_get(x_135, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_135);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
x_166 = !lean_is_exclusive(x_132);
if (x_166 == 0)
{
return x_132;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_132, 0);
x_168 = lean_ctor_get(x_132, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_132);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_124);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_170 = !lean_is_exclusive(x_129);
if (x_170 == 0)
{
return x_129;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_129, 0);
x_172 = lean_ctor_get(x_129, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_129);
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
lean_dec(x_124);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_174 = !lean_is_exclusive(x_126);
if (x_174 == 0)
{
return x_126;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_126, 0);
x_176 = lean_ctor_get(x_126, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_126);
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
lean_dec(x_117);
lean_dec(x_109);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_178 = !lean_is_exclusive(x_119);
if (x_178 == 0)
{
return x_119;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_119, 0);
x_180 = lean_ctor_get(x_119, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_119);
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
lean_dec(x_109);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_116);
if (x_182 == 0)
{
return x_116;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_116, 0);
x_184 = lean_ctor_get(x_116, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_116);
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
lean_dec(x_109);
lean_dec(x_107);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_186 = !lean_is_exclusive(x_110);
if (x_186 == 0)
{
return x_110;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_110, 0);
x_188 = lean_ctor_get(x_110, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_110);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_107);
lean_dec(x_19);
x_190 = lean_array_push(x_10, x_2);
lean_inc(x_9);
x_191 = lean_array_push(x_190, x_9);
lean_inc(x_13);
x_192 = l_Lean_Meta_mkLambda(x_191, x_15, x_13, x_106);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = 2;
lean_inc(x_13);
x_196 = l_Lean_Meta_mkFreshExprMVar(x_109, x_3, x_195, x_13, x_194);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
lean_inc(x_13);
lean_inc(x_197);
x_199 = l_Lean_Meta_mkEqRec(x_193, x_197, x_9, x_13, x_198);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = l_Lean_Meta_assignExprMVar(x_4, x_200, x_13, x_201);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
lean_dec(x_202);
x_204 = l_Lean_Expr_mvarId_x21(x_197);
lean_dec(x_197);
x_205 = l_Lean_Meta_clear(x_204, x_1, x_13, x_203);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_205, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = l_Lean_Meta_clear(x_206, x_5, x_13, x_207);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
x_211 = lean_array_get_size(x_6);
x_212 = lean_unsigned_to_nat(2u);
x_213 = lean_nat_sub(x_211, x_212);
lean_dec(x_211);
x_214 = 0;
x_215 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_214, x_209, x_213, x_7, x_13, x_210);
lean_dec(x_13);
if (lean_obj_tag(x_215) == 0)
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_215);
if (x_216 == 0)
{
lean_object* x_217; uint8_t x_218; 
x_217 = lean_ctor_get(x_215, 0);
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; 
x_219 = lean_ctor_get(x_217, 0);
lean_dec(x_219);
x_220 = lean_box(0);
lean_ctor_set(x_217, 0, x_220);
return x_215;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_217, 1);
lean_inc(x_221);
lean_dec(x_217);
x_222 = lean_box(0);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_222);
lean_ctor_set(x_223, 1, x_221);
lean_ctor_set(x_215, 0, x_223);
return x_215;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_224 = lean_ctor_get(x_215, 0);
x_225 = lean_ctor_get(x_215, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_215);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_227 = x_224;
} else {
 lean_dec_ref(x_224);
 x_227 = lean_box(0);
}
x_228 = lean_box(0);
if (lean_is_scalar(x_227)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_227;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_226);
x_230 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_225);
return x_230;
}
}
else
{
uint8_t x_231; 
x_231 = !lean_is_exclusive(x_215);
if (x_231 == 0)
{
return x_215;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_215, 0);
x_233 = lean_ctor_get(x_215, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_215);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
else
{
uint8_t x_235; 
lean_dec(x_13);
lean_dec(x_7);
x_235 = !lean_is_exclusive(x_208);
if (x_235 == 0)
{
return x_208;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_208, 0);
x_237 = lean_ctor_get(x_208, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_208);
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
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
x_239 = !lean_is_exclusive(x_205);
if (x_239 == 0)
{
return x_205;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_205, 0);
x_241 = lean_ctor_get(x_205, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_205);
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
lean_dec(x_197);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_243 = !lean_is_exclusive(x_202);
if (x_243 == 0)
{
return x_202;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_202, 0);
x_245 = lean_ctor_get(x_202, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_202);
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
lean_dec(x_197);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_247 = !lean_is_exclusive(x_199);
if (x_247 == 0)
{
return x_199;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_199, 0);
x_249 = lean_ctor_get(x_199, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_199);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
else
{
uint8_t x_251; 
lean_dec(x_109);
lean_dec(x_13);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_251 = !lean_is_exclusive(x_192);
if (x_251 == 0)
{
return x_192;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_192, 0);
x_253 = lean_ctor_get(x_192, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_192);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
}
else
{
uint8_t x_255; 
lean_dec(x_103);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_255 = !lean_is_exclusive(x_104);
if (x_255 == 0)
{
return x_104;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_104, 0);
x_257 = lean_ctor_get(x_104, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_104);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
}
}
else
{
uint8_t x_277; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_277 = !lean_is_exclusive(x_16);
if (x_277 == 0)
{
return x_16;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_16, 0);
x_279 = lean_ctor_get(x_16, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_16);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
return x_280;
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
lean_object* x_1; 
x_1 = lean_mk_string("' occurs at");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__17;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Meta_substCore___lambda__3___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_substCore___lambda__3___closed__18;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Meta_substCore___lambda__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_Meta_substCore___lambda__3___closed__2;
lean_inc(x_1);
x_8 = l_Lean_Meta_checkNotAssigned(x_1, x_7, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_2);
x_10 = l_Lean_Meta_getLocalDecl(x_2, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_LocalDecl_type(x_11);
lean_dec(x_11);
x_14 = l_Lean_Expr_eq_x3f___closed__2;
x_15 = lean_unsigned_to_nat(3u);
x_16 = l_Lean_Expr_isAppOfArity___main(x_13, x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_2);
x_17 = l_Lean_Meta_substCore___lambda__3___closed__5;
x_18 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_17, x_5, x_12);
lean_dec(x_5);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_Expr_getAppNumArgsAux___main(x_13, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_20, x_21);
x_23 = lean_nat_sub(x_22, x_21);
lean_dec(x_22);
x_24 = l_Lean_Expr_getRevArg_x21___main(x_13, x_23);
x_25 = lean_unsigned_to_nat(2u);
x_26 = lean_nat_sub(x_20, x_25);
lean_dec(x_20);
x_27 = lean_nat_sub(x_26, x_21);
lean_dec(x_26);
x_28 = l_Lean_Expr_getRevArg_x21___main(x_13, x_27);
if (x_3 == 0)
{
uint8_t x_105; 
x_105 = 0;
x_29 = x_105;
goto block_104;
}
else
{
uint8_t x_106; 
x_106 = 1;
x_29 = x_106;
goto block_104;
}
block_104:
{
lean_object* x_30; lean_object* x_40; 
if (x_29 == 0)
{
lean_inc(x_24);
x_40 = x_24;
goto block_103;
}
else
{
lean_inc(x_28);
x_40 = x_28;
goto block_103;
}
block_39:
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_30);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_13);
x_32 = l_Lean_indentExpr(x_31);
if (x_29 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Lean_Meta_substCore___lambda__3___closed__12;
x_34 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
x_35 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_34, x_5, x_12);
lean_dec(x_5);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = l_Lean_Meta_substCore___lambda__3___closed__16;
x_37 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
x_38 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_37, x_5, x_12);
lean_dec(x_5);
return x_38;
}
}
block_103:
{
lean_object* x_41; 
if (x_29 == 0)
{
lean_dec(x_24);
x_41 = x_28;
goto block_102;
}
else
{
lean_dec(x_28);
x_41 = x_24;
goto block_102;
}
block_102:
{
if (lean_obj_tag(x_40) == 1)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_86; uint8_t x_87; 
lean_dec(x_13);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_12, 1);
lean_inc(x_43);
lean_inc(x_41);
x_86 = l_Lean_MetavarContext_exprDependsOn(x_43, x_41, x_42);
x_87 = lean_unbox(x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_dec(x_41);
lean_dec(x_40);
x_44 = x_12;
goto block_85;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_42);
lean_dec(x_4);
lean_dec(x_2);
x_88 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_88, 0, x_40);
x_89 = l_Array_forMAux___main___at_Lean_Meta_clear___spec__5___closed__8;
x_90 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
x_91 = l_Lean_Meta_substCore___lambda__3___closed__19;
x_92 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_93, 0, x_41);
x_94 = l_Lean_indentExpr(x_93);
x_95 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
x_96 = l_Lean_Meta_throwTacticEx___rarg(x_7, x_1, x_95, x_5, x_12);
lean_dec(x_5);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
return x_96;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_96);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
block_85:
{
lean_object* x_45; 
lean_inc(x_5);
lean_inc(x_42);
x_45 = l_Lean_Meta_getLocalDecl(x_42, x_5, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_mkAppStx___closed__9;
x_48 = lean_array_push(x_47, x_42);
x_49 = lean_array_push(x_48, x_2);
x_50 = 1;
x_51 = l_Lean_Meta_revert(x_1, x_49, x_50, x_5, x_46);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
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
x_58 = l_Lean_Meta_introNCore___at_Lean_Meta_introN___spec__1(x_57, x_55, x_25, x_56, x_5, x_53);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_63 = l_Lean_Name_inhabited;
x_64 = lean_array_get(x_63, x_61, x_19);
lean_inc(x_64);
x_65 = l_Lean_mkFVar(x_64);
x_66 = lean_array_get(x_63, x_61, x_21);
lean_dec(x_61);
lean_inc(x_66);
x_67 = l_Lean_mkFVar(x_66);
lean_inc(x_62);
x_68 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarDecl___boxed), 3, 1);
lean_closure_set(x_68, 0, x_62);
x_69 = lean_box(x_29);
lean_inc(x_62);
x_70 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__2___boxed), 14, 11);
lean_closure_set(x_70, 0, x_66);
lean_closure_set(x_70, 1, x_65);
lean_closure_set(x_70, 2, x_4);
lean_closure_set(x_70, 3, x_62);
lean_closure_set(x_70, 4, x_64);
lean_closure_set(x_70, 5, x_54);
lean_closure_set(x_70, 6, x_56);
lean_closure_set(x_70, 7, x_69);
lean_closure_set(x_70, 8, x_67);
lean_closure_set(x_70, 9, x_47);
lean_closure_set(x_70, 10, x_14);
x_71 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_71, 0, x_68);
lean_closure_set(x_71, 1, x_70);
x_72 = l_Lean_Meta_withMVarContext___rarg(x_62, x_71, x_5, x_60);
lean_dec(x_5);
return x_72;
}
else
{
uint8_t x_73; 
lean_dec(x_54);
lean_dec(x_5);
lean_dec(x_4);
x_73 = !lean_is_exclusive(x_58);
if (x_73 == 0)
{
return x_58;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_58, 0);
x_75 = lean_ctor_get(x_58, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_58);
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
lean_dec(x_5);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_51);
if (x_77 == 0)
{
return x_51;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_51, 0);
x_79 = lean_ctor_get(x_51, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_51);
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
lean_dec(x_42);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_45);
if (x_81 == 0)
{
return x_45;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_45, 0);
x_83 = lean_ctor_get(x_45, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_45);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
}
else
{
lean_object* x_101; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_4);
lean_dec(x_2);
x_101 = lean_box(0);
x_30 = x_101;
goto block_39;
}
}
}
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_10);
if (x_107 == 0)
{
return x_10;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_10, 0);
x_109 = lean_ctor_get(x_10, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_10);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_8);
if (x_111 == 0)
{
return x_8;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_8, 0);
x_113 = lean_ctor_get(x_8, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_8);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
lean_object* l_Lean_Meta_substCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_getMVarTag___boxed), 3, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_box(x_3);
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lambda__3___boxed), 6, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
lean_closure_set(x_9, 2, x_8);
x_10 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Meta_isClassExpensive___main___spec__4___rarg), 4, 2);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_Meta_withMVarContext___rarg(x_1, x_10, x_5, x_6);
return x_11;
}
}
lean_object* l_Lean_Meta_substCore___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_substCore___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
lean_object* l_Lean_Meta_substCore___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_8);
lean_dec(x_8);
x_16 = l_Lean_Meta_substCore___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_11);
lean_dec(x_6);
return x_16;
}
}
lean_object* l_Lean_Meta_substCore___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Meta_substCore___lambda__3(x_1, x_2, x_7, x_4, x_5, x_6);
return x_8;
}
}
lean_object* l_Lean_Meta_substCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; lean_object* x_9; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Meta_substCore(x_1, x_2, x_7, x_8, x_5, x_6);
lean_dec(x_5);
return x_9;
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
x_13 = l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(x_1, x_2, x_3, x_12, x_6, x_7);
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_53; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Expr_getAppNumArgsAux___main(x_18, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_25, x_26);
x_28 = lean_nat_sub(x_27, x_26);
lean_dec(x_27);
x_29 = l_Lean_Expr_getRevArg_x21___main(x_18, x_28);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_sub(x_25, x_30);
lean_dec(x_25);
x_32 = lean_nat_sub(x_31, x_26);
lean_dec(x_31);
x_33 = l_Lean_Expr_getRevArg_x21___main(x_18, x_32);
lean_dec(x_18);
x_53 = l_Lean_Expr_isFVar(x_33);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_box(0);
x_34 = x_54;
goto block_52;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = l_Lean_Expr_fvarId_x21(x_33);
x_56 = lean_name_eq(x_55, x_1);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_box(0);
x_34 = x_57;
goto block_52;
}
else
{
lean_object* x_58; uint8_t x_59; 
lean_inc(x_29);
lean_inc(x_3);
x_58 = l_Lean_MetavarContext_exprDependsOn(x_3, x_29, x_1);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_3);
x_60 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_61 = 1;
x_62 = lean_box(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_7);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_box(0);
x_34 = x_66;
goto block_52;
}
}
}
block_52:
{
uint8_t x_35; 
lean_dec(x_34);
x_35 = l_Lean_Expr_isFVar(x_29);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_16);
x_36 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_5 = x_36;
goto _start;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_Expr_fvarId_x21(x_29);
lean_dec(x_29);
x_39 = lean_name_eq(x_38, x_1);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_16);
x_40 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_5 = x_40;
goto _start;
}
else
{
lean_object* x_42; uint8_t x_43; 
lean_inc(x_3);
x_42 = l_Lean_MetavarContext_exprDependsOn(x_3, x_33, x_1);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_5);
lean_dec(x_3);
x_44 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_45 = 0;
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
if (lean_is_scalar(x_17)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_17;
}
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_7);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_17);
lean_dec(x_16);
x_50 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_5 = x_50;
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
lean_object* l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_53; 
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_Expr_getAppNumArgsAux___main(x_18, x_24);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_sub(x_25, x_26);
x_28 = lean_nat_sub(x_27, x_26);
lean_dec(x_27);
x_29 = l_Lean_Expr_getRevArg_x21___main(x_18, x_28);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_sub(x_25, x_30);
lean_dec(x_25);
x_32 = lean_nat_sub(x_31, x_26);
lean_dec(x_31);
x_33 = l_Lean_Expr_getRevArg_x21___main(x_18, x_32);
lean_dec(x_18);
x_53 = l_Lean_Expr_isFVar(x_33);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_box(0);
x_34 = x_54;
goto block_52;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = l_Lean_Expr_fvarId_x21(x_33);
x_56 = lean_name_eq(x_55, x_1);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_box(0);
x_34 = x_57;
goto block_52;
}
else
{
lean_object* x_58; uint8_t x_59; 
lean_inc(x_29);
lean_inc(x_3);
x_58 = l_Lean_MetavarContext_exprDependsOn(x_3, x_29, x_1);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_5);
lean_dec(x_3);
x_60 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_61 = 1;
x_62 = lean_box(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_7);
return x_65;
}
else
{
lean_object* x_66; 
x_66 = lean_box(0);
x_34 = x_66;
goto block_52;
}
}
}
block_52:
{
uint8_t x_35; 
lean_dec(x_34);
x_35 = l_Lean_Expr_isFVar(x_29);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_17);
lean_dec(x_16);
x_36 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_5 = x_36;
goto _start;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = l_Lean_Expr_fvarId_x21(x_29);
lean_dec(x_29);
x_39 = lean_name_eq(x_38, x_1);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_dec(x_33);
lean_dec(x_17);
lean_dec(x_16);
x_40 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_5 = x_40;
goto _start;
}
else
{
lean_object* x_42; uint8_t x_43; 
lean_inc(x_3);
x_42 = l_Lean_MetavarContext_exprDependsOn(x_3, x_33, x_1);
x_43 = lean_unbox(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_5);
lean_dec(x_3);
x_44 = l_Lean_LocalDecl_fvarId(x_16);
lean_dec(x_16);
x_45 = 0;
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
if (lean_is_scalar(x_17)) {
 x_48 = lean_alloc_ctor(1, 1, 0);
} else {
 x_48 = x_17;
}
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_7);
return x_49;
}
else
{
lean_object* x_50; 
lean_dec(x_17);
lean_dec(x_16);
x_50 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_5 = x_50;
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
lean_object* l_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_3);
x_8 = l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(x_1, x_2, x_3, x_7, x_5, x_6);
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
x_8 = l_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(x_1, x_2, x_3, x_7, x_5, x_6);
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
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
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
x_27 = 0;
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
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Lean_Expr_getAppNumArgsAux___main(x_6, x_41);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_sub(x_42, x_43);
x_45 = lean_nat_sub(x_44, x_43);
lean_dec(x_44);
x_46 = l_Lean_Expr_getRevArg_x21___main(x_6, x_45);
x_47 = lean_unsigned_to_nat(2u);
x_48 = lean_nat_sub(x_42, x_47);
lean_dec(x_42);
x_49 = lean_nat_sub(x_48, x_43);
lean_dec(x_48);
x_50 = l_Lean_Expr_getRevArg_x21___main(x_6, x_49);
x_51 = l_Lean_Expr_isFVar(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = l_Lean_Expr_isFVar(x_46);
lean_dec(x_46);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_1);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_6);
x_54 = l_Lean_indentExpr(x_53);
x_55 = l_Lean_Meta_subst___lambda__1___closed__6;
x_56 = lean_alloc_ctor(9, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
x_57 = l_Lean_Meta_substCore___lambda__3___closed__2;
x_58 = l_Lean_Meta_throwTacticEx___rarg(x_57, x_2, x_56, x_4, x_5);
return x_58;
}
else
{
uint8_t x_59; lean_object* x_60; 
lean_dec(x_6);
x_59 = 0;
x_60 = l_Lean_Meta_substCore(x_2, x_1, x_59, x_59, x_4, x_5);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_60, 0);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
lean_ctor_set(x_60, 0, x_63);
return x_60;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_60, 0);
x_65 = lean_ctor_get(x_60, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_60);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
else
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_60);
if (x_68 == 0)
{
return x_60;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_60, 0);
x_70 = lean_ctor_get(x_60, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_60);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
uint8_t x_72; uint8_t x_73; lean_object* x_74; 
lean_dec(x_46);
lean_dec(x_6);
x_72 = 1;
x_73 = 0;
x_74 = l_Lean_Meta_substCore(x_2, x_1, x_72, x_73, x_4, x_5);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
lean_ctor_set(x_74, 0, x_77);
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_74, 0);
x_79 = lean_ctor_get(x_74, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_74);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
else
{
uint8_t x_82; 
x_82 = !lean_is_exclusive(x_74);
if (x_82 == 0)
{
return x_74;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_74, 0);
x_84 = lean_ctor_get(x_74, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_74);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
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
x_8 = l_Lean_Meta_withMVarContext___rarg(x_1, x_7, x_3, x_4);
return x_8;
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
lean_object* l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_PersistentArray_findSomeMAux___main___at_Lean_Meta_subst___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* l_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_PersistentArray_findSomeM_x3f___at_Lean_Meta_subst___spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* _init_l___private_Init_Lean_Meta_Tactic_Subst_1__regTraceClasses___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Init_Lean_Meta_Tactic_Util_1__regTraceClasses___closed__2;
x_2 = l_Lean_Meta_substCore___lambda__3___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l___private_Init_Lean_Meta_Tactic_Subst_1__regTraceClasses(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l___private_Init_Lean_Meta_Tactic_Subst_1__regTraceClasses___closed__1;
x_3 = l_Lean_registerTraceClass(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init_Lean_Meta_AppBuilder(lean_object*);
lean_object* initialize_Init_Lean_Meta_Message(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Util(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Revert(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Intro(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_Clear(lean_object*);
lean_object* initialize_Init_Lean_Meta_Tactic_FVarSubst(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_Tactic_Subst(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Meta_AppBuilder(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Message(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_Revert(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_Intro(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_Clear(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_Tactic_FVarSubst(lean_io_mk_world());
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
l___private_Init_Lean_Meta_Tactic_Subst_1__regTraceClasses___closed__1 = _init_l___private_Init_Lean_Meta_Tactic_Subst_1__regTraceClasses___closed__1();
lean_mark_persistent(l___private_Init_Lean_Meta_Tactic_Subst_1__regTraceClasses___closed__1);
res = l___private_Init_Lean_Meta_Tactic_Subst_1__regTraceClasses(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
