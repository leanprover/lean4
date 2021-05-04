// Lean compiler output
// Module: Lean.Elab.Tactic.Rewrite
// Imports: Init Lean.Meta.Tactic.Rewrite Lean.Meta.Tactic.Replace Lean.Elab.Tactic.Basic Lean.Elab.Tactic.ElabTerm Lean.Elab.Tactic.Location
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
lean_object* l_Lean_Elab_Tactic_rewriteAll___lambda__1___closed__2;
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalERewriteSeq(lean_object*);
size_t l_USize_add(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_rewriteAll___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_rewriteAll___spec__1(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
extern lean_object* l_Lean_nullKind;
lean_object* l_Lean_Elab_Tactic_rewriteTarget___lambda__1(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decEq(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Elab_Tactic_rewriteAll___lambda__1___closed__1;
lean_object* l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaMAtMain___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalRewriteCore___spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_rewriteAll(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_rewrite___closed__1;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Elab_Tactic_withMainContext___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_rewriteAll___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclFVarId___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_USize_decLt(size_t, size_t);
lean_object* l_Lean_Elab_Tactic_rewriteTarget___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_replaceLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_rewriteAll___lambda__1(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalERewriteSeq___closed__1;
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_List_forIn_loop___at_Lean_Elab_resolveGlobalConstWithInfos___spec__1___rarg___lambda__1___closed__1;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_rewriteTarget(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_replaceTargetEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalRewriteCore___spec__3___boxed(lean_object**);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalERewriteSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_rewriteAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__2(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_expandOptLocation(lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclFVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getGoals___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_rewriteAll___lambda__1___closed__3;
lean_object* l_Lean_Elab_Tactic_rewriteTarget___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___closed__1;
lean_object* l_Lean_Elab_Tactic_evalRewriteCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclFVarId___lambda__1(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_getMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___rarg(lean_object*);
lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedSyntax;
lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Elab_Tactic_evalRewriteCore_match__1___rarg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclFVarId(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalRewriteCore___spec__1(uint8_t, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalRewriteCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Syntax_mkApp___closed__1;
lean_object* l_Std_PersistentArray_push___rarg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalERewriteSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* l_Lean_Meta_getLocalDeclFromUserName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalRewriteCore___spec__2(uint8_t, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_Elab_Tactic_tryTactic___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq___closed__1;
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalRewriteCore___spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_replaceMainGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalRewriteCore___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_erewriteSeq___closed__2;
lean_object* l_Lean_Elab_Tactic_evalRewriteSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalRewriteCore_match__1(lean_object*);
lean_object* l_Lean_Elab_Tactic_elabTerm___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_mkTacticInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Tactic_rewriteSeq___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_rewriteTarget___lambda__1(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_16 = l_Lean_Elab_Tactic_getMainTarget(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_20 = l_Lean_Meta_rewrite(x_14, x_17, x_3, x_1, x_19, x_2, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Elab_Tactic_getMainGoal(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_21, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_28 = l_Lean_Meta_replaceTargetEq(x_24, x_26, x_27, x_8, x_9, x_10, x_11, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_21, 2);
lean_inc(x_31);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_Elab_Tactic_replaceMainGoal(x_32, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_30);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_33;
}
else
{
uint8_t x_34; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_34 = !lean_is_exclusive(x_28);
if (x_34 == 0)
{
return x_28;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_28);
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
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_38 = !lean_is_exclusive(x_23);
if (x_38 == 0)
{
return x_23;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_23, 0);
x_40 = lean_ctor_get(x_23, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_23);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_42 = !lean_is_exclusive(x_20);
if (x_42 == 0)
{
return x_20;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_20, 0);
x_44 = lean_ctor_get(x_20, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_20);
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
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_16);
if (x_46 == 0)
{
return x_16;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_16, 0);
x_48 = lean_ctor_get(x_16, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_16);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_50 = !lean_is_exclusive(x_13);
if (x_50 == 0)
{
return x_13;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_13, 0);
x_52 = lean_ctor_get(x_13, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_13);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_rewriteTarget(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_13 = lean_box(0);
x_14 = 1;
x_15 = lean_box(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTerm___boxed), 12, 3);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_13);
lean_closure_set(x_16, 2, x_15);
x_17 = lean_box(x_2);
x_18 = lean_box(x_3);
x_19 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___lambda__1___boxed), 12, 2);
lean_closure_set(x_19, 0, x_17);
lean_closure_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaMAtMain___spec__1___rarg), 11, 2);
lean_closure_set(x_20, 0, x_16);
lean_closure_set(x_20, 1, x_19);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___rarg), 10, 3);
lean_closure_set(x_21, 0, x_20);
lean_closure_set(x_21, 1, x_4);
lean_closure_set(x_21, 2, x_5);
x_22 = 0;
x_23 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_21, x_22, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_23;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteTarget___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Lean_Elab_Tactic_rewriteTarget___lambda__1(x_13, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_15;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteTarget___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Elab_Tactic_rewriteTarget(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclFVarId___lambda__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_9);
lean_inc(x_1);
x_14 = l_Lean_Meta_getLocalDecl(x_1, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Elab_Tactic_getMainGoal(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_LocalDecl_type(x_15);
lean_dec(x_15);
x_21 = lean_box(0);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_22 = l_Lean_Meta_rewrite(x_18, x_20, x_4, x_2, x_21, x_3, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Elab_Tactic_getMainGoal(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_23, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_30 = l_Lean_Meta_replaceLocalDecl(x_26, x_1, x_28, x_29, x_9, x_10, x_11, x_12, x_27);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_23, 2);
lean_inc(x_34);
lean_dec(x_23);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Elab_Tactic_replaceMainGoal(x_35, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_32);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
return x_30;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_30, 0);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_30);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_23);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_25);
if (x_41 == 0)
{
return x_25;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_25, 0);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_25);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_22);
if (x_45 == 0)
{
return x_22;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_22, 0);
x_47 = lean_ctor_get(x_22, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_22);
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
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_17);
if (x_49 == 0)
{
return x_17;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_17, 0);
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_17);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_14);
if (x_53 == 0)
{
return x_14;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_14, 0);
x_55 = lean_ctor_get(x_14, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_14);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclFVarId(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_14 = lean_box(0);
x_15 = 1;
x_16 = lean_box(x_15);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_elabTerm___boxed), 12, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_14);
lean_closure_set(x_17, 2, x_16);
x_18 = lean_box(x_2);
x_19 = lean_box(x_4);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDeclFVarId___lambda__1___boxed), 13, 3);
lean_closure_set(x_20, 0, x_3);
lean_closure_set(x_20, 1, x_18);
lean_closure_set(x_20, 2, x_19);
x_21 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaMAtMain___spec__1___rarg), 11, 2);
lean_closure_set(x_21, 0, x_17);
lean_closure_set(x_21, 1, x_20);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_withMainContext___rarg), 10, 3);
lean_closure_set(x_22, 0, x_21);
lean_closure_set(x_22, 1, x_5);
lean_closure_set(x_22, 2, x_6);
x_23 = 0;
x_24 = l___private_Lean_Elab_SyntheticMVars_0__Lean_Elab_Term_withSynthesizeImp___rarg(x_22, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_24;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclFVarId___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_Elab_Tactic_rewriteLocalDeclFVarId___lambda__1(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteLocalDeclFVarId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Elab_Tactic_rewriteLocalDeclFVarId(x_1, x_14, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_getLocalDeclFromUserName(x_1, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__2(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_LocalDecl_fvarId(x_4);
x_15 = l_Lean_Elab_Tactic_rewriteLocalDeclFVarId(x_1, x_2, x_14, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__1___boxed), 10, 1);
lean_closure_set(x_14, 0, x_3);
x_15 = lean_box(x_2);
x_16 = lean_box(x_4);
x_17 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__2___boxed), 13, 3);
lean_closure_set(x_17, 0, x_1);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_16);
x_18 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaMAtMain___spec__1___rarg), 11, 2);
lean_closure_set(x_18, 0, x_14);
lean_closure_set(x_18, 1, x_17);
x_19 = l_Lean_Elab_Tactic_withMainContext___rarg(x_18, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_19;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = l_Lean_Elab_Tactic_rewriteLocalDecl___lambda__2(x_1, x_14, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
return x_16;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteLocalDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_Elab_Tactic_rewriteLocalDecl(x_1, x_14, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_rewriteAll___spec__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = x_6 < x_5;
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_18 = lean_box(x_7);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_array_uget(x_4, x_6);
x_21 = lean_box(x_2);
x_22 = lean_box(x_3);
lean_inc(x_1);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteLocalDeclFVarId___boxed), 13, 4);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_21);
lean_closure_set(x_23, 2, x_20);
lean_closure_set(x_23, 3, x_22);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_24 = l_Lean_Elab_Tactic_tryTactic___rarg(x_23, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (x_7 == 0)
{
lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = 1;
x_28 = x_6 + x_27;
x_29 = lean_unbox(x_25);
lean_dec(x_25);
x_6 = x_28;
x_7 = x_29;
x_16 = x_26;
goto _start;
}
else
{
lean_object* x_31; size_t x_32; size_t x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_32 = 1;
x_33 = x_6 + x_32;
x_34 = 1;
x_6 = x_33;
x_7 = x_34;
x_16 = x_31;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_rewriteAll___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("did not find instance of the pattern in the current goal");
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_rewriteAll___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_rewriteAll___lambda__1___closed__1;
x_2 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_rewriteAll___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Tactic_rewriteAll___lambda__1___closed__2;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteAll___lambda__1(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_15 = l_Lean_LocalContext_getFVarIds(x_5);
x_16 = l_Array_reverse___rarg(x_15);
x_17 = lean_array_get_size(x_16);
x_18 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_19 = 0;
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_20 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_rewriteAll___spec__1(x_1, x_2, x_3, x_16, x_18, x_19, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_Elab_Tactic_getMainGoal(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Meta_rewrite___closed__1;
x_28 = l_Lean_Elab_Tactic_rewriteAll___lambda__1___closed__3;
x_29 = lean_box(0);
x_30 = l_Lean_Meta_throwTacticEx___rarg(x_27, x_25, x_28, x_29, x_10, x_11, x_12, x_13, x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_31 = !lean_is_exclusive(x_24);
if (x_31 == 0)
{
return x_24;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_24, 0);
x_33 = lean_ctor_get(x_24, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_24);
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
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_35 = !lean_is_exclusive(x_20);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_20, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_20, 0, x_37);
return x_20;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_20, 1);
lean_inc(x_38);
lean_dec(x_20);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
lean_object* l_Lean_Elab_Tactic_rewriteAll(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_13 = lean_box(x_2);
x_14 = lean_box(x_3);
lean_inc(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteTarget___boxed), 12, 3);
lean_closure_set(x_15, 0, x_1);
lean_closure_set(x_15, 1, x_13);
lean_closure_set(x_15, 2, x_14);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lean_Elab_Tactic_tryTactic___rarg(x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(x_2);
x_20 = lean_box(x_3);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_rewriteAll___lambda__1___boxed), 14, 4);
lean_closure_set(x_21, 0, x_1);
lean_closure_set(x_21, 1, x_19);
lean_closure_set(x_21, 2, x_20);
lean_closure_set(x_21, 3, x_17);
x_22 = l___private_Lean_Elab_Tactic_Basic_0__Lean_Elab_Tactic_sortFVarIds___closed__1;
x_23 = lean_alloc_closure((void*)(l_ReaderT_bind___at_Lean_Elab_Tactic_liftMetaMAtMain___spec__1___rarg), 11, 2);
lean_closure_set(x_23, 0, x_22);
lean_closure_set(x_23, 1, x_21);
x_24 = l_Lean_Elab_Tactic_withMainContext___rarg(x_23, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
return x_24;
}
}
lean_object* l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_rewriteAll___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; size_t x_19; size_t x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_unbox(x_2);
lean_dec(x_2);
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_20 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_21 = lean_unbox(x_7);
lean_dec(x_7);
x_22 = l_Array_forInUnsafe_loop___at_Lean_Elab_Tactic_rewriteAll___spec__1(x_1, x_17, x_18, x_4, x_19, x_20, x_21, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
return x_22;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteAll___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox(x_4);
lean_dec(x_4);
x_18 = l_Lean_Elab_Tactic_rewriteAll___lambda__1(x_1, x_15, x_16, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_5);
return x_18;
}
}
lean_object* l_Lean_Elab_Tactic_rewriteAll___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_2);
lean_dec(x_2);
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Elab_Tactic_rewriteAll(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
lean_object* l_Lean_Elab_Tactic_evalRewriteCore_match__1___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_8 = lean_box(x_7);
x_9 = lean_apply_2(x_2, x_6, x_8);
return x_9;
}
}
}
lean_object* l_Lean_Elab_Tactic_evalRewriteCore_match__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteCore_match__1___rarg), 3, 0);
return x_2;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalRewriteCore___spec__1(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = x_5 == x_6;
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = lean_array_uget(x_4, x_5);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_19 = l_Lean_Elab_Tactic_rewriteLocalDecl(x_2, x_3, x_18, x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = x_5 + x_22;
x_5 = x_23;
x_7 = x_20;
x_16 = x_21;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_16);
return x_29;
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalRewriteCore___spec__2(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; 
x_17 = x_5 == x_6;
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
x_18 = lean_array_uget(x_4, x_5);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_19 = l_Lean_Elab_Tactic_rewriteLocalDecl(x_2, x_3, x_18, x_1, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = 1;
x_23 = x_5 + x_22;
x_5 = x_23;
x_7 = x_20;
x_16 = x_21;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_19);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_16);
return x_29;
}
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalRewriteCore___spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_5, 1);
x_19 = lean_nat_dec_le(x_18, x_7);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_6, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_42; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_8);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_6, x_22);
lean_dec(x_6);
x_54 = lean_unsigned_to_nat(2u);
x_55 = lean_nat_mul(x_7, x_54);
x_56 = l_Lean_instInhabitedSyntax;
x_57 = lean_array_get(x_56, x_2, x_55);
x_58 = lean_nat_add(x_55, x_22);
lean_dec(x_55);
x_59 = lean_nat_dec_lt(x_58, x_4);
x_60 = l_Lean_Syntax_mkApp___closed__1;
lean_inc(x_57);
x_61 = lean_array_push(x_60, x_57);
x_62 = l_Lean_Syntax_getArg(x_57, x_20);
x_63 = l_Lean_Syntax_isNone(x_62);
lean_dec(x_62);
x_64 = l_Lean_Syntax_getArg(x_57, x_22);
x_65 = lean_st_ref_get(x_16, x_17);
if (x_59 == 0)
{
lean_object* x_579; 
lean_dec(x_58);
x_579 = lean_box(0);
x_66 = x_579;
goto block_578;
}
else
{
lean_object* x_580; 
x_580 = lean_array_fget(x_2, x_58);
lean_dec(x_58);
x_66 = x_580;
goto block_578;
}
block_41:
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_ctor_get(x_25, 0);
lean_inc(x_30);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
lean_dec(x_25);
x_34 = lean_ctor_get(x_5, 2);
x_35 = lean_nat_add(x_7, x_34);
lean_dec(x_7);
x_6 = x_23;
x_7 = x_35;
x_8 = x_33;
x_17 = x_32;
goto _start;
}
}
else
{
uint8_t x_37; 
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
block_53:
{
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = l_List_forIn_loop___at_Lean_Elab_resolveGlobalConstWithInfos___spec__1___rarg___lambda__1___closed__1;
lean_ctor_set(x_42, 0, x_45);
x_24 = x_42;
goto block_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = l_List_forIn_loop___at_Lean_Elab_resolveGlobalConstWithInfos___spec__1___rarg___lambda__1___closed__1;
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
x_24 = x_48;
goto block_41;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_42);
if (x_49 == 0)
{
x_24 = x_42;
goto block_41;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_42, 0);
x_51 = lean_ctor_get(x_42, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_42);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_24 = x_52;
goto block_41;
}
}
}
block_578:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_array_push(x_61, x_66);
x_68 = l_Lean_nullKind;
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
if (x_63 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_70 = lean_ctor_get(x_65, 1);
lean_inc(x_70);
lean_dec(x_65);
x_71 = lean_st_ref_get(x_14, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
x_75 = l_Lean_Elab_Tactic_getGoals___rarg(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_73);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_st_ref_get(x_16, x_77);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = lean_st_ref_get(x_12, x_79);
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 5);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_ctor_get_uint8(x_82, sizeof(void*)*2);
lean_dec(x_82);
if (x_83 == 0)
{
uint8_t x_84; 
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_69);
x_84 = !lean_is_exclusive(x_80);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_85 = lean_ctor_get(x_80, 1);
x_86 = lean_ctor_get(x_80, 0);
lean_dec(x_86);
x_87 = lean_ctor_get(x_15, 0);
x_88 = lean_ctor_get(x_15, 1);
x_89 = lean_ctor_get(x_15, 2);
x_90 = lean_ctor_get(x_15, 3);
x_91 = lean_ctor_get(x_15, 4);
x_92 = lean_ctor_get(x_15, 5);
x_93 = lean_ctor_get(x_15, 6);
x_94 = lean_ctor_get(x_15, 7);
x_95 = l_Lean_replaceRef(x_57, x_90);
lean_dec(x_57);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
x_96 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_96, 0, x_87);
lean_ctor_set(x_96, 1, x_88);
lean_ctor_set(x_96, 2, x_89);
lean_ctor_set(x_96, 3, x_95);
lean_ctor_set(x_96, 4, x_91);
lean_ctor_set(x_96, 5, x_92);
lean_ctor_set(x_96, 6, x_93);
lean_ctor_set(x_96, 7, x_94);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_97; lean_object* x_98; 
lean_free_object(x_80);
x_97 = 1;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_98 = l_Lean_Elab_Tactic_rewriteAll(x_64, x_97, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_96, x_16, x_85);
x_42 = x_98;
goto block_53;
}
else
{
lean_object* x_99; uint8_t x_100; lean_object* x_101; uint8_t x_102; 
x_99 = lean_ctor_get(x_3, 0);
x_100 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_101 = lean_array_get_size(x_99);
x_102 = lean_nat_dec_lt(x_20, x_101);
if (x_102 == 0)
{
lean_dec(x_101);
if (x_100 == 0)
{
lean_object* x_103; 
lean_dec(x_96);
lean_dec(x_64);
x_103 = lean_box(0);
lean_ctor_set(x_80, 0, x_103);
x_42 = x_80;
goto block_53;
}
else
{
uint8_t x_104; lean_object* x_105; 
lean_free_object(x_80);
x_104 = 1;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_105 = l_Lean_Elab_Tactic_rewriteTarget(x_64, x_104, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_96, x_16, x_85);
x_42 = x_105;
goto block_53;
}
}
else
{
uint8_t x_106; 
x_106 = lean_nat_dec_le(x_101, x_101);
if (x_106 == 0)
{
lean_dec(x_101);
if (x_100 == 0)
{
lean_object* x_107; 
lean_dec(x_96);
lean_dec(x_64);
x_107 = lean_box(0);
lean_ctor_set(x_80, 0, x_107);
x_42 = x_80;
goto block_53;
}
else
{
uint8_t x_108; lean_object* x_109; 
lean_free_object(x_80);
x_108 = 1;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_109 = l_Lean_Elab_Tactic_rewriteTarget(x_64, x_108, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_96, x_16, x_85);
x_42 = x_109;
goto block_53;
}
}
else
{
size_t x_110; size_t x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; 
lean_free_object(x_80);
x_110 = 0;
x_111 = lean_usize_of_nat(x_101);
lean_dec(x_101);
x_112 = 1;
x_113 = lean_box(0);
lean_inc(x_16);
lean_inc(x_96);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_64);
x_114 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalRewriteCore___spec__1(x_1, x_64, x_112, x_99, x_110, x_111, x_113, x_9, x_10, x_11, x_12, x_13, x_14, x_96, x_16, x_85);
if (lean_obj_tag(x_114) == 0)
{
if (x_100 == 0)
{
uint8_t x_115; 
lean_dec(x_96);
lean_dec(x_64);
x_115 = !lean_is_exclusive(x_114);
if (x_115 == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_114, 0);
lean_dec(x_116);
lean_ctor_set(x_114, 0, x_113);
x_42 = x_114;
goto block_53;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_113);
lean_ctor_set(x_118, 1, x_117);
x_42 = x_118;
goto block_53;
}
}
else
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_114, 1);
lean_inc(x_119);
lean_dec(x_114);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_120 = l_Lean_Elab_Tactic_rewriteTarget(x_64, x_112, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_96, x_16, x_119);
x_42 = x_120;
goto block_53;
}
}
else
{
uint8_t x_121; 
lean_dec(x_96);
lean_dec(x_64);
x_121 = !lean_is_exclusive(x_114);
if (x_121 == 0)
{
x_42 = x_114;
goto block_53;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_114, 0);
x_123 = lean_ctor_get(x_114, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_114);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
x_42 = x_124;
goto block_53;
}
}
}
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_125 = lean_ctor_get(x_80, 1);
lean_inc(x_125);
lean_dec(x_80);
x_126 = lean_ctor_get(x_15, 0);
x_127 = lean_ctor_get(x_15, 1);
x_128 = lean_ctor_get(x_15, 2);
x_129 = lean_ctor_get(x_15, 3);
x_130 = lean_ctor_get(x_15, 4);
x_131 = lean_ctor_get(x_15, 5);
x_132 = lean_ctor_get(x_15, 6);
x_133 = lean_ctor_get(x_15, 7);
x_134 = l_Lean_replaceRef(x_57, x_129);
lean_dec(x_57);
lean_inc(x_133);
lean_inc(x_132);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_128);
lean_inc(x_127);
lean_inc(x_126);
x_135 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_135, 0, x_126);
lean_ctor_set(x_135, 1, x_127);
lean_ctor_set(x_135, 2, x_128);
lean_ctor_set(x_135, 3, x_134);
lean_ctor_set(x_135, 4, x_130);
lean_ctor_set(x_135, 5, x_131);
lean_ctor_set(x_135, 6, x_132);
lean_ctor_set(x_135, 7, x_133);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_136; lean_object* x_137; 
x_136 = 1;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_137 = l_Lean_Elab_Tactic_rewriteAll(x_64, x_136, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_135, x_16, x_125);
x_42 = x_137;
goto block_53;
}
else
{
lean_object* x_138; uint8_t x_139; lean_object* x_140; uint8_t x_141; 
x_138 = lean_ctor_get(x_3, 0);
x_139 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_140 = lean_array_get_size(x_138);
x_141 = lean_nat_dec_lt(x_20, x_140);
if (x_141 == 0)
{
lean_dec(x_140);
if (x_139 == 0)
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_135);
lean_dec(x_64);
x_142 = lean_box(0);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_125);
x_42 = x_143;
goto block_53;
}
else
{
uint8_t x_144; lean_object* x_145; 
x_144 = 1;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_145 = l_Lean_Elab_Tactic_rewriteTarget(x_64, x_144, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_135, x_16, x_125);
x_42 = x_145;
goto block_53;
}
}
else
{
uint8_t x_146; 
x_146 = lean_nat_dec_le(x_140, x_140);
if (x_146 == 0)
{
lean_dec(x_140);
if (x_139 == 0)
{
lean_object* x_147; lean_object* x_148; 
lean_dec(x_135);
lean_dec(x_64);
x_147 = lean_box(0);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_125);
x_42 = x_148;
goto block_53;
}
else
{
uint8_t x_149; lean_object* x_150; 
x_149 = 1;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_150 = l_Lean_Elab_Tactic_rewriteTarget(x_64, x_149, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_135, x_16, x_125);
x_42 = x_150;
goto block_53;
}
}
else
{
size_t x_151; size_t x_152; uint8_t x_153; lean_object* x_154; lean_object* x_155; 
x_151 = 0;
x_152 = lean_usize_of_nat(x_140);
lean_dec(x_140);
x_153 = 1;
x_154 = lean_box(0);
lean_inc(x_16);
lean_inc(x_135);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_64);
x_155 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalRewriteCore___spec__1(x_1, x_64, x_153, x_138, x_151, x_152, x_154, x_9, x_10, x_11, x_12, x_13, x_14, x_135, x_16, x_125);
if (lean_obj_tag(x_155) == 0)
{
if (x_139 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_135);
lean_dec(x_64);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_157 = x_155;
} else {
 lean_dec_ref(x_155);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_154);
lean_ctor_set(x_158, 1, x_156);
x_42 = x_158;
goto block_53;
}
else
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_155, 1);
lean_inc(x_159);
lean_dec(x_155);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_160 = l_Lean_Elab_Tactic_rewriteTarget(x_64, x_153, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_135, x_16, x_159);
x_42 = x_160;
goto block_53;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_135);
lean_dec(x_64);
x_161 = lean_ctor_get(x_155, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_155, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_163 = x_155;
} else {
 lean_dec_ref(x_155);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
x_42 = x_164;
goto block_53;
}
}
}
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_222; lean_object* x_223; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_165 = lean_ctor_get(x_80, 1);
lean_inc(x_165);
lean_dec(x_80);
x_166 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg(x_12, x_13, x_14, x_15, x_16, x_165);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
x_275 = lean_ctor_get(x_15, 0);
x_276 = lean_ctor_get(x_15, 1);
x_277 = lean_ctor_get(x_15, 2);
x_278 = lean_ctor_get(x_15, 3);
x_279 = lean_ctor_get(x_15, 4);
x_280 = lean_ctor_get(x_15, 5);
x_281 = lean_ctor_get(x_15, 6);
x_282 = lean_ctor_get(x_15, 7);
x_283 = l_Lean_replaceRef(x_57, x_278);
lean_dec(x_57);
lean_inc(x_282);
lean_inc(x_281);
lean_inc(x_280);
lean_inc(x_279);
lean_inc(x_277);
lean_inc(x_276);
lean_inc(x_275);
x_284 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_284, 0, x_275);
lean_ctor_set(x_284, 1, x_276);
lean_ctor_set(x_284, 2, x_277);
lean_ctor_set(x_284, 3, x_283);
lean_ctor_set(x_284, 4, x_279);
lean_ctor_set(x_284, 5, x_280);
lean_ctor_set(x_284, 6, x_281);
lean_ctor_set(x_284, 7, x_282);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_285; lean_object* x_286; 
x_285 = 1;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_286 = l_Lean_Elab_Tactic_rewriteAll(x_64, x_285, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_284, x_16, x_168);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_169 = x_287;
x_170 = x_288;
goto block_221;
}
else
{
lean_object* x_289; lean_object* x_290; 
x_289 = lean_ctor_get(x_286, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_286, 1);
lean_inc(x_290);
lean_dec(x_286);
x_222 = x_289;
x_223 = x_290;
goto block_274;
}
}
else
{
lean_object* x_291; uint8_t x_292; lean_object* x_293; uint8_t x_294; 
x_291 = lean_ctor_get(x_3, 0);
x_292 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_293 = lean_array_get_size(x_291);
x_294 = lean_nat_dec_lt(x_20, x_293);
if (x_294 == 0)
{
lean_dec(x_293);
if (x_292 == 0)
{
lean_object* x_295; 
lean_dec(x_284);
lean_dec(x_64);
x_295 = lean_box(0);
x_169 = x_295;
x_170 = x_168;
goto block_221;
}
else
{
uint8_t x_296; lean_object* x_297; 
x_296 = 1;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_297 = l_Lean_Elab_Tactic_rewriteTarget(x_64, x_296, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_284, x_16, x_168);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_169 = x_298;
x_170 = x_299;
goto block_221;
}
else
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_297, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_297, 1);
lean_inc(x_301);
lean_dec(x_297);
x_222 = x_300;
x_223 = x_301;
goto block_274;
}
}
}
else
{
uint8_t x_302; 
x_302 = lean_nat_dec_le(x_293, x_293);
if (x_302 == 0)
{
lean_dec(x_293);
if (x_292 == 0)
{
lean_object* x_303; 
lean_dec(x_284);
lean_dec(x_64);
x_303 = lean_box(0);
x_169 = x_303;
x_170 = x_168;
goto block_221;
}
else
{
uint8_t x_304; lean_object* x_305; 
x_304 = 1;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_305 = l_Lean_Elab_Tactic_rewriteTarget(x_64, x_304, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_284, x_16, x_168);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
x_169 = x_306;
x_170 = x_307;
goto block_221;
}
else
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_ctor_get(x_305, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_305, 1);
lean_inc(x_309);
lean_dec(x_305);
x_222 = x_308;
x_223 = x_309;
goto block_274;
}
}
}
else
{
size_t x_310; size_t x_311; uint8_t x_312; lean_object* x_313; lean_object* x_314; 
x_310 = 0;
x_311 = lean_usize_of_nat(x_293);
lean_dec(x_293);
x_312 = 1;
x_313 = lean_box(0);
lean_inc(x_16);
lean_inc(x_284);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_64);
x_314 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalRewriteCore___spec__2(x_1, x_64, x_312, x_291, x_310, x_311, x_313, x_9, x_10, x_11, x_12, x_13, x_14, x_284, x_16, x_168);
if (lean_obj_tag(x_314) == 0)
{
if (x_292 == 0)
{
lean_object* x_315; 
lean_dec(x_284);
lean_dec(x_64);
x_315 = lean_ctor_get(x_314, 1);
lean_inc(x_315);
lean_dec(x_314);
x_169 = x_313;
x_170 = x_315;
goto block_221;
}
else
{
lean_object* x_316; lean_object* x_317; 
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_317 = l_Lean_Elab_Tactic_rewriteTarget(x_64, x_312, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_284, x_16, x_316);
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_318; lean_object* x_319; 
x_318 = lean_ctor_get(x_317, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
x_169 = x_318;
x_170 = x_319;
goto block_221;
}
else
{
lean_object* x_320; lean_object* x_321; 
x_320 = lean_ctor_get(x_317, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_317, 1);
lean_inc(x_321);
lean_dec(x_317);
x_222 = x_320;
x_223 = x_321;
goto block_274;
}
}
}
else
{
lean_object* x_322; lean_object* x_323; 
lean_dec(x_284);
lean_dec(x_64);
x_322 = lean_ctor_get(x_314, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_314, 1);
lean_inc(x_323);
lean_dec(x_314);
x_222 = x_322;
x_223 = x_323;
goto block_274;
}
}
}
}
block_221:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_171 = lean_st_ref_get(x_16, x_170);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
lean_dec(x_171);
x_173 = lean_st_ref_get(x_12, x_172);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_ctor_get(x_174, 5);
lean_inc(x_176);
lean_dec(x_174);
x_177 = lean_ctor_get(x_176, 1);
lean_inc(x_177);
lean_dec(x_176);
x_178 = l_Lean_Elab_Tactic_mkTacticInfo(x_74, x_76, x_69, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_175);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_177);
x_182 = lean_st_ref_get(x_16, x_180);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_184 = lean_st_ref_take(x_12, x_183);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_185, 5);
lean_inc(x_186);
x_187 = lean_ctor_get(x_184, 1);
lean_inc(x_187);
lean_dec(x_184);
x_188 = !lean_is_exclusive(x_185);
if (x_188 == 0)
{
lean_object* x_189; uint8_t x_190; 
x_189 = lean_ctor_get(x_185, 5);
lean_dec(x_189);
x_190 = !lean_is_exclusive(x_186);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_186, 1);
lean_dec(x_191);
x_192 = l_Std_PersistentArray_push___rarg(x_167, x_181);
lean_ctor_set(x_186, 1, x_192);
x_193 = lean_st_ref_set(x_12, x_185, x_187);
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
lean_object* x_195; 
x_195 = lean_ctor_get(x_193, 0);
lean_dec(x_195);
lean_ctor_set(x_193, 0, x_169);
x_42 = x_193;
goto block_53;
}
else
{
lean_object* x_196; lean_object* x_197; 
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
lean_dec(x_193);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_169);
lean_ctor_set(x_197, 1, x_196);
x_42 = x_197;
goto block_53;
}
}
else
{
uint8_t x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_198 = lean_ctor_get_uint8(x_186, sizeof(void*)*2);
x_199 = lean_ctor_get(x_186, 0);
lean_inc(x_199);
lean_dec(x_186);
x_200 = l_Std_PersistentArray_push___rarg(x_167, x_181);
x_201 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
lean_ctor_set_uint8(x_201, sizeof(void*)*2, x_198);
lean_ctor_set(x_185, 5, x_201);
x_202 = lean_st_ref_set(x_12, x_185, x_187);
x_203 = lean_ctor_get(x_202, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_204 = x_202;
} else {
 lean_dec_ref(x_202);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_169);
lean_ctor_set(x_205, 1, x_203);
x_42 = x_205;
goto block_53;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_206 = lean_ctor_get(x_185, 0);
x_207 = lean_ctor_get(x_185, 1);
x_208 = lean_ctor_get(x_185, 2);
x_209 = lean_ctor_get(x_185, 3);
x_210 = lean_ctor_get(x_185, 4);
lean_inc(x_210);
lean_inc(x_209);
lean_inc(x_208);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_185);
x_211 = lean_ctor_get_uint8(x_186, sizeof(void*)*2);
x_212 = lean_ctor_get(x_186, 0);
lean_inc(x_212);
if (lean_is_exclusive(x_186)) {
 lean_ctor_release(x_186, 0);
 lean_ctor_release(x_186, 1);
 x_213 = x_186;
} else {
 lean_dec_ref(x_186);
 x_213 = lean_box(0);
}
x_214 = l_Std_PersistentArray_push___rarg(x_167, x_181);
if (lean_is_scalar(x_213)) {
 x_215 = lean_alloc_ctor(0, 2, 1);
} else {
 x_215 = x_213;
}
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_214);
lean_ctor_set_uint8(x_215, sizeof(void*)*2, x_211);
x_216 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_216, 0, x_206);
lean_ctor_set(x_216, 1, x_207);
lean_ctor_set(x_216, 2, x_208);
lean_ctor_set(x_216, 3, x_209);
lean_ctor_set(x_216, 4, x_210);
lean_ctor_set(x_216, 5, x_215);
x_217 = lean_st_ref_set(x_12, x_216, x_187);
x_218 = lean_ctor_get(x_217, 1);
lean_inc(x_218);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_219 = x_217;
} else {
 lean_dec_ref(x_217);
 x_219 = lean_box(0);
}
if (lean_is_scalar(x_219)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_219;
}
lean_ctor_set(x_220, 0, x_169);
lean_ctor_set(x_220, 1, x_218);
x_42 = x_220;
goto block_53;
}
}
block_274:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint8_t x_241; 
x_224 = lean_st_ref_get(x_16, x_223);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
x_226 = lean_st_ref_get(x_12, x_225);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_226, 1);
lean_inc(x_228);
lean_dec(x_226);
x_229 = lean_ctor_get(x_227, 5);
lean_inc(x_229);
lean_dec(x_227);
x_230 = lean_ctor_get(x_229, 1);
lean_inc(x_230);
lean_dec(x_229);
x_231 = l_Lean_Elab_Tactic_mkTacticInfo(x_74, x_76, x_69, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_228);
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_230);
x_235 = lean_st_ref_get(x_16, x_233);
x_236 = lean_ctor_get(x_235, 1);
lean_inc(x_236);
lean_dec(x_235);
x_237 = lean_st_ref_take(x_12, x_236);
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_238, 5);
lean_inc(x_239);
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
lean_dec(x_237);
x_241 = !lean_is_exclusive(x_238);
if (x_241 == 0)
{
lean_object* x_242; uint8_t x_243; 
x_242 = lean_ctor_get(x_238, 5);
lean_dec(x_242);
x_243 = !lean_is_exclusive(x_239);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; uint8_t x_247; 
x_244 = lean_ctor_get(x_239, 1);
lean_dec(x_244);
x_245 = l_Std_PersistentArray_push___rarg(x_167, x_234);
lean_ctor_set(x_239, 1, x_245);
x_246 = lean_st_ref_set(x_12, x_238, x_240);
x_247 = !lean_is_exclusive(x_246);
if (x_247 == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_246, 0);
lean_dec(x_248);
lean_ctor_set_tag(x_246, 1);
lean_ctor_set(x_246, 0, x_222);
x_42 = x_246;
goto block_53;
}
else
{
lean_object* x_249; lean_object* x_250; 
x_249 = lean_ctor_get(x_246, 1);
lean_inc(x_249);
lean_dec(x_246);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_222);
lean_ctor_set(x_250, 1, x_249);
x_42 = x_250;
goto block_53;
}
}
else
{
uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_251 = lean_ctor_get_uint8(x_239, sizeof(void*)*2);
x_252 = lean_ctor_get(x_239, 0);
lean_inc(x_252);
lean_dec(x_239);
x_253 = l_Std_PersistentArray_push___rarg(x_167, x_234);
x_254 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
lean_ctor_set_uint8(x_254, sizeof(void*)*2, x_251);
lean_ctor_set(x_238, 5, x_254);
x_255 = lean_st_ref_set(x_12, x_238, x_240);
x_256 = lean_ctor_get(x_255, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_255)) {
 lean_ctor_release(x_255, 0);
 lean_ctor_release(x_255, 1);
 x_257 = x_255;
} else {
 lean_dec_ref(x_255);
 x_257 = lean_box(0);
}
if (lean_is_scalar(x_257)) {
 x_258 = lean_alloc_ctor(1, 2, 0);
} else {
 x_258 = x_257;
 lean_ctor_set_tag(x_258, 1);
}
lean_ctor_set(x_258, 0, x_222);
lean_ctor_set(x_258, 1, x_256);
x_42 = x_258;
goto block_53;
}
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; uint8_t x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_259 = lean_ctor_get(x_238, 0);
x_260 = lean_ctor_get(x_238, 1);
x_261 = lean_ctor_get(x_238, 2);
x_262 = lean_ctor_get(x_238, 3);
x_263 = lean_ctor_get(x_238, 4);
lean_inc(x_263);
lean_inc(x_262);
lean_inc(x_261);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_238);
x_264 = lean_ctor_get_uint8(x_239, sizeof(void*)*2);
x_265 = lean_ctor_get(x_239, 0);
lean_inc(x_265);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_266 = x_239;
} else {
 lean_dec_ref(x_239);
 x_266 = lean_box(0);
}
x_267 = l_Std_PersistentArray_push___rarg(x_167, x_234);
if (lean_is_scalar(x_266)) {
 x_268 = lean_alloc_ctor(0, 2, 1);
} else {
 x_268 = x_266;
}
lean_ctor_set(x_268, 0, x_265);
lean_ctor_set(x_268, 1, x_267);
lean_ctor_set_uint8(x_268, sizeof(void*)*2, x_264);
x_269 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_269, 0, x_259);
lean_ctor_set(x_269, 1, x_260);
lean_ctor_set(x_269, 2, x_261);
lean_ctor_set(x_269, 3, x_262);
lean_ctor_set(x_269, 4, x_263);
lean_ctor_set(x_269, 5, x_268);
x_270 = lean_st_ref_set(x_12, x_269, x_240);
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_272 = x_270;
} else {
 lean_dec_ref(x_270);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_272;
 lean_ctor_set_tag(x_273, 1);
}
lean_ctor_set(x_273, 0, x_222);
lean_ctor_set(x_273, 1, x_271);
x_42 = x_273;
goto block_53;
}
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; uint8_t x_337; 
x_324 = lean_ctor_get(x_65, 1);
lean_inc(x_324);
lean_dec(x_65);
x_325 = lean_st_ref_get(x_14, x_324);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
lean_dec(x_325);
x_328 = lean_ctor_get(x_326, 0);
lean_inc(x_328);
lean_dec(x_326);
x_329 = l_Lean_Elab_Tactic_getGoals___rarg(x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_327);
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
lean_dec(x_329);
x_332 = lean_st_ref_get(x_16, x_331);
x_333 = lean_ctor_get(x_332, 1);
lean_inc(x_333);
lean_dec(x_332);
x_334 = lean_st_ref_get(x_12, x_333);
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_335, 5);
lean_inc(x_336);
lean_dec(x_335);
x_337 = lean_ctor_get_uint8(x_336, sizeof(void*)*2);
lean_dec(x_336);
if (x_337 == 0)
{
uint8_t x_338; 
lean_dec(x_330);
lean_dec(x_328);
lean_dec(x_69);
x_338 = !lean_is_exclusive(x_334);
if (x_338 == 0)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_339 = lean_ctor_get(x_334, 1);
x_340 = lean_ctor_get(x_334, 0);
lean_dec(x_340);
x_341 = lean_ctor_get(x_15, 0);
x_342 = lean_ctor_get(x_15, 1);
x_343 = lean_ctor_get(x_15, 2);
x_344 = lean_ctor_get(x_15, 3);
x_345 = lean_ctor_get(x_15, 4);
x_346 = lean_ctor_get(x_15, 5);
x_347 = lean_ctor_get(x_15, 6);
x_348 = lean_ctor_get(x_15, 7);
x_349 = l_Lean_replaceRef(x_57, x_344);
lean_dec(x_57);
lean_inc(x_348);
lean_inc(x_347);
lean_inc(x_346);
lean_inc(x_345);
lean_inc(x_343);
lean_inc(x_342);
lean_inc(x_341);
x_350 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_350, 0, x_341);
lean_ctor_set(x_350, 1, x_342);
lean_ctor_set(x_350, 2, x_343);
lean_ctor_set(x_350, 3, x_349);
lean_ctor_set(x_350, 4, x_345);
lean_ctor_set(x_350, 5, x_346);
lean_ctor_set(x_350, 6, x_347);
lean_ctor_set(x_350, 7, x_348);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_351; lean_object* x_352; 
lean_free_object(x_334);
x_351 = 0;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_352 = l_Lean_Elab_Tactic_rewriteAll(x_64, x_351, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_350, x_16, x_339);
x_42 = x_352;
goto block_53;
}
else
{
lean_object* x_353; uint8_t x_354; lean_object* x_355; uint8_t x_356; 
x_353 = lean_ctor_get(x_3, 0);
x_354 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_355 = lean_array_get_size(x_353);
x_356 = lean_nat_dec_lt(x_20, x_355);
if (x_356 == 0)
{
lean_dec(x_355);
if (x_354 == 0)
{
lean_object* x_357; 
lean_dec(x_350);
lean_dec(x_64);
x_357 = lean_box(0);
lean_ctor_set(x_334, 0, x_357);
x_42 = x_334;
goto block_53;
}
else
{
uint8_t x_358; lean_object* x_359; 
lean_free_object(x_334);
x_358 = 0;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_359 = l_Lean_Elab_Tactic_rewriteTarget(x_64, x_358, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_350, x_16, x_339);
x_42 = x_359;
goto block_53;
}
}
else
{
uint8_t x_360; 
x_360 = lean_nat_dec_le(x_355, x_355);
if (x_360 == 0)
{
lean_dec(x_355);
if (x_354 == 0)
{
lean_object* x_361; 
lean_dec(x_350);
lean_dec(x_64);
x_361 = lean_box(0);
lean_ctor_set(x_334, 0, x_361);
x_42 = x_334;
goto block_53;
}
else
{
uint8_t x_362; lean_object* x_363; 
lean_free_object(x_334);
x_362 = 0;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_363 = l_Lean_Elab_Tactic_rewriteTarget(x_64, x_362, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_350, x_16, x_339);
x_42 = x_363;
goto block_53;
}
}
else
{
size_t x_364; size_t x_365; uint8_t x_366; lean_object* x_367; lean_object* x_368; 
lean_free_object(x_334);
x_364 = 0;
x_365 = lean_usize_of_nat(x_355);
lean_dec(x_355);
x_366 = 0;
x_367 = lean_box(0);
lean_inc(x_16);
lean_inc(x_350);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_64);
x_368 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalRewriteCore___spec__1(x_1, x_64, x_366, x_353, x_364, x_365, x_367, x_9, x_10, x_11, x_12, x_13, x_14, x_350, x_16, x_339);
if (lean_obj_tag(x_368) == 0)
{
if (x_354 == 0)
{
uint8_t x_369; 
lean_dec(x_350);
lean_dec(x_64);
x_369 = !lean_is_exclusive(x_368);
if (x_369 == 0)
{
lean_object* x_370; 
x_370 = lean_ctor_get(x_368, 0);
lean_dec(x_370);
lean_ctor_set(x_368, 0, x_367);
x_42 = x_368;
goto block_53;
}
else
{
lean_object* x_371; lean_object* x_372; 
x_371 = lean_ctor_get(x_368, 1);
lean_inc(x_371);
lean_dec(x_368);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_367);
lean_ctor_set(x_372, 1, x_371);
x_42 = x_372;
goto block_53;
}
}
else
{
lean_object* x_373; lean_object* x_374; 
x_373 = lean_ctor_get(x_368, 1);
lean_inc(x_373);
lean_dec(x_368);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_374 = l_Lean_Elab_Tactic_rewriteTarget(x_64, x_366, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_350, x_16, x_373);
x_42 = x_374;
goto block_53;
}
}
else
{
uint8_t x_375; 
lean_dec(x_350);
lean_dec(x_64);
x_375 = !lean_is_exclusive(x_368);
if (x_375 == 0)
{
x_42 = x_368;
goto block_53;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_368, 0);
x_377 = lean_ctor_get(x_368, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_368);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
x_42 = x_378;
goto block_53;
}
}
}
}
}
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_379 = lean_ctor_get(x_334, 1);
lean_inc(x_379);
lean_dec(x_334);
x_380 = lean_ctor_get(x_15, 0);
x_381 = lean_ctor_get(x_15, 1);
x_382 = lean_ctor_get(x_15, 2);
x_383 = lean_ctor_get(x_15, 3);
x_384 = lean_ctor_get(x_15, 4);
x_385 = lean_ctor_get(x_15, 5);
x_386 = lean_ctor_get(x_15, 6);
x_387 = lean_ctor_get(x_15, 7);
x_388 = l_Lean_replaceRef(x_57, x_383);
lean_dec(x_57);
lean_inc(x_387);
lean_inc(x_386);
lean_inc(x_385);
lean_inc(x_384);
lean_inc(x_382);
lean_inc(x_381);
lean_inc(x_380);
x_389 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_389, 0, x_380);
lean_ctor_set(x_389, 1, x_381);
lean_ctor_set(x_389, 2, x_382);
lean_ctor_set(x_389, 3, x_388);
lean_ctor_set(x_389, 4, x_384);
lean_ctor_set(x_389, 5, x_385);
lean_ctor_set(x_389, 6, x_386);
lean_ctor_set(x_389, 7, x_387);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_390; lean_object* x_391; 
x_390 = 0;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_391 = l_Lean_Elab_Tactic_rewriteAll(x_64, x_390, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_389, x_16, x_379);
x_42 = x_391;
goto block_53;
}
else
{
lean_object* x_392; uint8_t x_393; lean_object* x_394; uint8_t x_395; 
x_392 = lean_ctor_get(x_3, 0);
x_393 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_394 = lean_array_get_size(x_392);
x_395 = lean_nat_dec_lt(x_20, x_394);
if (x_395 == 0)
{
lean_dec(x_394);
if (x_393 == 0)
{
lean_object* x_396; lean_object* x_397; 
lean_dec(x_389);
lean_dec(x_64);
x_396 = lean_box(0);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_396);
lean_ctor_set(x_397, 1, x_379);
x_42 = x_397;
goto block_53;
}
else
{
uint8_t x_398; lean_object* x_399; 
x_398 = 0;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_399 = l_Lean_Elab_Tactic_rewriteTarget(x_64, x_398, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_389, x_16, x_379);
x_42 = x_399;
goto block_53;
}
}
else
{
uint8_t x_400; 
x_400 = lean_nat_dec_le(x_394, x_394);
if (x_400 == 0)
{
lean_dec(x_394);
if (x_393 == 0)
{
lean_object* x_401; lean_object* x_402; 
lean_dec(x_389);
lean_dec(x_64);
x_401 = lean_box(0);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_379);
x_42 = x_402;
goto block_53;
}
else
{
uint8_t x_403; lean_object* x_404; 
x_403 = 0;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_404 = l_Lean_Elab_Tactic_rewriteTarget(x_64, x_403, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_389, x_16, x_379);
x_42 = x_404;
goto block_53;
}
}
else
{
size_t x_405; size_t x_406; uint8_t x_407; lean_object* x_408; lean_object* x_409; 
x_405 = 0;
x_406 = lean_usize_of_nat(x_394);
lean_dec(x_394);
x_407 = 0;
x_408 = lean_box(0);
lean_inc(x_16);
lean_inc(x_389);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_64);
x_409 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalRewriteCore___spec__1(x_1, x_64, x_407, x_392, x_405, x_406, x_408, x_9, x_10, x_11, x_12, x_13, x_14, x_389, x_16, x_379);
if (lean_obj_tag(x_409) == 0)
{
if (x_393 == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_389);
lean_dec(x_64);
x_410 = lean_ctor_get(x_409, 1);
lean_inc(x_410);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_411 = x_409;
} else {
 lean_dec_ref(x_409);
 x_411 = lean_box(0);
}
if (lean_is_scalar(x_411)) {
 x_412 = lean_alloc_ctor(0, 2, 0);
} else {
 x_412 = x_411;
}
lean_ctor_set(x_412, 0, x_408);
lean_ctor_set(x_412, 1, x_410);
x_42 = x_412;
goto block_53;
}
else
{
lean_object* x_413; lean_object* x_414; 
x_413 = lean_ctor_get(x_409, 1);
lean_inc(x_413);
lean_dec(x_409);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_414 = l_Lean_Elab_Tactic_rewriteTarget(x_64, x_407, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_389, x_16, x_413);
x_42 = x_414;
goto block_53;
}
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
lean_dec(x_389);
lean_dec(x_64);
x_415 = lean_ctor_get(x_409, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_409, 1);
lean_inc(x_416);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_417 = x_409;
} else {
 lean_dec_ref(x_409);
 x_417 = lean_box(0);
}
if (lean_is_scalar(x_417)) {
 x_418 = lean_alloc_ctor(1, 2, 0);
} else {
 x_418 = x_417;
}
lean_ctor_set(x_418, 0, x_415);
lean_ctor_set(x_418, 1, x_416);
x_42 = x_418;
goto block_53;
}
}
}
}
}
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_476; lean_object* x_477; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_419 = lean_ctor_get(x_334, 1);
lean_inc(x_419);
lean_dec(x_334);
x_420 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg(x_12, x_13, x_14, x_15, x_16, x_419);
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
x_529 = lean_ctor_get(x_15, 0);
x_530 = lean_ctor_get(x_15, 1);
x_531 = lean_ctor_get(x_15, 2);
x_532 = lean_ctor_get(x_15, 3);
x_533 = lean_ctor_get(x_15, 4);
x_534 = lean_ctor_get(x_15, 5);
x_535 = lean_ctor_get(x_15, 6);
x_536 = lean_ctor_get(x_15, 7);
x_537 = l_Lean_replaceRef(x_57, x_532);
lean_dec(x_57);
lean_inc(x_536);
lean_inc(x_535);
lean_inc(x_534);
lean_inc(x_533);
lean_inc(x_531);
lean_inc(x_530);
lean_inc(x_529);
x_538 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_538, 0, x_529);
lean_ctor_set(x_538, 1, x_530);
lean_ctor_set(x_538, 2, x_531);
lean_ctor_set(x_538, 3, x_537);
lean_ctor_set(x_538, 4, x_533);
lean_ctor_set(x_538, 5, x_534);
lean_ctor_set(x_538, 6, x_535);
lean_ctor_set(x_538, 7, x_536);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_539; lean_object* x_540; 
x_539 = 0;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_540 = l_Lean_Elab_Tactic_rewriteAll(x_64, x_539, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_538, x_16, x_422);
if (lean_obj_tag(x_540) == 0)
{
lean_object* x_541; lean_object* x_542; 
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_540, 1);
lean_inc(x_542);
lean_dec(x_540);
x_423 = x_541;
x_424 = x_542;
goto block_475;
}
else
{
lean_object* x_543; lean_object* x_544; 
x_543 = lean_ctor_get(x_540, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_540, 1);
lean_inc(x_544);
lean_dec(x_540);
x_476 = x_543;
x_477 = x_544;
goto block_528;
}
}
else
{
lean_object* x_545; uint8_t x_546; lean_object* x_547; uint8_t x_548; 
x_545 = lean_ctor_get(x_3, 0);
x_546 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
x_547 = lean_array_get_size(x_545);
x_548 = lean_nat_dec_lt(x_20, x_547);
if (x_548 == 0)
{
lean_dec(x_547);
if (x_546 == 0)
{
lean_object* x_549; 
lean_dec(x_538);
lean_dec(x_64);
x_549 = lean_box(0);
x_423 = x_549;
x_424 = x_422;
goto block_475;
}
else
{
uint8_t x_550; lean_object* x_551; 
x_550 = 0;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_551 = l_Lean_Elab_Tactic_rewriteTarget(x_64, x_550, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_538, x_16, x_422);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; lean_object* x_553; 
x_552 = lean_ctor_get(x_551, 0);
lean_inc(x_552);
x_553 = lean_ctor_get(x_551, 1);
lean_inc(x_553);
lean_dec(x_551);
x_423 = x_552;
x_424 = x_553;
goto block_475;
}
else
{
lean_object* x_554; lean_object* x_555; 
x_554 = lean_ctor_get(x_551, 0);
lean_inc(x_554);
x_555 = lean_ctor_get(x_551, 1);
lean_inc(x_555);
lean_dec(x_551);
x_476 = x_554;
x_477 = x_555;
goto block_528;
}
}
}
else
{
uint8_t x_556; 
x_556 = lean_nat_dec_le(x_547, x_547);
if (x_556 == 0)
{
lean_dec(x_547);
if (x_546 == 0)
{
lean_object* x_557; 
lean_dec(x_538);
lean_dec(x_64);
x_557 = lean_box(0);
x_423 = x_557;
x_424 = x_422;
goto block_475;
}
else
{
uint8_t x_558; lean_object* x_559; 
x_558 = 0;
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_559 = l_Lean_Elab_Tactic_rewriteTarget(x_64, x_558, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_538, x_16, x_422);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; 
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_559, 1);
lean_inc(x_561);
lean_dec(x_559);
x_423 = x_560;
x_424 = x_561;
goto block_475;
}
else
{
lean_object* x_562; lean_object* x_563; 
x_562 = lean_ctor_get(x_559, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_559, 1);
lean_inc(x_563);
lean_dec(x_559);
x_476 = x_562;
x_477 = x_563;
goto block_528;
}
}
}
else
{
size_t x_564; size_t x_565; uint8_t x_566; lean_object* x_567; lean_object* x_568; 
x_564 = 0;
x_565 = lean_usize_of_nat(x_547);
lean_dec(x_547);
x_566 = 0;
x_567 = lean_box(0);
lean_inc(x_16);
lean_inc(x_538);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_64);
x_568 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalRewriteCore___spec__2(x_1, x_64, x_566, x_545, x_564, x_565, x_567, x_9, x_10, x_11, x_12, x_13, x_14, x_538, x_16, x_422);
if (lean_obj_tag(x_568) == 0)
{
if (x_546 == 0)
{
lean_object* x_569; 
lean_dec(x_538);
lean_dec(x_64);
x_569 = lean_ctor_get(x_568, 1);
lean_inc(x_569);
lean_dec(x_568);
x_423 = x_567;
x_424 = x_569;
goto block_475;
}
else
{
lean_object* x_570; lean_object* x_571; 
x_570 = lean_ctor_get(x_568, 1);
lean_inc(x_570);
lean_dec(x_568);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_571 = l_Lean_Elab_Tactic_rewriteTarget(x_64, x_566, x_1, x_9, x_10, x_11, x_12, x_13, x_14, x_538, x_16, x_570);
if (lean_obj_tag(x_571) == 0)
{
lean_object* x_572; lean_object* x_573; 
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_571, 1);
lean_inc(x_573);
lean_dec(x_571);
x_423 = x_572;
x_424 = x_573;
goto block_475;
}
else
{
lean_object* x_574; lean_object* x_575; 
x_574 = lean_ctor_get(x_571, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_571, 1);
lean_inc(x_575);
lean_dec(x_571);
x_476 = x_574;
x_477 = x_575;
goto block_528;
}
}
}
else
{
lean_object* x_576; lean_object* x_577; 
lean_dec(x_538);
lean_dec(x_64);
x_576 = lean_ctor_get(x_568, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_568, 1);
lean_inc(x_577);
lean_dec(x_568);
x_476 = x_576;
x_477 = x_577;
goto block_528;
}
}
}
}
block_475:
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; 
x_425 = lean_st_ref_get(x_16, x_424);
x_426 = lean_ctor_get(x_425, 1);
lean_inc(x_426);
lean_dec(x_425);
x_427 = lean_st_ref_get(x_12, x_426);
x_428 = lean_ctor_get(x_427, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec(x_427);
x_430 = lean_ctor_get(x_428, 5);
lean_inc(x_430);
lean_dec(x_428);
x_431 = lean_ctor_get(x_430, 1);
lean_inc(x_431);
lean_dec(x_430);
x_432 = l_Lean_Elab_Tactic_mkTacticInfo(x_328, x_330, x_69, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_429);
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
lean_dec(x_432);
x_435 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_435, 0, x_433);
lean_ctor_set(x_435, 1, x_431);
x_436 = lean_st_ref_get(x_16, x_434);
x_437 = lean_ctor_get(x_436, 1);
lean_inc(x_437);
lean_dec(x_436);
x_438 = lean_st_ref_take(x_12, x_437);
x_439 = lean_ctor_get(x_438, 0);
lean_inc(x_439);
x_440 = lean_ctor_get(x_439, 5);
lean_inc(x_440);
x_441 = lean_ctor_get(x_438, 1);
lean_inc(x_441);
lean_dec(x_438);
x_442 = !lean_is_exclusive(x_439);
if (x_442 == 0)
{
lean_object* x_443; uint8_t x_444; 
x_443 = lean_ctor_get(x_439, 5);
lean_dec(x_443);
x_444 = !lean_is_exclusive(x_440);
if (x_444 == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; uint8_t x_448; 
x_445 = lean_ctor_get(x_440, 1);
lean_dec(x_445);
x_446 = l_Std_PersistentArray_push___rarg(x_421, x_435);
lean_ctor_set(x_440, 1, x_446);
x_447 = lean_st_ref_set(x_12, x_439, x_441);
x_448 = !lean_is_exclusive(x_447);
if (x_448 == 0)
{
lean_object* x_449; 
x_449 = lean_ctor_get(x_447, 0);
lean_dec(x_449);
lean_ctor_set(x_447, 0, x_423);
x_42 = x_447;
goto block_53;
}
else
{
lean_object* x_450; lean_object* x_451; 
x_450 = lean_ctor_get(x_447, 1);
lean_inc(x_450);
lean_dec(x_447);
x_451 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_451, 0, x_423);
lean_ctor_set(x_451, 1, x_450);
x_42 = x_451;
goto block_53;
}
}
else
{
uint8_t x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_452 = lean_ctor_get_uint8(x_440, sizeof(void*)*2);
x_453 = lean_ctor_get(x_440, 0);
lean_inc(x_453);
lean_dec(x_440);
x_454 = l_Std_PersistentArray_push___rarg(x_421, x_435);
x_455 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_455, 0, x_453);
lean_ctor_set(x_455, 1, x_454);
lean_ctor_set_uint8(x_455, sizeof(void*)*2, x_452);
lean_ctor_set(x_439, 5, x_455);
x_456 = lean_st_ref_set(x_12, x_439, x_441);
x_457 = lean_ctor_get(x_456, 1);
lean_inc(x_457);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 lean_ctor_release(x_456, 1);
 x_458 = x_456;
} else {
 lean_dec_ref(x_456);
 x_458 = lean_box(0);
}
if (lean_is_scalar(x_458)) {
 x_459 = lean_alloc_ctor(0, 2, 0);
} else {
 x_459 = x_458;
}
lean_ctor_set(x_459, 0, x_423);
lean_ctor_set(x_459, 1, x_457);
x_42 = x_459;
goto block_53;
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_460 = lean_ctor_get(x_439, 0);
x_461 = lean_ctor_get(x_439, 1);
x_462 = lean_ctor_get(x_439, 2);
x_463 = lean_ctor_get(x_439, 3);
x_464 = lean_ctor_get(x_439, 4);
lean_inc(x_464);
lean_inc(x_463);
lean_inc(x_462);
lean_inc(x_461);
lean_inc(x_460);
lean_dec(x_439);
x_465 = lean_ctor_get_uint8(x_440, sizeof(void*)*2);
x_466 = lean_ctor_get(x_440, 0);
lean_inc(x_466);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_467 = x_440;
} else {
 lean_dec_ref(x_440);
 x_467 = lean_box(0);
}
x_468 = l_Std_PersistentArray_push___rarg(x_421, x_435);
if (lean_is_scalar(x_467)) {
 x_469 = lean_alloc_ctor(0, 2, 1);
} else {
 x_469 = x_467;
}
lean_ctor_set(x_469, 0, x_466);
lean_ctor_set(x_469, 1, x_468);
lean_ctor_set_uint8(x_469, sizeof(void*)*2, x_465);
x_470 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_470, 0, x_460);
lean_ctor_set(x_470, 1, x_461);
lean_ctor_set(x_470, 2, x_462);
lean_ctor_set(x_470, 3, x_463);
lean_ctor_set(x_470, 4, x_464);
lean_ctor_set(x_470, 5, x_469);
x_471 = lean_st_ref_set(x_12, x_470, x_441);
x_472 = lean_ctor_get(x_471, 1);
lean_inc(x_472);
if (lean_is_exclusive(x_471)) {
 lean_ctor_release(x_471, 0);
 lean_ctor_release(x_471, 1);
 x_473 = x_471;
} else {
 lean_dec_ref(x_471);
 x_473 = lean_box(0);
}
if (lean_is_scalar(x_473)) {
 x_474 = lean_alloc_ctor(0, 2, 0);
} else {
 x_474 = x_473;
}
lean_ctor_set(x_474, 0, x_423);
lean_ctor_set(x_474, 1, x_472);
x_42 = x_474;
goto block_53;
}
}
block_528:
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; uint8_t x_495; 
x_478 = lean_st_ref_get(x_16, x_477);
x_479 = lean_ctor_get(x_478, 1);
lean_inc(x_479);
lean_dec(x_478);
x_480 = lean_st_ref_get(x_12, x_479);
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_480, 1);
lean_inc(x_482);
lean_dec(x_480);
x_483 = lean_ctor_get(x_481, 5);
lean_inc(x_483);
lean_dec(x_481);
x_484 = lean_ctor_get(x_483, 1);
lean_inc(x_484);
lean_dec(x_483);
x_485 = l_Lean_Elab_Tactic_mkTacticInfo(x_328, x_330, x_69, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_482);
x_486 = lean_ctor_get(x_485, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_485, 1);
lean_inc(x_487);
lean_dec(x_485);
x_488 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_484);
x_489 = lean_st_ref_get(x_16, x_487);
x_490 = lean_ctor_get(x_489, 1);
lean_inc(x_490);
lean_dec(x_489);
x_491 = lean_st_ref_take(x_12, x_490);
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
x_493 = lean_ctor_get(x_492, 5);
lean_inc(x_493);
x_494 = lean_ctor_get(x_491, 1);
lean_inc(x_494);
lean_dec(x_491);
x_495 = !lean_is_exclusive(x_492);
if (x_495 == 0)
{
lean_object* x_496; uint8_t x_497; 
x_496 = lean_ctor_get(x_492, 5);
lean_dec(x_496);
x_497 = !lean_is_exclusive(x_493);
if (x_497 == 0)
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; uint8_t x_501; 
x_498 = lean_ctor_get(x_493, 1);
lean_dec(x_498);
x_499 = l_Std_PersistentArray_push___rarg(x_421, x_488);
lean_ctor_set(x_493, 1, x_499);
x_500 = lean_st_ref_set(x_12, x_492, x_494);
x_501 = !lean_is_exclusive(x_500);
if (x_501 == 0)
{
lean_object* x_502; 
x_502 = lean_ctor_get(x_500, 0);
lean_dec(x_502);
lean_ctor_set_tag(x_500, 1);
lean_ctor_set(x_500, 0, x_476);
x_42 = x_500;
goto block_53;
}
else
{
lean_object* x_503; lean_object* x_504; 
x_503 = lean_ctor_get(x_500, 1);
lean_inc(x_503);
lean_dec(x_500);
x_504 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_504, 0, x_476);
lean_ctor_set(x_504, 1, x_503);
x_42 = x_504;
goto block_53;
}
}
else
{
uint8_t x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_505 = lean_ctor_get_uint8(x_493, sizeof(void*)*2);
x_506 = lean_ctor_get(x_493, 0);
lean_inc(x_506);
lean_dec(x_493);
x_507 = l_Std_PersistentArray_push___rarg(x_421, x_488);
x_508 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_508, 0, x_506);
lean_ctor_set(x_508, 1, x_507);
lean_ctor_set_uint8(x_508, sizeof(void*)*2, x_505);
lean_ctor_set(x_492, 5, x_508);
x_509 = lean_st_ref_set(x_12, x_492, x_494);
x_510 = lean_ctor_get(x_509, 1);
lean_inc(x_510);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 x_511 = x_509;
} else {
 lean_dec_ref(x_509);
 x_511 = lean_box(0);
}
if (lean_is_scalar(x_511)) {
 x_512 = lean_alloc_ctor(1, 2, 0);
} else {
 x_512 = x_511;
 lean_ctor_set_tag(x_512, 1);
}
lean_ctor_set(x_512, 0, x_476);
lean_ctor_set(x_512, 1, x_510);
x_42 = x_512;
goto block_53;
}
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; uint8_t x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_513 = lean_ctor_get(x_492, 0);
x_514 = lean_ctor_get(x_492, 1);
x_515 = lean_ctor_get(x_492, 2);
x_516 = lean_ctor_get(x_492, 3);
x_517 = lean_ctor_get(x_492, 4);
lean_inc(x_517);
lean_inc(x_516);
lean_inc(x_515);
lean_inc(x_514);
lean_inc(x_513);
lean_dec(x_492);
x_518 = lean_ctor_get_uint8(x_493, sizeof(void*)*2);
x_519 = lean_ctor_get(x_493, 0);
lean_inc(x_519);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 lean_ctor_release(x_493, 1);
 x_520 = x_493;
} else {
 lean_dec_ref(x_493);
 x_520 = lean_box(0);
}
x_521 = l_Std_PersistentArray_push___rarg(x_421, x_488);
if (lean_is_scalar(x_520)) {
 x_522 = lean_alloc_ctor(0, 2, 1);
} else {
 x_522 = x_520;
}
lean_ctor_set(x_522, 0, x_519);
lean_ctor_set(x_522, 1, x_521);
lean_ctor_set_uint8(x_522, sizeof(void*)*2, x_518);
x_523 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_523, 0, x_513);
lean_ctor_set(x_523, 1, x_514);
lean_ctor_set(x_523, 2, x_515);
lean_ctor_set(x_523, 3, x_516);
lean_ctor_set(x_523, 4, x_517);
lean_ctor_set(x_523, 5, x_522);
x_524 = lean_st_ref_set(x_12, x_523, x_494);
x_525 = lean_ctor_get(x_524, 1);
lean_inc(x_525);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 x_526 = x_524;
} else {
 lean_dec_ref(x_524);
 x_526 = lean_box(0);
}
if (lean_is_scalar(x_526)) {
 x_527 = lean_alloc_ctor(1, 2, 0);
} else {
 x_527 = x_526;
 lean_ctor_set_tag(x_527, 1);
}
lean_ctor_set(x_527, 0, x_476);
lean_ctor_set(x_527, 1, x_525);
x_42 = x_527;
goto block_53;
}
}
}
}
}
}
else
{
lean_object* x_581; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_581 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_581, 0, x_8);
lean_ctor_set(x_581, 1, x_17);
return x_581;
}
}
else
{
lean_object* x_582; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
x_582 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_582, 0, x_8);
lean_ctor_set(x_582, 1, x_17);
return x_582;
}
}
}
lean_object* l_Lean_Elab_Tactic_evalRewriteCore(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_2, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = l_Lean_Syntax_getArg(x_2, x_14);
x_16 = l_Lean_Syntax_getArg(x_15, x_12);
x_17 = l_Lean_Syntax_getArg(x_15, x_14);
lean_dec(x_15);
x_18 = l_Lean_Syntax_getArgs(x_17);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Syntax_getArg(x_2, x_19);
x_21 = l_Lean_Elab_Tactic_expandOptLocation(x_20);
lean_dec(x_20);
x_39 = l_Lean_Syntax_mkApp___closed__1;
x_40 = lean_array_push(x_39, x_13);
x_41 = lean_array_push(x_40, x_16);
x_42 = l_Lean_nullKind;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_st_ref_get(x_10, x_11);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_st_ref_get(x_8, x_45);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_47, 0);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Elab_Tactic_getGoals___rarg(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_48);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_st_ref_get(x_10, x_52);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_st_ref_get(x_6, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 5);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_ctor_get_uint8(x_57, sizeof(void*)*2);
lean_dec(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_43);
x_59 = !lean_is_exclusive(x_55);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_55, 0);
lean_dec(x_60);
x_61 = lean_box(0);
lean_ctor_set(x_55, 0, x_61);
x_22 = x_55;
goto block_38;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_dec(x_55);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
x_22 = x_64;
goto block_38;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_65 = lean_ctor_get(x_55, 1);
lean_inc(x_65);
lean_dec(x_55);
x_66 = l___private_Lean_Elab_InfoTree_0__Lean_Elab_getResetInfoTrees___at_Lean_Elab_Tactic_withTacticInfoContext___spec__1___rarg(x_6, x_7, x_8, x_9, x_10, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_st_ref_get(x_10, x_68);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_st_ref_get(x_6, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_ctor_get(x_72, 5);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_Lean_Elab_Tactic_mkTacticInfo(x_49, x_51, x_43, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_73);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_75);
x_80 = lean_st_ref_get(x_10, x_78);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_st_ref_take(x_6, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_83, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = !lean_is_exclusive(x_83);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_83, 5);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_84);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_89 = lean_ctor_get(x_84, 1);
lean_dec(x_89);
x_90 = l_Std_PersistentArray_push___rarg(x_67, x_79);
lean_ctor_set(x_84, 1, x_90);
x_91 = lean_st_ref_set(x_6, x_83, x_85);
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
lean_dec(x_93);
x_94 = lean_box(0);
lean_ctor_set(x_91, 0, x_94);
x_22 = x_91;
goto block_38;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
lean_dec(x_91);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
x_22 = x_97;
goto block_38;
}
}
else
{
uint8_t x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_98 = lean_ctor_get_uint8(x_84, sizeof(void*)*2);
x_99 = lean_ctor_get(x_84, 0);
lean_inc(x_99);
lean_dec(x_84);
x_100 = l_Std_PersistentArray_push___rarg(x_67, x_79);
x_101 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set_uint8(x_101, sizeof(void*)*2, x_98);
lean_ctor_set(x_83, 5, x_101);
x_102 = lean_st_ref_set(x_6, x_83, x_85);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_box(0);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
x_22 = x_106;
goto block_38;
}
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_107 = lean_ctor_get(x_83, 0);
x_108 = lean_ctor_get(x_83, 1);
x_109 = lean_ctor_get(x_83, 2);
x_110 = lean_ctor_get(x_83, 3);
x_111 = lean_ctor_get(x_83, 4);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_83);
x_112 = lean_ctor_get_uint8(x_84, sizeof(void*)*2);
x_113 = lean_ctor_get(x_84, 0);
lean_inc(x_113);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_114 = x_84;
} else {
 lean_dec_ref(x_84);
 x_114 = lean_box(0);
}
x_115 = l_Std_PersistentArray_push___rarg(x_67, x_79);
if (lean_is_scalar(x_114)) {
 x_116 = lean_alloc_ctor(0, 2, 1);
} else {
 x_116 = x_114;
}
lean_ctor_set(x_116, 0, x_113);
lean_ctor_set(x_116, 1, x_115);
lean_ctor_set_uint8(x_116, sizeof(void*)*2, x_112);
x_117 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_117, 0, x_107);
lean_ctor_set(x_117, 1, x_108);
lean_ctor_set(x_117, 2, x_109);
lean_ctor_set(x_117, 3, x_110);
lean_ctor_set(x_117, 4, x_111);
lean_ctor_set(x_117, 5, x_116);
x_118 = lean_st_ref_set(x_6, x_117, x_85);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_118)) {
 lean_ctor_release(x_118, 0);
 lean_ctor_release(x_118, 1);
 x_120 = x_118;
} else {
 lean_dec_ref(x_118);
 x_120 = lean_box(0);
}
x_121 = lean_box(0);
if (lean_is_scalar(x_120)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_120;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_119);
x_22 = x_122;
goto block_38;
}
}
block_38:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = lean_array_get_size(x_18);
x_25 = lean_nat_add(x_24, x_14);
x_26 = lean_nat_div(x_25, x_19);
lean_dec(x_25);
lean_inc(x_26);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_14);
x_28 = lean_box(0);
x_29 = l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalRewriteCore___spec__3(x_1, x_18, x_21, x_24, x_27, x_26, x_12, x_28, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_23);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_18);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_29, 0);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_29);
if (x_34 == 0)
{
return x_29;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_29, 0);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_29);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalRewriteCore___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_unbox(x_1);
lean_dec(x_1);
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_20 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_21 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalRewriteCore___spec__1(x_17, x_2, x_18, x_4, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
return x_21;
}
}
lean_object* l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalRewriteCore___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_unbox(x_1);
lean_dec(x_1);
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_20 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_21 = l_Array_foldlMUnsafe_fold___at_Lean_Elab_Tactic_evalRewriteCore___spec__2(x_17, x_2, x_18, x_4, x_19, x_20, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_4);
return x_21;
}
}
lean_object* l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalRewriteCore___spec__3___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_18; lean_object* x_19; 
x_18 = lean_unbox(x_1);
lean_dec(x_1);
x_19 = l_Std_Range_forIn_loop___at_Lean_Elab_Tactic_evalRewriteCore___spec__3(x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_19;
}
}
lean_object* l_Lean_Elab_Tactic_evalRewriteCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_Elab_Tactic_evalRewriteCore(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_2);
return x_13;
}
}
lean_object* l_Lean_Elab_Tactic_evalRewriteSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 3;
x_12 = l_Lean_Elab_Tactic_evalRewriteCore(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_evalRewriteSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalRewriteSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalRewriteSeq___boxed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_rewriteSeq___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* l_Lean_Elab_Tactic_evalERewriteSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = 1;
x_12 = l_Lean_Elab_Tactic_evalRewriteCore(x_11, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
lean_object* l_Lean_Elab_Tactic_evalERewriteSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalERewriteSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___regBuiltin_Lean_Elab_Tactic_evalERewriteSeq___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalERewriteSeq___boxed), 10, 0);
return x_1;
}
}
lean_object* l___regBuiltin_Lean_Elab_Tactic_evalERewriteSeq(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = l_Lean_Parser_Tactic_erewriteSeq___closed__2;
x_4 = l___regBuiltin_Lean_Elab_Tactic_evalERewriteSeq___closed__1;
x_5 = l_Lean_KeyedDeclsAttribute_addBuiltin___rarg(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Rewrite(lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Replace(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Basic(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_ElabTerm(lean_object*);
lean_object* initialize_Lean_Elab_Tactic_Location(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Elab_Tactic_Rewrite(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Rewrite(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Replace(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Basic(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_ElabTerm(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Location(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_rewriteAll___lambda__1___closed__1 = _init_l_Lean_Elab_Tactic_rewriteAll___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Tactic_rewriteAll___lambda__1___closed__1);
l_Lean_Elab_Tactic_rewriteAll___lambda__1___closed__2 = _init_l_Lean_Elab_Tactic_rewriteAll___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Tactic_rewriteAll___lambda__1___closed__2);
l_Lean_Elab_Tactic_rewriteAll___lambda__1___closed__3 = _init_l_Lean_Elab_Tactic_rewriteAll___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Tactic_rewriteAll___lambda__1___closed__3);
l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalRewriteSeq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___regBuiltin_Lean_Elab_Tactic_evalERewriteSeq___closed__1 = _init_l___regBuiltin_Lean_Elab_Tactic_evalERewriteSeq___closed__1();
lean_mark_persistent(l___regBuiltin_Lean_Elab_Tactic_evalERewriteSeq___closed__1);
res = l___regBuiltin_Lean_Elab_Tactic_evalERewriteSeq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
