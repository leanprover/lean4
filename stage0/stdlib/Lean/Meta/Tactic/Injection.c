// Lean compiler output
// Module: Lean.Meta.Tactic.Injection
// Imports: Lean.Meta.AppBuilder Lean.Meta.MatchUtil Lean.Meta.Tactic.Clear Lean.Meta.Tactic.Subst Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Intro
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
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__16;
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at_Lean_Meta_injections_go___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEqHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__10;
static lean_object* l_Lean_Meta_injectionCore___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__17;
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__1;
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__6;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__5;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__6;
lean_object* l_outOfBounds___rarg(lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__12;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_getCtorNumPropFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__4;
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__5;
lean_object* l_Lean_Meta_saveState___rarg(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__7;
static lean_object* l_Lean_Meta_injectionIntro___closed__1;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__1;
static lean_object* l_Lean_Meta_injectionCore___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__15;
lean_object* l_Lean_Meta_heqToEq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injections_go___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__3;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static uint64_t l_Lean_Meta_injectionCore___lambda__1___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__9;
lean_object* l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_getCtorNumPropFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__4;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__14;
static lean_object* l_Lean_Meta_injections_go___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_injections_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_getCtorNumPropFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_nat_dec_lt(x_6, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_1, 3);
x_25 = lean_nat_add(x_24, x_6);
x_26 = lean_array_get_size(x_2);
x_27 = lean_nat_dec_lt(x_25, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
x_28 = l_Lean_instInhabitedExpr;
x_29 = l_outOfBounds___rarg(x_28);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_30 = lean_infer_type(x_29, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_33 = l_Lean_Meta_isProp(x_31, x_9, x_10, x_11, x_12, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
lean_dec(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_5);
x_17 = x_37;
x_18 = x_36;
goto block_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_add(x_5, x_39);
lean_dec(x_5);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_17 = x_41;
x_18 = x_38;
goto block_23;
}
}
else
{
uint8_t x_42; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_42 = !lean_is_exclusive(x_33);
if (x_42 == 0)
{
return x_33;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_33, 0);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_33);
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
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_30);
if (x_46 == 0)
{
return x_30;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_30, 0);
x_48 = lean_ctor_get(x_30, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_30);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_array_fget(x_2, x_25);
lean_dec(x_25);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_51 = lean_infer_type(x_50, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_54 = l_Lean_Meta_isProp(x_52, x_9, x_10, x_11, x_12, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_5);
x_17 = x_58;
x_18 = x_57;
goto block_23;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_dec(x_54);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_5, x_60);
lean_dec(x_5);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_17 = x_62;
x_18 = x_59;
goto block_23;
}
}
else
{
uint8_t x_63; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_63 = !lean_is_exclusive(x_54);
if (x_63 == 0)
{
return x_54;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_54, 0);
x_65 = lean_ctor_get(x_54, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_54);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_67 = !lean_is_exclusive(x_51);
if (x_67 == 0)
{
return x_51;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_51, 0);
x_69 = lean_ctor_get(x_51, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_51);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
block_23:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_4, 2);
x_21 = lean_nat_add(x_6, x_20);
lean_dec(x_6);
x_5 = x_19;
x_6 = x_21;
x_7 = lean_box(0);
x_8 = lean_box(0);
x_13 = x_18;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 4);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_getCtorNumPropFields___spec__1(x_1, x_2, x_12, x_12, x_10, x_10, lean_box(0), lean_box(0), x_4, x_5, x_6, x_7, x_8);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_getCtorNumPropFields___lambda__1___boxed), 8, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = 0;
x_11 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_8, x_9, x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_getCtorNumPropFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_getCtorNumPropFields___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getCtorNumPropFields___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("HEq", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_injectionCore___lambda__1___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_injectionCore___lambda__1___closed__3;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("equality expected", 17, 17);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__6;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__7;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("equality of constructor applications expected", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__9;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__10;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__11;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static uint64_t _init_l_Lean_Meta_injectionCore___lambda__1___closed__13() {
_start:
{
uint8_t x_1; uint64_t x_2; 
x_1 = 1;
x_2 = l_Lean_Meta_TransparencyMode_toUInt64(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ill-formed noConfusion auxiliary construction", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__14;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__15;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__16;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_FVarId_getDecl(x_3, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_LocalDecl_type(x_12);
lean_dec(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = lean_whnf(x_14, x_4, x_5, x_6, x_7, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_3);
x_18 = l_Lean_Expr_fvar___override(x_3);
x_19 = l_Lean_Meta_injectionCore___lambda__1___closed__2;
x_20 = lean_unsigned_to_nat(4u);
x_21 = l_Lean_Expr_isAppOfArity(x_16, x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_Lean_Meta_injectionCore___lambda__1___closed__4;
x_23 = lean_unsigned_to_nat(3u);
x_24 = l_Lean_Expr_isAppOfArity(x_16, x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_3);
x_25 = l_Lean_Meta_injectionCore___lambda__1___closed__8;
x_26 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_25, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = l_Lean_Expr_appFn_x21(x_16);
x_28 = l_Lean_Expr_appArg_x21(x_27);
lean_dec(x_27);
x_29 = l_Lean_Expr_appArg_x21(x_16);
lean_dec(x_16);
lean_inc(x_1);
x_30 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_33 = l_Lean_Meta_isConstructorApp_x27_x3f(x_28, x_4, x_5, x_6, x_7, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_36 = l_Lean_Meta_isConstructorApp_x27_x3f(x_29, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_36) == 0)
{
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_31);
lean_dec(x_18);
lean_dec(x_3);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_39 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_38, x_4, x_5, x_6, x_7, x_37);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_39;
}
else
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_36, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_18);
lean_dec(x_3);
x_41 = lean_ctor_get(x_36, 1);
lean_inc(x_41);
lean_dec(x_36);
x_42 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_43 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_42, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_44 = lean_ctor_get(x_4, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_ctor_get(x_34, 0);
lean_inc(x_46);
lean_dec(x_34);
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
lean_dec(x_40);
x_48 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_49 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_50 = lean_ctor_get(x_4, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_4, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_4, 3);
lean_inc(x_52);
x_53 = lean_ctor_get(x_4, 4);
lean_inc(x_53);
x_54 = lean_ctor_get(x_4, 5);
lean_inc(x_54);
x_55 = lean_ctor_get(x_4, 6);
lean_inc(x_55);
x_56 = !lean_is_exclusive(x_44);
if (x_56 == 0)
{
uint8_t x_57; uint8_t x_58; uint8_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; lean_object* x_65; lean_object* x_66; 
x_57 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_58 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
x_59 = 1;
lean_ctor_set_uint8(x_44, 9, x_59);
x_60 = 2;
x_61 = lean_uint64_shift_right(x_48, x_60);
x_62 = lean_uint64_shift_left(x_61, x_60);
x_63 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_64 = lean_uint64_lor(x_62, x_63);
x_65 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_65, 0, x_44);
lean_ctor_set(x_65, 1, x_50);
lean_ctor_set(x_65, 2, x_51);
lean_ctor_set(x_65, 3, x_52);
lean_ctor_set(x_65, 4, x_53);
lean_ctor_set(x_65, 5, x_54);
lean_ctor_set(x_65, 6, x_55);
lean_ctor_set_uint64(x_65, sizeof(void*)*7, x_64);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 8, x_49);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 9, x_57);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 10, x_58);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_66 = l_Lean_Meta_mkNoConfusion(x_31, x_18, x_65, x_5, x_6, x_7, x_45);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_46, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_ctor_get(x_47, 0);
lean_inc(x_71);
lean_dec(x_47);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_name_eq(x_70, x_72);
lean_dec(x_72);
lean_dec(x_70);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
lean_dec(x_46);
lean_dec(x_3);
lean_dec(x_2);
x_74 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_67, x_4, x_5, x_6, x_7, x_68);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_74, 0);
lean_dec(x_76);
x_77 = lean_box(0);
lean_ctor_set(x_74, 0, x_77);
return x_74;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
lean_dec(x_74);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
else
{
lean_object* x_81; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_67);
x_81 = lean_infer_type(x_67, x_4, x_5, x_6, x_7, x_68);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_84 = l_Lean_Meta_whnfD(x_82, x_4, x_5, x_6, x_7, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 7)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_2);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Expr_headBeta(x_87);
lean_inc(x_1);
x_89 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_86);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_4);
x_92 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_88, x_90, x_4, x_5, x_6, x_7, x_91);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
lean_inc(x_93);
x_95 = l_Lean_Expr_app___override(x_67, x_93);
x_96 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_95, x_4, x_5, x_6, x_7, x_94);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_96, 1);
x_99 = lean_ctor_get(x_96, 0);
lean_dec(x_99);
x_100 = l_Lean_Expr_mvarId_x21(x_93);
lean_dec(x_93);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_101 = l_Lean_MVarId_tryClear(x_100, x_3, x_4, x_5, x_6, x_7, x_98);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_46);
x_104 = l_Lean_Meta_getCtorNumPropFields(x_46, x_4, x_5, x_6, x_7, x_103);
if (lean_obj_tag(x_104) == 0)
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_104, 0);
x_107 = lean_ctor_get(x_46, 4);
lean_inc(x_107);
lean_dec(x_46);
x_108 = lean_nat_sub(x_107, x_106);
lean_dec(x_106);
lean_dec(x_107);
lean_ctor_set_tag(x_96, 1);
lean_ctor_set(x_96, 1, x_108);
lean_ctor_set(x_96, 0, x_102);
lean_ctor_set(x_104, 0, x_96);
return x_104;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_109 = lean_ctor_get(x_104, 0);
x_110 = lean_ctor_get(x_104, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_104);
x_111 = lean_ctor_get(x_46, 4);
lean_inc(x_111);
lean_dec(x_46);
x_112 = lean_nat_sub(x_111, x_109);
lean_dec(x_109);
lean_dec(x_111);
lean_ctor_set_tag(x_96, 1);
lean_ctor_set(x_96, 1, x_112);
lean_ctor_set(x_96, 0, x_102);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_96);
lean_ctor_set(x_113, 1, x_110);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_102);
lean_free_object(x_96);
lean_dec(x_46);
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
else
{
uint8_t x_118; 
lean_free_object(x_96);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_118 = !lean_is_exclusive(x_101);
if (x_118 == 0)
{
return x_101;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_101, 0);
x_120 = lean_ctor_get(x_101, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_101);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_96, 1);
lean_inc(x_122);
lean_dec(x_96);
x_123 = l_Lean_Expr_mvarId_x21(x_93);
lean_dec(x_93);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_124 = l_Lean_MVarId_tryClear(x_123, x_3, x_4, x_5, x_6, x_7, x_122);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
lean_inc(x_46);
x_127 = l_Lean_Meta_getCtorNumPropFields(x_46, x_4, x_5, x_6, x_7, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_130 = x_127;
} else {
 lean_dec_ref(x_127);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_46, 4);
lean_inc(x_131);
lean_dec(x_46);
x_132 = lean_nat_sub(x_131, x_128);
lean_dec(x_128);
lean_dec(x_131);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_125);
lean_ctor_set(x_133, 1, x_132);
if (lean_is_scalar(x_130)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_130;
}
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_129);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_125);
lean_dec(x_46);
x_135 = lean_ctor_get(x_127, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_127, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_127)) {
 lean_ctor_release(x_127, 0);
 lean_ctor_release(x_127, 1);
 x_137 = x_127;
} else {
 lean_dec_ref(x_127);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_139 = lean_ctor_get(x_124, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_124, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_141 = x_124;
} else {
 lean_dec_ref(x_124);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_88);
lean_dec(x_67);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_89);
if (x_143 == 0)
{
return x_89;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_89, 0);
x_145 = lean_ctor_get(x_89, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_89);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_dec(x_85);
lean_dec(x_67);
lean_dec(x_46);
lean_dec(x_3);
x_147 = lean_ctor_get(x_84, 1);
lean_inc(x_147);
lean_dec(x_84);
x_148 = l_Lean_Meta_injectionCore___lambda__1___closed__17;
x_149 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_148, x_4, x_5, x_6, x_7, x_147);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_149;
}
}
else
{
uint8_t x_150; 
lean_dec(x_67);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_84);
if (x_150 == 0)
{
return x_84;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_84, 0);
x_152 = lean_ctor_get(x_84, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_84);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_67);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_154 = !lean_is_exclusive(x_81);
if (x_154 == 0)
{
return x_81;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_81, 0);
x_156 = lean_ctor_get(x_81, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_81);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
}
else
{
uint8_t x_158; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_158 = !lean_is_exclusive(x_66);
if (x_158 == 0)
{
return x_66;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_66, 0);
x_160 = lean_ctor_get(x_66, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_66);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
else
{
uint8_t x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; uint8_t x_180; lean_object* x_181; uint64_t x_182; uint64_t x_183; uint64_t x_184; uint64_t x_185; uint64_t x_186; lean_object* x_187; lean_object* x_188; 
x_162 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_163 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
x_164 = lean_ctor_get_uint8(x_44, 0);
x_165 = lean_ctor_get_uint8(x_44, 1);
x_166 = lean_ctor_get_uint8(x_44, 2);
x_167 = lean_ctor_get_uint8(x_44, 3);
x_168 = lean_ctor_get_uint8(x_44, 4);
x_169 = lean_ctor_get_uint8(x_44, 5);
x_170 = lean_ctor_get_uint8(x_44, 6);
x_171 = lean_ctor_get_uint8(x_44, 7);
x_172 = lean_ctor_get_uint8(x_44, 8);
x_173 = lean_ctor_get_uint8(x_44, 10);
x_174 = lean_ctor_get_uint8(x_44, 11);
x_175 = lean_ctor_get_uint8(x_44, 12);
x_176 = lean_ctor_get_uint8(x_44, 13);
x_177 = lean_ctor_get_uint8(x_44, 14);
x_178 = lean_ctor_get_uint8(x_44, 15);
x_179 = lean_ctor_get_uint8(x_44, 16);
lean_dec(x_44);
x_180 = 1;
x_181 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_181, 0, x_164);
lean_ctor_set_uint8(x_181, 1, x_165);
lean_ctor_set_uint8(x_181, 2, x_166);
lean_ctor_set_uint8(x_181, 3, x_167);
lean_ctor_set_uint8(x_181, 4, x_168);
lean_ctor_set_uint8(x_181, 5, x_169);
lean_ctor_set_uint8(x_181, 6, x_170);
lean_ctor_set_uint8(x_181, 7, x_171);
lean_ctor_set_uint8(x_181, 8, x_172);
lean_ctor_set_uint8(x_181, 9, x_180);
lean_ctor_set_uint8(x_181, 10, x_173);
lean_ctor_set_uint8(x_181, 11, x_174);
lean_ctor_set_uint8(x_181, 12, x_175);
lean_ctor_set_uint8(x_181, 13, x_176);
lean_ctor_set_uint8(x_181, 14, x_177);
lean_ctor_set_uint8(x_181, 15, x_178);
lean_ctor_set_uint8(x_181, 16, x_179);
x_182 = 2;
x_183 = lean_uint64_shift_right(x_48, x_182);
x_184 = lean_uint64_shift_left(x_183, x_182);
x_185 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_186 = lean_uint64_lor(x_184, x_185);
x_187 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_187, 0, x_181);
lean_ctor_set(x_187, 1, x_50);
lean_ctor_set(x_187, 2, x_51);
lean_ctor_set(x_187, 3, x_52);
lean_ctor_set(x_187, 4, x_53);
lean_ctor_set(x_187, 5, x_54);
lean_ctor_set(x_187, 6, x_55);
lean_ctor_set_uint64(x_187, sizeof(void*)*7, x_186);
lean_ctor_set_uint8(x_187, sizeof(void*)*7 + 8, x_49);
lean_ctor_set_uint8(x_187, sizeof(void*)*7 + 9, x_162);
lean_ctor_set_uint8(x_187, sizeof(void*)*7 + 10, x_163);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_188 = l_Lean_Meta_mkNoConfusion(x_31, x_18, x_187, x_5, x_6, x_7, x_45);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = lean_ctor_get(x_46, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
lean_dec(x_191);
x_193 = lean_ctor_get(x_47, 0);
lean_inc(x_193);
lean_dec(x_47);
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
lean_dec(x_193);
x_195 = lean_name_eq(x_192, x_194);
lean_dec(x_194);
lean_dec(x_192);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_46);
lean_dec(x_3);
lean_dec(x_2);
x_196 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_189, x_4, x_5, x_6, x_7, x_190);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_198 = x_196;
} else {
 lean_dec_ref(x_196);
 x_198 = lean_box(0);
}
x_199 = lean_box(0);
if (lean_is_scalar(x_198)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_198;
}
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_197);
return x_200;
}
else
{
lean_object* x_201; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_189);
x_201 = lean_infer_type(x_189, x_4, x_5, x_6, x_7, x_190);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_204 = l_Lean_Meta_whnfD(x_202, x_4, x_5, x_6, x_7, x_203);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
if (lean_obj_tag(x_205) == 7)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_2);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
lean_dec(x_205);
x_208 = l_Lean_Expr_headBeta(x_207);
lean_inc(x_1);
x_209 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_206);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
lean_inc(x_4);
x_212 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_208, x_210, x_4, x_5, x_6, x_7, x_211);
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
lean_dec(x_212);
lean_inc(x_213);
x_215 = l_Lean_Expr_app___override(x_189, x_213);
x_216 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_215, x_4, x_5, x_6, x_7, x_214);
x_217 = lean_ctor_get(x_216, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_218 = x_216;
} else {
 lean_dec_ref(x_216);
 x_218 = lean_box(0);
}
x_219 = l_Lean_Expr_mvarId_x21(x_213);
lean_dec(x_213);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_220 = l_Lean_MVarId_tryClear(x_219, x_3, x_4, x_5, x_6, x_7, x_217);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
lean_inc(x_46);
x_223 = l_Lean_Meta_getCtorNumPropFields(x_46, x_4, x_5, x_6, x_7, x_222);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_226 = x_223;
} else {
 lean_dec_ref(x_223);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_46, 4);
lean_inc(x_227);
lean_dec(x_46);
x_228 = lean_nat_sub(x_227, x_224);
lean_dec(x_224);
lean_dec(x_227);
if (lean_is_scalar(x_218)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_218;
 lean_ctor_set_tag(x_229, 1);
}
lean_ctor_set(x_229, 0, x_221);
lean_ctor_set(x_229, 1, x_228);
if (lean_is_scalar(x_226)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_226;
}
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_230, 1, x_225);
return x_230;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_221);
lean_dec(x_218);
lean_dec(x_46);
x_231 = lean_ctor_get(x_223, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_223, 1);
lean_inc(x_232);
if (lean_is_exclusive(x_223)) {
 lean_ctor_release(x_223, 0);
 lean_ctor_release(x_223, 1);
 x_233 = x_223;
} else {
 lean_dec_ref(x_223);
 x_233 = lean_box(0);
}
if (lean_is_scalar(x_233)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_233;
}
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_218);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_235 = lean_ctor_get(x_220, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_220, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_237 = x_220;
} else {
 lean_dec_ref(x_220);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(1, 2, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_236);
return x_238;
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_208);
lean_dec(x_189);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_239 = lean_ctor_get(x_209, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_209, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_241 = x_209;
} else {
 lean_dec_ref(x_209);
 x_241 = lean_box(0);
}
if (lean_is_scalar(x_241)) {
 x_242 = lean_alloc_ctor(1, 2, 0);
} else {
 x_242 = x_241;
}
lean_ctor_set(x_242, 0, x_239);
lean_ctor_set(x_242, 1, x_240);
return x_242;
}
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_205);
lean_dec(x_189);
lean_dec(x_46);
lean_dec(x_3);
x_243 = lean_ctor_get(x_204, 1);
lean_inc(x_243);
lean_dec(x_204);
x_244 = l_Lean_Meta_injectionCore___lambda__1___closed__17;
x_245 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_244, x_4, x_5, x_6, x_7, x_243);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_189);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_246 = lean_ctor_get(x_204, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_204, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_248 = x_204;
} else {
 lean_dec_ref(x_204);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
lean_dec(x_189);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_250 = lean_ctor_get(x_201, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_201, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_252 = x_201;
} else {
 lean_dec_ref(x_201);
 x_252 = lean_box(0);
}
if (lean_is_scalar(x_252)) {
 x_253 = lean_alloc_ctor(1, 2, 0);
} else {
 x_253 = x_252;
}
lean_ctor_set(x_253, 0, x_250);
lean_ctor_set(x_253, 1, x_251);
return x_253;
}
}
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_254 = lean_ctor_get(x_188, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_188, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_256 = x_188;
} else {
 lean_dec_ref(x_188);
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
}
}
}
else
{
uint8_t x_258; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_258 = !lean_is_exclusive(x_36);
if (x_258 == 0)
{
return x_36;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_36, 0);
x_260 = lean_ctor_get(x_36, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_36);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
else
{
uint8_t x_262; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_262 = !lean_is_exclusive(x_33);
if (x_262 == 0)
{
return x_33;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_33, 0);
x_264 = lean_ctor_get(x_33, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_33);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
else
{
uint8_t x_266; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_266 = !lean_is_exclusive(x_30);
if (x_266 == 0)
{
return x_30;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_30, 0);
x_268 = lean_ctor_get(x_30, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_30);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_270 = l_Lean_Expr_appFn_x21(x_16);
x_271 = l_Lean_Expr_appFn_x21(x_270);
x_272 = l_Lean_Expr_appFn_x21(x_271);
x_273 = l_Lean_Expr_appArg_x21(x_272);
lean_dec(x_272);
x_274 = l_Lean_Expr_appArg_x21(x_271);
lean_dec(x_271);
x_275 = l_Lean_Expr_appArg_x21(x_270);
lean_dec(x_270);
x_276 = l_Lean_Expr_appArg_x21(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_275);
x_277 = l_Lean_Meta_isExprDefEq(x_273, x_275, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; uint8_t x_279; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_unbox(x_278);
lean_dec(x_278);
if (x_279 == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
lean_dec(x_274);
x_280 = lean_ctor_get(x_277, 1);
lean_inc(x_280);
lean_dec(x_277);
x_281 = l_Lean_Meta_injectionCore___lambda__1___closed__4;
x_282 = lean_unsigned_to_nat(3u);
x_283 = l_Lean_Expr_isAppOfArity(x_16, x_281, x_282);
lean_dec(x_16);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; 
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_18);
lean_dec(x_3);
x_284 = l_Lean_Meta_injectionCore___lambda__1___closed__8;
x_285 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_284, x_4, x_5, x_6, x_7, x_280);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_285;
}
else
{
lean_object* x_286; 
lean_inc(x_1);
x_286 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_280);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_289 = l_Lean_Meta_isConstructorApp_x27_x3f(x_275, x_4, x_5, x_6, x_7, x_288);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
lean_dec(x_289);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_292 = l_Lean_Meta_isConstructorApp_x27_x3f(x_276, x_4, x_5, x_6, x_7, x_291);
if (lean_obj_tag(x_292) == 0)
{
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_287);
lean_dec(x_18);
lean_dec(x_3);
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
lean_dec(x_292);
x_294 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_295 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_294, x_4, x_5, x_6, x_7, x_293);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_295;
}
else
{
lean_object* x_296; 
x_296 = lean_ctor_get(x_292, 0);
lean_inc(x_296);
if (lean_obj_tag(x_296) == 0)
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_290);
lean_dec(x_287);
lean_dec(x_18);
lean_dec(x_3);
x_297 = lean_ctor_get(x_292, 1);
lean_inc(x_297);
lean_dec(x_292);
x_298 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_299 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_298, x_4, x_5, x_6, x_7, x_297);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_299;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint64_t x_304; uint8_t x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_300 = lean_ctor_get(x_4, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_292, 1);
lean_inc(x_301);
lean_dec(x_292);
x_302 = lean_ctor_get(x_290, 0);
lean_inc(x_302);
lean_dec(x_290);
x_303 = lean_ctor_get(x_296, 0);
lean_inc(x_303);
lean_dec(x_296);
x_304 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_305 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_306 = lean_ctor_get(x_4, 1);
lean_inc(x_306);
x_307 = lean_ctor_get(x_4, 2);
lean_inc(x_307);
x_308 = lean_ctor_get(x_4, 3);
lean_inc(x_308);
x_309 = lean_ctor_get(x_4, 4);
lean_inc(x_309);
x_310 = lean_ctor_get(x_4, 5);
lean_inc(x_310);
x_311 = lean_ctor_get(x_4, 6);
lean_inc(x_311);
x_312 = !lean_is_exclusive(x_300);
if (x_312 == 0)
{
uint8_t x_313; uint8_t x_314; uint8_t x_315; uint64_t x_316; uint64_t x_317; uint64_t x_318; uint64_t x_319; uint64_t x_320; lean_object* x_321; lean_object* x_322; 
x_313 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_314 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
x_315 = 1;
lean_ctor_set_uint8(x_300, 9, x_315);
x_316 = 2;
x_317 = lean_uint64_shift_right(x_304, x_316);
x_318 = lean_uint64_shift_left(x_317, x_316);
x_319 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_320 = lean_uint64_lor(x_318, x_319);
x_321 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_321, 0, x_300);
lean_ctor_set(x_321, 1, x_306);
lean_ctor_set(x_321, 2, x_307);
lean_ctor_set(x_321, 3, x_308);
lean_ctor_set(x_321, 4, x_309);
lean_ctor_set(x_321, 5, x_310);
lean_ctor_set(x_321, 6, x_311);
lean_ctor_set_uint64(x_321, sizeof(void*)*7, x_320);
lean_ctor_set_uint8(x_321, sizeof(void*)*7 + 8, x_305);
lean_ctor_set_uint8(x_321, sizeof(void*)*7 + 9, x_313);
lean_ctor_set_uint8(x_321, sizeof(void*)*7 + 10, x_314);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_322 = l_Lean_Meta_mkNoConfusion(x_287, x_18, x_321, x_5, x_6, x_7, x_301);
if (lean_obj_tag(x_322) == 0)
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; 
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
x_324 = lean_ctor_get(x_322, 1);
lean_inc(x_324);
lean_dec(x_322);
x_325 = lean_ctor_get(x_302, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
lean_dec(x_325);
x_327 = lean_ctor_get(x_303, 0);
lean_inc(x_327);
lean_dec(x_303);
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
lean_dec(x_327);
x_329 = lean_name_eq(x_326, x_328);
lean_dec(x_328);
lean_dec(x_326);
if (x_329 == 0)
{
lean_object* x_330; uint8_t x_331; 
lean_dec(x_302);
lean_dec(x_3);
lean_dec(x_2);
x_330 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_323, x_4, x_5, x_6, x_7, x_324);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_331 = !lean_is_exclusive(x_330);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; 
x_332 = lean_ctor_get(x_330, 0);
lean_dec(x_332);
x_333 = lean_box(0);
lean_ctor_set(x_330, 0, x_333);
return x_330;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_330, 1);
lean_inc(x_334);
lean_dec(x_330);
x_335 = lean_box(0);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_334);
return x_336;
}
}
else
{
lean_object* x_337; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_323);
x_337 = lean_infer_type(x_323, x_4, x_5, x_6, x_7, x_324);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_340 = l_Lean_Meta_whnfD(x_338, x_4, x_5, x_6, x_7, x_339);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; 
x_341 = lean_ctor_get(x_340, 0);
lean_inc(x_341);
if (lean_obj_tag(x_341) == 7)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
lean_dec(x_2);
x_342 = lean_ctor_get(x_340, 1);
lean_inc(x_342);
lean_dec(x_340);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec(x_341);
x_344 = l_Lean_Expr_headBeta(x_343);
lean_inc(x_1);
x_345 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_342);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; uint8_t x_353; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
lean_inc(x_4);
x_348 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_344, x_346, x_4, x_5, x_6, x_7, x_347);
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
lean_inc(x_349);
x_351 = l_Lean_Expr_app___override(x_323, x_349);
x_352 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_351, x_4, x_5, x_6, x_7, x_350);
x_353 = !lean_is_exclusive(x_352);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_354 = lean_ctor_get(x_352, 1);
x_355 = lean_ctor_get(x_352, 0);
lean_dec(x_355);
x_356 = l_Lean_Expr_mvarId_x21(x_349);
lean_dec(x_349);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_357 = l_Lean_MVarId_tryClear(x_356, x_3, x_4, x_5, x_6, x_7, x_354);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
lean_inc(x_302);
x_360 = l_Lean_Meta_getCtorNumPropFields(x_302, x_4, x_5, x_6, x_7, x_359);
if (lean_obj_tag(x_360) == 0)
{
uint8_t x_361; 
x_361 = !lean_is_exclusive(x_360);
if (x_361 == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_360, 0);
x_363 = lean_ctor_get(x_302, 4);
lean_inc(x_363);
lean_dec(x_302);
x_364 = lean_nat_sub(x_363, x_362);
lean_dec(x_362);
lean_dec(x_363);
lean_ctor_set_tag(x_352, 1);
lean_ctor_set(x_352, 1, x_364);
lean_ctor_set(x_352, 0, x_358);
lean_ctor_set(x_360, 0, x_352);
return x_360;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_365 = lean_ctor_get(x_360, 0);
x_366 = lean_ctor_get(x_360, 1);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_360);
x_367 = lean_ctor_get(x_302, 4);
lean_inc(x_367);
lean_dec(x_302);
x_368 = lean_nat_sub(x_367, x_365);
lean_dec(x_365);
lean_dec(x_367);
lean_ctor_set_tag(x_352, 1);
lean_ctor_set(x_352, 1, x_368);
lean_ctor_set(x_352, 0, x_358);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_352);
lean_ctor_set(x_369, 1, x_366);
return x_369;
}
}
else
{
uint8_t x_370; 
lean_dec(x_358);
lean_free_object(x_352);
lean_dec(x_302);
x_370 = !lean_is_exclusive(x_360);
if (x_370 == 0)
{
return x_360;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_360, 0);
x_372 = lean_ctor_get(x_360, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_360);
x_373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
return x_373;
}
}
}
else
{
uint8_t x_374; 
lean_free_object(x_352);
lean_dec(x_302);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_374 = !lean_is_exclusive(x_357);
if (x_374 == 0)
{
return x_357;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_357, 0);
x_376 = lean_ctor_get(x_357, 1);
lean_inc(x_376);
lean_inc(x_375);
lean_dec(x_357);
x_377 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set(x_377, 1, x_376);
return x_377;
}
}
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_352, 1);
lean_inc(x_378);
lean_dec(x_352);
x_379 = l_Lean_Expr_mvarId_x21(x_349);
lean_dec(x_349);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_380 = l_Lean_MVarId_tryClear(x_379, x_3, x_4, x_5, x_6, x_7, x_378);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
lean_dec(x_380);
lean_inc(x_302);
x_383 = l_Lean_Meta_getCtorNumPropFields(x_302, x_4, x_5, x_6, x_7, x_382);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; 
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_386 = x_383;
} else {
 lean_dec_ref(x_383);
 x_386 = lean_box(0);
}
x_387 = lean_ctor_get(x_302, 4);
lean_inc(x_387);
lean_dec(x_302);
x_388 = lean_nat_sub(x_387, x_384);
lean_dec(x_384);
lean_dec(x_387);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_381);
lean_ctor_set(x_389, 1, x_388);
if (lean_is_scalar(x_386)) {
 x_390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_390 = x_386;
}
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_385);
return x_390;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_dec(x_381);
lean_dec(x_302);
x_391 = lean_ctor_get(x_383, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_383, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_393 = x_383;
} else {
 lean_dec_ref(x_383);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(1, 2, 0);
} else {
 x_394 = x_393;
}
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_392);
return x_394;
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_302);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_395 = lean_ctor_get(x_380, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_380, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_397 = x_380;
} else {
 lean_dec_ref(x_380);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(1, 2, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_396);
return x_398;
}
}
}
else
{
uint8_t x_399; 
lean_dec(x_344);
lean_dec(x_323);
lean_dec(x_302);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_399 = !lean_is_exclusive(x_345);
if (x_399 == 0)
{
return x_345;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_345, 0);
x_401 = lean_ctor_get(x_345, 1);
lean_inc(x_401);
lean_inc(x_400);
lean_dec(x_345);
x_402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_402, 0, x_400);
lean_ctor_set(x_402, 1, x_401);
return x_402;
}
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_341);
lean_dec(x_323);
lean_dec(x_302);
lean_dec(x_3);
x_403 = lean_ctor_get(x_340, 1);
lean_inc(x_403);
lean_dec(x_340);
x_404 = l_Lean_Meta_injectionCore___lambda__1___closed__17;
x_405 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_404, x_4, x_5, x_6, x_7, x_403);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_405;
}
}
else
{
uint8_t x_406; 
lean_dec(x_323);
lean_dec(x_302);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_406 = !lean_is_exclusive(x_340);
if (x_406 == 0)
{
return x_340;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_407 = lean_ctor_get(x_340, 0);
x_408 = lean_ctor_get(x_340, 1);
lean_inc(x_408);
lean_inc(x_407);
lean_dec(x_340);
x_409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
return x_409;
}
}
}
else
{
uint8_t x_410; 
lean_dec(x_323);
lean_dec(x_302);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_410 = !lean_is_exclusive(x_337);
if (x_410 == 0)
{
return x_337;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_411 = lean_ctor_get(x_337, 0);
x_412 = lean_ctor_get(x_337, 1);
lean_inc(x_412);
lean_inc(x_411);
lean_dec(x_337);
x_413 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
return x_413;
}
}
}
}
else
{
uint8_t x_414; 
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_414 = !lean_is_exclusive(x_322);
if (x_414 == 0)
{
return x_322;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_322, 0);
x_416 = lean_ctor_get(x_322, 1);
lean_inc(x_416);
lean_inc(x_415);
lean_dec(x_322);
x_417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
return x_417;
}
}
}
else
{
uint8_t x_418; uint8_t x_419; uint8_t x_420; uint8_t x_421; uint8_t x_422; uint8_t x_423; uint8_t x_424; uint8_t x_425; uint8_t x_426; uint8_t x_427; uint8_t x_428; uint8_t x_429; uint8_t x_430; uint8_t x_431; uint8_t x_432; uint8_t x_433; uint8_t x_434; uint8_t x_435; uint8_t x_436; lean_object* x_437; uint64_t x_438; uint64_t x_439; uint64_t x_440; uint64_t x_441; uint64_t x_442; lean_object* x_443; lean_object* x_444; 
x_418 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_419 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
x_420 = lean_ctor_get_uint8(x_300, 0);
x_421 = lean_ctor_get_uint8(x_300, 1);
x_422 = lean_ctor_get_uint8(x_300, 2);
x_423 = lean_ctor_get_uint8(x_300, 3);
x_424 = lean_ctor_get_uint8(x_300, 4);
x_425 = lean_ctor_get_uint8(x_300, 5);
x_426 = lean_ctor_get_uint8(x_300, 6);
x_427 = lean_ctor_get_uint8(x_300, 7);
x_428 = lean_ctor_get_uint8(x_300, 8);
x_429 = lean_ctor_get_uint8(x_300, 10);
x_430 = lean_ctor_get_uint8(x_300, 11);
x_431 = lean_ctor_get_uint8(x_300, 12);
x_432 = lean_ctor_get_uint8(x_300, 13);
x_433 = lean_ctor_get_uint8(x_300, 14);
x_434 = lean_ctor_get_uint8(x_300, 15);
x_435 = lean_ctor_get_uint8(x_300, 16);
lean_dec(x_300);
x_436 = 1;
x_437 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_437, 0, x_420);
lean_ctor_set_uint8(x_437, 1, x_421);
lean_ctor_set_uint8(x_437, 2, x_422);
lean_ctor_set_uint8(x_437, 3, x_423);
lean_ctor_set_uint8(x_437, 4, x_424);
lean_ctor_set_uint8(x_437, 5, x_425);
lean_ctor_set_uint8(x_437, 6, x_426);
lean_ctor_set_uint8(x_437, 7, x_427);
lean_ctor_set_uint8(x_437, 8, x_428);
lean_ctor_set_uint8(x_437, 9, x_436);
lean_ctor_set_uint8(x_437, 10, x_429);
lean_ctor_set_uint8(x_437, 11, x_430);
lean_ctor_set_uint8(x_437, 12, x_431);
lean_ctor_set_uint8(x_437, 13, x_432);
lean_ctor_set_uint8(x_437, 14, x_433);
lean_ctor_set_uint8(x_437, 15, x_434);
lean_ctor_set_uint8(x_437, 16, x_435);
x_438 = 2;
x_439 = lean_uint64_shift_right(x_304, x_438);
x_440 = lean_uint64_shift_left(x_439, x_438);
x_441 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_442 = lean_uint64_lor(x_440, x_441);
x_443 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_443, 0, x_437);
lean_ctor_set(x_443, 1, x_306);
lean_ctor_set(x_443, 2, x_307);
lean_ctor_set(x_443, 3, x_308);
lean_ctor_set(x_443, 4, x_309);
lean_ctor_set(x_443, 5, x_310);
lean_ctor_set(x_443, 6, x_311);
lean_ctor_set_uint64(x_443, sizeof(void*)*7, x_442);
lean_ctor_set_uint8(x_443, sizeof(void*)*7 + 8, x_305);
lean_ctor_set_uint8(x_443, sizeof(void*)*7 + 9, x_418);
lean_ctor_set_uint8(x_443, sizeof(void*)*7 + 10, x_419);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_444 = l_Lean_Meta_mkNoConfusion(x_287, x_18, x_443, x_5, x_6, x_7, x_301);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; uint8_t x_451; 
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_444, 1);
lean_inc(x_446);
lean_dec(x_444);
x_447 = lean_ctor_get(x_302, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
lean_dec(x_447);
x_449 = lean_ctor_get(x_303, 0);
lean_inc(x_449);
lean_dec(x_303);
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
lean_dec(x_449);
x_451 = lean_name_eq(x_448, x_450);
lean_dec(x_450);
lean_dec(x_448);
if (x_451 == 0)
{
lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
lean_dec(x_302);
lean_dec(x_3);
lean_dec(x_2);
x_452 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_445, x_4, x_5, x_6, x_7, x_446);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_453 = lean_ctor_get(x_452, 1);
lean_inc(x_453);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 x_454 = x_452;
} else {
 lean_dec_ref(x_452);
 x_454 = lean_box(0);
}
x_455 = lean_box(0);
if (lean_is_scalar(x_454)) {
 x_456 = lean_alloc_ctor(0, 2, 0);
} else {
 x_456 = x_454;
}
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_453);
return x_456;
}
else
{
lean_object* x_457; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_445);
x_457 = lean_infer_type(x_445, x_4, x_5, x_6, x_7, x_446);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_457, 1);
lean_inc(x_459);
lean_dec(x_457);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_460 = l_Lean_Meta_whnfD(x_458, x_4, x_5, x_6, x_7, x_459);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; 
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
if (lean_obj_tag(x_461) == 7)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_2);
x_462 = lean_ctor_get(x_460, 1);
lean_inc(x_462);
lean_dec(x_460);
x_463 = lean_ctor_get(x_461, 1);
lean_inc(x_463);
lean_dec(x_461);
x_464 = l_Lean_Expr_headBeta(x_463);
lean_inc(x_1);
x_465 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_462);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
lean_dec(x_465);
lean_inc(x_4);
x_468 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_464, x_466, x_4, x_5, x_6, x_7, x_467);
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_468, 1);
lean_inc(x_470);
lean_dec(x_468);
lean_inc(x_469);
x_471 = l_Lean_Expr_app___override(x_445, x_469);
x_472 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_471, x_4, x_5, x_6, x_7, x_470);
x_473 = lean_ctor_get(x_472, 1);
lean_inc(x_473);
if (lean_is_exclusive(x_472)) {
 lean_ctor_release(x_472, 0);
 lean_ctor_release(x_472, 1);
 x_474 = x_472;
} else {
 lean_dec_ref(x_472);
 x_474 = lean_box(0);
}
x_475 = l_Lean_Expr_mvarId_x21(x_469);
lean_dec(x_469);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_476 = l_Lean_MVarId_tryClear(x_475, x_3, x_4, x_5, x_6, x_7, x_473);
if (lean_obj_tag(x_476) == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_477 = lean_ctor_get(x_476, 0);
lean_inc(x_477);
x_478 = lean_ctor_get(x_476, 1);
lean_inc(x_478);
lean_dec(x_476);
lean_inc(x_302);
x_479 = l_Lean_Meta_getCtorNumPropFields(x_302, x_4, x_5, x_6, x_7, x_478);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_479, 1);
lean_inc(x_481);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 lean_ctor_release(x_479, 1);
 x_482 = x_479;
} else {
 lean_dec_ref(x_479);
 x_482 = lean_box(0);
}
x_483 = lean_ctor_get(x_302, 4);
lean_inc(x_483);
lean_dec(x_302);
x_484 = lean_nat_sub(x_483, x_480);
lean_dec(x_480);
lean_dec(x_483);
if (lean_is_scalar(x_474)) {
 x_485 = lean_alloc_ctor(1, 2, 0);
} else {
 x_485 = x_474;
 lean_ctor_set_tag(x_485, 1);
}
lean_ctor_set(x_485, 0, x_477);
lean_ctor_set(x_485, 1, x_484);
if (lean_is_scalar(x_482)) {
 x_486 = lean_alloc_ctor(0, 2, 0);
} else {
 x_486 = x_482;
}
lean_ctor_set(x_486, 0, x_485);
lean_ctor_set(x_486, 1, x_481);
return x_486;
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
lean_dec(x_477);
lean_dec(x_474);
lean_dec(x_302);
x_487 = lean_ctor_get(x_479, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_479, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_479)) {
 lean_ctor_release(x_479, 0);
 lean_ctor_release(x_479, 1);
 x_489 = x_479;
} else {
 lean_dec_ref(x_479);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(1, 2, 0);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_488);
return x_490;
}
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_474);
lean_dec(x_302);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_491 = lean_ctor_get(x_476, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_476, 1);
lean_inc(x_492);
if (lean_is_exclusive(x_476)) {
 lean_ctor_release(x_476, 0);
 lean_ctor_release(x_476, 1);
 x_493 = x_476;
} else {
 lean_dec_ref(x_476);
 x_493 = lean_box(0);
}
if (lean_is_scalar(x_493)) {
 x_494 = lean_alloc_ctor(1, 2, 0);
} else {
 x_494 = x_493;
}
lean_ctor_set(x_494, 0, x_491);
lean_ctor_set(x_494, 1, x_492);
return x_494;
}
}
else
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; 
lean_dec(x_464);
lean_dec(x_445);
lean_dec(x_302);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_495 = lean_ctor_get(x_465, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_465, 1);
lean_inc(x_496);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_497 = x_465;
} else {
 lean_dec_ref(x_465);
 x_497 = lean_box(0);
}
if (lean_is_scalar(x_497)) {
 x_498 = lean_alloc_ctor(1, 2, 0);
} else {
 x_498 = x_497;
}
lean_ctor_set(x_498, 0, x_495);
lean_ctor_set(x_498, 1, x_496);
return x_498;
}
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; 
lean_dec(x_461);
lean_dec(x_445);
lean_dec(x_302);
lean_dec(x_3);
x_499 = lean_ctor_get(x_460, 1);
lean_inc(x_499);
lean_dec(x_460);
x_500 = l_Lean_Meta_injectionCore___lambda__1___closed__17;
x_501 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_500, x_4, x_5, x_6, x_7, x_499);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_501;
}
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
lean_dec(x_445);
lean_dec(x_302);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_502 = lean_ctor_get(x_460, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_460, 1);
lean_inc(x_503);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 x_504 = x_460;
} else {
 lean_dec_ref(x_460);
 x_504 = lean_box(0);
}
if (lean_is_scalar(x_504)) {
 x_505 = lean_alloc_ctor(1, 2, 0);
} else {
 x_505 = x_504;
}
lean_ctor_set(x_505, 0, x_502);
lean_ctor_set(x_505, 1, x_503);
return x_505;
}
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
lean_dec(x_445);
lean_dec(x_302);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_506 = lean_ctor_get(x_457, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_457, 1);
lean_inc(x_507);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 lean_ctor_release(x_457, 1);
 x_508 = x_457;
} else {
 lean_dec_ref(x_457);
 x_508 = lean_box(0);
}
if (lean_is_scalar(x_508)) {
 x_509 = lean_alloc_ctor(1, 2, 0);
} else {
 x_509 = x_508;
}
lean_ctor_set(x_509, 0, x_506);
lean_ctor_set(x_509, 1, x_507);
return x_509;
}
}
}
else
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_510 = lean_ctor_get(x_444, 0);
lean_inc(x_510);
x_511 = lean_ctor_get(x_444, 1);
lean_inc(x_511);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_512 = x_444;
} else {
 lean_dec_ref(x_444);
 x_512 = lean_box(0);
}
if (lean_is_scalar(x_512)) {
 x_513 = lean_alloc_ctor(1, 2, 0);
} else {
 x_513 = x_512;
}
lean_ctor_set(x_513, 0, x_510);
lean_ctor_set(x_513, 1, x_511);
return x_513;
}
}
}
}
}
else
{
uint8_t x_514; 
lean_dec(x_290);
lean_dec(x_287);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_514 = !lean_is_exclusive(x_292);
if (x_514 == 0)
{
return x_292;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_515 = lean_ctor_get(x_292, 0);
x_516 = lean_ctor_get(x_292, 1);
lean_inc(x_516);
lean_inc(x_515);
lean_dec(x_292);
x_517 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_517, 0, x_515);
lean_ctor_set(x_517, 1, x_516);
return x_517;
}
}
}
else
{
uint8_t x_518; 
lean_dec(x_287);
lean_dec(x_276);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_518 = !lean_is_exclusive(x_289);
if (x_518 == 0)
{
return x_289;
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_519 = lean_ctor_get(x_289, 0);
x_520 = lean_ctor_get(x_289, 1);
lean_inc(x_520);
lean_inc(x_519);
lean_dec(x_289);
x_521 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_521, 0, x_519);
lean_ctor_set(x_521, 1, x_520);
return x_521;
}
}
}
else
{
uint8_t x_522; 
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_522 = !lean_is_exclusive(x_286);
if (x_522 == 0)
{
return x_286;
}
else
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_523 = lean_ctor_get(x_286, 0);
x_524 = lean_ctor_get(x_286, 1);
lean_inc(x_524);
lean_inc(x_523);
lean_dec(x_286);
x_525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_525, 0, x_523);
lean_ctor_set(x_525, 1, x_524);
return x_525;
}
}
}
}
else
{
lean_object* x_526; lean_object* x_527; 
lean_dec(x_275);
lean_dec(x_16);
x_526 = lean_ctor_get(x_277, 1);
lean_inc(x_526);
lean_dec(x_277);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_527 = l_Lean_Meta_mkEq(x_274, x_276, x_4, x_5, x_6, x_7, x_526);
if (lean_obj_tag(x_527) == 0)
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_528 = lean_ctor_get(x_527, 0);
lean_inc(x_528);
x_529 = lean_ctor_get(x_527, 1);
lean_inc(x_529);
lean_dec(x_527);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_530 = l_Lean_Meta_mkEqOfHEq(x_18, x_4, x_5, x_6, x_7, x_529);
if (lean_obj_tag(x_530) == 0)
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; uint8_t x_535; 
x_531 = lean_ctor_get(x_530, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_530, 1);
lean_inc(x_532);
lean_dec(x_530);
x_533 = l_Lean_Meta_injectionCore___lambda__1___closed__4;
x_534 = lean_unsigned_to_nat(3u);
x_535 = l_Lean_Expr_isAppOfArity(x_528, x_533, x_534);
if (x_535 == 0)
{
lean_object* x_536; lean_object* x_537; 
lean_dec(x_531);
lean_dec(x_528);
lean_dec(x_3);
x_536 = l_Lean_Meta_injectionCore___lambda__1___closed__8;
x_537 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_536, x_4, x_5, x_6, x_7, x_532);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_537;
}
else
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
x_538 = l_Lean_Expr_appFn_x21(x_528);
x_539 = l_Lean_Expr_appArg_x21(x_538);
lean_dec(x_538);
x_540 = l_Lean_Expr_appArg_x21(x_528);
lean_dec(x_528);
lean_inc(x_1);
x_541 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_532);
if (lean_obj_tag(x_541) == 0)
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_542 = lean_ctor_get(x_541, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_541, 1);
lean_inc(x_543);
lean_dec(x_541);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_544 = l_Lean_Meta_isConstructorApp_x27_x3f(x_539, x_4, x_5, x_6, x_7, x_543);
if (lean_obj_tag(x_544) == 0)
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_545 = lean_ctor_get(x_544, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_544, 1);
lean_inc(x_546);
lean_dec(x_544);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_547 = l_Lean_Meta_isConstructorApp_x27_x3f(x_540, x_4, x_5, x_6, x_7, x_546);
if (lean_obj_tag(x_547) == 0)
{
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; 
lean_dec(x_542);
lean_dec(x_531);
lean_dec(x_3);
x_548 = lean_ctor_get(x_547, 1);
lean_inc(x_548);
lean_dec(x_547);
x_549 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_550 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_549, x_4, x_5, x_6, x_7, x_548);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_550;
}
else
{
lean_object* x_551; 
x_551 = lean_ctor_get(x_547, 0);
lean_inc(x_551);
if (lean_obj_tag(x_551) == 0)
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
lean_dec(x_545);
lean_dec(x_542);
lean_dec(x_531);
lean_dec(x_3);
x_552 = lean_ctor_get(x_547, 1);
lean_inc(x_552);
lean_dec(x_547);
x_553 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_554 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_553, x_4, x_5, x_6, x_7, x_552);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_554;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; uint64_t x_559; uint8_t x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; uint8_t x_567; 
x_555 = lean_ctor_get(x_4, 0);
lean_inc(x_555);
x_556 = lean_ctor_get(x_547, 1);
lean_inc(x_556);
lean_dec(x_547);
x_557 = lean_ctor_get(x_545, 0);
lean_inc(x_557);
lean_dec(x_545);
x_558 = lean_ctor_get(x_551, 0);
lean_inc(x_558);
lean_dec(x_551);
x_559 = lean_ctor_get_uint64(x_4, sizeof(void*)*7);
x_560 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 8);
x_561 = lean_ctor_get(x_4, 1);
lean_inc(x_561);
x_562 = lean_ctor_get(x_4, 2);
lean_inc(x_562);
x_563 = lean_ctor_get(x_4, 3);
lean_inc(x_563);
x_564 = lean_ctor_get(x_4, 4);
lean_inc(x_564);
x_565 = lean_ctor_get(x_4, 5);
lean_inc(x_565);
x_566 = lean_ctor_get(x_4, 6);
lean_inc(x_566);
x_567 = !lean_is_exclusive(x_555);
if (x_567 == 0)
{
uint8_t x_568; uint8_t x_569; uint8_t x_570; uint64_t x_571; uint64_t x_572; uint64_t x_573; uint64_t x_574; uint64_t x_575; lean_object* x_576; lean_object* x_577; 
x_568 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_569 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
x_570 = 1;
lean_ctor_set_uint8(x_555, 9, x_570);
x_571 = 2;
x_572 = lean_uint64_shift_right(x_559, x_571);
x_573 = lean_uint64_shift_left(x_572, x_571);
x_574 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_575 = lean_uint64_lor(x_573, x_574);
x_576 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_576, 0, x_555);
lean_ctor_set(x_576, 1, x_561);
lean_ctor_set(x_576, 2, x_562);
lean_ctor_set(x_576, 3, x_563);
lean_ctor_set(x_576, 4, x_564);
lean_ctor_set(x_576, 5, x_565);
lean_ctor_set(x_576, 6, x_566);
lean_ctor_set_uint64(x_576, sizeof(void*)*7, x_575);
lean_ctor_set_uint8(x_576, sizeof(void*)*7 + 8, x_560);
lean_ctor_set_uint8(x_576, sizeof(void*)*7 + 9, x_568);
lean_ctor_set_uint8(x_576, sizeof(void*)*7 + 10, x_569);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_577 = l_Lean_Meta_mkNoConfusion(x_542, x_531, x_576, x_5, x_6, x_7, x_556);
if (lean_obj_tag(x_577) == 0)
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; uint8_t x_584; 
x_578 = lean_ctor_get(x_577, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_577, 1);
lean_inc(x_579);
lean_dec(x_577);
x_580 = lean_ctor_get(x_557, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_580, 0);
lean_inc(x_581);
lean_dec(x_580);
x_582 = lean_ctor_get(x_558, 0);
lean_inc(x_582);
lean_dec(x_558);
x_583 = lean_ctor_get(x_582, 0);
lean_inc(x_583);
lean_dec(x_582);
x_584 = lean_name_eq(x_581, x_583);
lean_dec(x_583);
lean_dec(x_581);
if (x_584 == 0)
{
lean_object* x_585; uint8_t x_586; 
lean_dec(x_557);
lean_dec(x_3);
lean_dec(x_2);
x_585 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_578, x_4, x_5, x_6, x_7, x_579);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_586 = !lean_is_exclusive(x_585);
if (x_586 == 0)
{
lean_object* x_587; lean_object* x_588; 
x_587 = lean_ctor_get(x_585, 0);
lean_dec(x_587);
x_588 = lean_box(0);
lean_ctor_set(x_585, 0, x_588);
return x_585;
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_589 = lean_ctor_get(x_585, 1);
lean_inc(x_589);
lean_dec(x_585);
x_590 = lean_box(0);
x_591 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_589);
return x_591;
}
}
else
{
lean_object* x_592; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_578);
x_592 = lean_infer_type(x_578, x_4, x_5, x_6, x_7, x_579);
if (lean_obj_tag(x_592) == 0)
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_592, 1);
lean_inc(x_594);
lean_dec(x_592);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_595 = l_Lean_Meta_whnfD(x_593, x_4, x_5, x_6, x_7, x_594);
if (lean_obj_tag(x_595) == 0)
{
lean_object* x_596; 
x_596 = lean_ctor_get(x_595, 0);
lean_inc(x_596);
if (lean_obj_tag(x_596) == 7)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_dec(x_2);
x_597 = lean_ctor_get(x_595, 1);
lean_inc(x_597);
lean_dec(x_595);
x_598 = lean_ctor_get(x_596, 1);
lean_inc(x_598);
lean_dec(x_596);
x_599 = l_Lean_Expr_headBeta(x_598);
lean_inc(x_1);
x_600 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_597);
if (lean_obj_tag(x_600) == 0)
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; uint8_t x_608; 
x_601 = lean_ctor_get(x_600, 0);
lean_inc(x_601);
x_602 = lean_ctor_get(x_600, 1);
lean_inc(x_602);
lean_dec(x_600);
lean_inc(x_4);
x_603 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_599, x_601, x_4, x_5, x_6, x_7, x_602);
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_603, 1);
lean_inc(x_605);
lean_dec(x_603);
lean_inc(x_604);
x_606 = l_Lean_Expr_app___override(x_578, x_604);
x_607 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_606, x_4, x_5, x_6, x_7, x_605);
x_608 = !lean_is_exclusive(x_607);
if (x_608 == 0)
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_609 = lean_ctor_get(x_607, 1);
x_610 = lean_ctor_get(x_607, 0);
lean_dec(x_610);
x_611 = l_Lean_Expr_mvarId_x21(x_604);
lean_dec(x_604);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_612 = l_Lean_MVarId_tryClear(x_611, x_3, x_4, x_5, x_6, x_7, x_609);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
lean_dec(x_612);
lean_inc(x_557);
x_615 = l_Lean_Meta_getCtorNumPropFields(x_557, x_4, x_5, x_6, x_7, x_614);
if (lean_obj_tag(x_615) == 0)
{
uint8_t x_616; 
x_616 = !lean_is_exclusive(x_615);
if (x_616 == 0)
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; 
x_617 = lean_ctor_get(x_615, 0);
x_618 = lean_ctor_get(x_557, 4);
lean_inc(x_618);
lean_dec(x_557);
x_619 = lean_nat_sub(x_618, x_617);
lean_dec(x_617);
lean_dec(x_618);
lean_ctor_set_tag(x_607, 1);
lean_ctor_set(x_607, 1, x_619);
lean_ctor_set(x_607, 0, x_613);
lean_ctor_set(x_615, 0, x_607);
return x_615;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_620 = lean_ctor_get(x_615, 0);
x_621 = lean_ctor_get(x_615, 1);
lean_inc(x_621);
lean_inc(x_620);
lean_dec(x_615);
x_622 = lean_ctor_get(x_557, 4);
lean_inc(x_622);
lean_dec(x_557);
x_623 = lean_nat_sub(x_622, x_620);
lean_dec(x_620);
lean_dec(x_622);
lean_ctor_set_tag(x_607, 1);
lean_ctor_set(x_607, 1, x_623);
lean_ctor_set(x_607, 0, x_613);
x_624 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_624, 0, x_607);
lean_ctor_set(x_624, 1, x_621);
return x_624;
}
}
else
{
uint8_t x_625; 
lean_dec(x_613);
lean_free_object(x_607);
lean_dec(x_557);
x_625 = !lean_is_exclusive(x_615);
if (x_625 == 0)
{
return x_615;
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_626 = lean_ctor_get(x_615, 0);
x_627 = lean_ctor_get(x_615, 1);
lean_inc(x_627);
lean_inc(x_626);
lean_dec(x_615);
x_628 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_628, 0, x_626);
lean_ctor_set(x_628, 1, x_627);
return x_628;
}
}
}
else
{
uint8_t x_629; 
lean_free_object(x_607);
lean_dec(x_557);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_629 = !lean_is_exclusive(x_612);
if (x_629 == 0)
{
return x_612;
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; 
x_630 = lean_ctor_get(x_612, 0);
x_631 = lean_ctor_get(x_612, 1);
lean_inc(x_631);
lean_inc(x_630);
lean_dec(x_612);
x_632 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_632, 0, x_630);
lean_ctor_set(x_632, 1, x_631);
return x_632;
}
}
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_633 = lean_ctor_get(x_607, 1);
lean_inc(x_633);
lean_dec(x_607);
x_634 = l_Lean_Expr_mvarId_x21(x_604);
lean_dec(x_604);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_635 = l_Lean_MVarId_tryClear(x_634, x_3, x_4, x_5, x_6, x_7, x_633);
if (lean_obj_tag(x_635) == 0)
{
lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_636 = lean_ctor_get(x_635, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_635, 1);
lean_inc(x_637);
lean_dec(x_635);
lean_inc(x_557);
x_638 = l_Lean_Meta_getCtorNumPropFields(x_557, x_4, x_5, x_6, x_7, x_637);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_638, 1);
lean_inc(x_640);
if (lean_is_exclusive(x_638)) {
 lean_ctor_release(x_638, 0);
 lean_ctor_release(x_638, 1);
 x_641 = x_638;
} else {
 lean_dec_ref(x_638);
 x_641 = lean_box(0);
}
x_642 = lean_ctor_get(x_557, 4);
lean_inc(x_642);
lean_dec(x_557);
x_643 = lean_nat_sub(x_642, x_639);
lean_dec(x_639);
lean_dec(x_642);
x_644 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_644, 0, x_636);
lean_ctor_set(x_644, 1, x_643);
if (lean_is_scalar(x_641)) {
 x_645 = lean_alloc_ctor(0, 2, 0);
} else {
 x_645 = x_641;
}
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_640);
return x_645;
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
lean_dec(x_636);
lean_dec(x_557);
x_646 = lean_ctor_get(x_638, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_638, 1);
lean_inc(x_647);
if (lean_is_exclusive(x_638)) {
 lean_ctor_release(x_638, 0);
 lean_ctor_release(x_638, 1);
 x_648 = x_638;
} else {
 lean_dec_ref(x_638);
 x_648 = lean_box(0);
}
if (lean_is_scalar(x_648)) {
 x_649 = lean_alloc_ctor(1, 2, 0);
} else {
 x_649 = x_648;
}
lean_ctor_set(x_649, 0, x_646);
lean_ctor_set(x_649, 1, x_647);
return x_649;
}
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_557);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_650 = lean_ctor_get(x_635, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_635, 1);
lean_inc(x_651);
if (lean_is_exclusive(x_635)) {
 lean_ctor_release(x_635, 0);
 lean_ctor_release(x_635, 1);
 x_652 = x_635;
} else {
 lean_dec_ref(x_635);
 x_652 = lean_box(0);
}
if (lean_is_scalar(x_652)) {
 x_653 = lean_alloc_ctor(1, 2, 0);
} else {
 x_653 = x_652;
}
lean_ctor_set(x_653, 0, x_650);
lean_ctor_set(x_653, 1, x_651);
return x_653;
}
}
}
else
{
uint8_t x_654; 
lean_dec(x_599);
lean_dec(x_578);
lean_dec(x_557);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_654 = !lean_is_exclusive(x_600);
if (x_654 == 0)
{
return x_600;
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_655 = lean_ctor_get(x_600, 0);
x_656 = lean_ctor_get(x_600, 1);
lean_inc(x_656);
lean_inc(x_655);
lean_dec(x_600);
x_657 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_657, 0, x_655);
lean_ctor_set(x_657, 1, x_656);
return x_657;
}
}
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; 
lean_dec(x_596);
lean_dec(x_578);
lean_dec(x_557);
lean_dec(x_3);
x_658 = lean_ctor_get(x_595, 1);
lean_inc(x_658);
lean_dec(x_595);
x_659 = l_Lean_Meta_injectionCore___lambda__1___closed__17;
x_660 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_659, x_4, x_5, x_6, x_7, x_658);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_660;
}
}
else
{
uint8_t x_661; 
lean_dec(x_578);
lean_dec(x_557);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_661 = !lean_is_exclusive(x_595);
if (x_661 == 0)
{
return x_595;
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_662 = lean_ctor_get(x_595, 0);
x_663 = lean_ctor_get(x_595, 1);
lean_inc(x_663);
lean_inc(x_662);
lean_dec(x_595);
x_664 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_664, 0, x_662);
lean_ctor_set(x_664, 1, x_663);
return x_664;
}
}
}
else
{
uint8_t x_665; 
lean_dec(x_578);
lean_dec(x_557);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_665 = !lean_is_exclusive(x_592);
if (x_665 == 0)
{
return x_592;
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_666 = lean_ctor_get(x_592, 0);
x_667 = lean_ctor_get(x_592, 1);
lean_inc(x_667);
lean_inc(x_666);
lean_dec(x_592);
x_668 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_668, 0, x_666);
lean_ctor_set(x_668, 1, x_667);
return x_668;
}
}
}
}
else
{
uint8_t x_669; 
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_669 = !lean_is_exclusive(x_577);
if (x_669 == 0)
{
return x_577;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_670 = lean_ctor_get(x_577, 0);
x_671 = lean_ctor_get(x_577, 1);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_577);
x_672 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_672, 0, x_670);
lean_ctor_set(x_672, 1, x_671);
return x_672;
}
}
}
else
{
uint8_t x_673; uint8_t x_674; uint8_t x_675; uint8_t x_676; uint8_t x_677; uint8_t x_678; uint8_t x_679; uint8_t x_680; uint8_t x_681; uint8_t x_682; uint8_t x_683; uint8_t x_684; uint8_t x_685; uint8_t x_686; uint8_t x_687; uint8_t x_688; uint8_t x_689; uint8_t x_690; uint8_t x_691; lean_object* x_692; uint64_t x_693; uint64_t x_694; uint64_t x_695; uint64_t x_696; uint64_t x_697; lean_object* x_698; lean_object* x_699; 
x_673 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 9);
x_674 = lean_ctor_get_uint8(x_4, sizeof(void*)*7 + 10);
x_675 = lean_ctor_get_uint8(x_555, 0);
x_676 = lean_ctor_get_uint8(x_555, 1);
x_677 = lean_ctor_get_uint8(x_555, 2);
x_678 = lean_ctor_get_uint8(x_555, 3);
x_679 = lean_ctor_get_uint8(x_555, 4);
x_680 = lean_ctor_get_uint8(x_555, 5);
x_681 = lean_ctor_get_uint8(x_555, 6);
x_682 = lean_ctor_get_uint8(x_555, 7);
x_683 = lean_ctor_get_uint8(x_555, 8);
x_684 = lean_ctor_get_uint8(x_555, 10);
x_685 = lean_ctor_get_uint8(x_555, 11);
x_686 = lean_ctor_get_uint8(x_555, 12);
x_687 = lean_ctor_get_uint8(x_555, 13);
x_688 = lean_ctor_get_uint8(x_555, 14);
x_689 = lean_ctor_get_uint8(x_555, 15);
x_690 = lean_ctor_get_uint8(x_555, 16);
lean_dec(x_555);
x_691 = 1;
x_692 = lean_alloc_ctor(0, 0, 17);
lean_ctor_set_uint8(x_692, 0, x_675);
lean_ctor_set_uint8(x_692, 1, x_676);
lean_ctor_set_uint8(x_692, 2, x_677);
lean_ctor_set_uint8(x_692, 3, x_678);
lean_ctor_set_uint8(x_692, 4, x_679);
lean_ctor_set_uint8(x_692, 5, x_680);
lean_ctor_set_uint8(x_692, 6, x_681);
lean_ctor_set_uint8(x_692, 7, x_682);
lean_ctor_set_uint8(x_692, 8, x_683);
lean_ctor_set_uint8(x_692, 9, x_691);
lean_ctor_set_uint8(x_692, 10, x_684);
lean_ctor_set_uint8(x_692, 11, x_685);
lean_ctor_set_uint8(x_692, 12, x_686);
lean_ctor_set_uint8(x_692, 13, x_687);
lean_ctor_set_uint8(x_692, 14, x_688);
lean_ctor_set_uint8(x_692, 15, x_689);
lean_ctor_set_uint8(x_692, 16, x_690);
x_693 = 2;
x_694 = lean_uint64_shift_right(x_559, x_693);
x_695 = lean_uint64_shift_left(x_694, x_693);
x_696 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_697 = lean_uint64_lor(x_695, x_696);
x_698 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_698, 0, x_692);
lean_ctor_set(x_698, 1, x_561);
lean_ctor_set(x_698, 2, x_562);
lean_ctor_set(x_698, 3, x_563);
lean_ctor_set(x_698, 4, x_564);
lean_ctor_set(x_698, 5, x_565);
lean_ctor_set(x_698, 6, x_566);
lean_ctor_set_uint64(x_698, sizeof(void*)*7, x_697);
lean_ctor_set_uint8(x_698, sizeof(void*)*7 + 8, x_560);
lean_ctor_set_uint8(x_698, sizeof(void*)*7 + 9, x_673);
lean_ctor_set_uint8(x_698, sizeof(void*)*7 + 10, x_674);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_699 = l_Lean_Meta_mkNoConfusion(x_542, x_531, x_698, x_5, x_6, x_7, x_556);
if (lean_obj_tag(x_699) == 0)
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; uint8_t x_706; 
x_700 = lean_ctor_get(x_699, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_699, 1);
lean_inc(x_701);
lean_dec(x_699);
x_702 = lean_ctor_get(x_557, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_702, 0);
lean_inc(x_703);
lean_dec(x_702);
x_704 = lean_ctor_get(x_558, 0);
lean_inc(x_704);
lean_dec(x_558);
x_705 = lean_ctor_get(x_704, 0);
lean_inc(x_705);
lean_dec(x_704);
x_706 = lean_name_eq(x_703, x_705);
lean_dec(x_705);
lean_dec(x_703);
if (x_706 == 0)
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; 
lean_dec(x_557);
lean_dec(x_3);
lean_dec(x_2);
x_707 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_700, x_4, x_5, x_6, x_7, x_701);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_708 = lean_ctor_get(x_707, 1);
lean_inc(x_708);
if (lean_is_exclusive(x_707)) {
 lean_ctor_release(x_707, 0);
 lean_ctor_release(x_707, 1);
 x_709 = x_707;
} else {
 lean_dec_ref(x_707);
 x_709 = lean_box(0);
}
x_710 = lean_box(0);
if (lean_is_scalar(x_709)) {
 x_711 = lean_alloc_ctor(0, 2, 0);
} else {
 x_711 = x_709;
}
lean_ctor_set(x_711, 0, x_710);
lean_ctor_set(x_711, 1, x_708);
return x_711;
}
else
{
lean_object* x_712; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_700);
x_712 = lean_infer_type(x_700, x_4, x_5, x_6, x_7, x_701);
if (lean_obj_tag(x_712) == 0)
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_713 = lean_ctor_get(x_712, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_712, 1);
lean_inc(x_714);
lean_dec(x_712);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_715 = l_Lean_Meta_whnfD(x_713, x_4, x_5, x_6, x_7, x_714);
if (lean_obj_tag(x_715) == 0)
{
lean_object* x_716; 
x_716 = lean_ctor_get(x_715, 0);
lean_inc(x_716);
if (lean_obj_tag(x_716) == 7)
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; 
lean_dec(x_2);
x_717 = lean_ctor_get(x_715, 1);
lean_inc(x_717);
lean_dec(x_715);
x_718 = lean_ctor_get(x_716, 1);
lean_inc(x_718);
lean_dec(x_716);
x_719 = l_Lean_Expr_headBeta(x_718);
lean_inc(x_1);
x_720 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_717);
if (lean_obj_tag(x_720) == 0)
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_721 = lean_ctor_get(x_720, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_720, 1);
lean_inc(x_722);
lean_dec(x_720);
lean_inc(x_4);
x_723 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_719, x_721, x_4, x_5, x_6, x_7, x_722);
x_724 = lean_ctor_get(x_723, 0);
lean_inc(x_724);
x_725 = lean_ctor_get(x_723, 1);
lean_inc(x_725);
lean_dec(x_723);
lean_inc(x_724);
x_726 = l_Lean_Expr_app___override(x_700, x_724);
x_727 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_726, x_4, x_5, x_6, x_7, x_725);
x_728 = lean_ctor_get(x_727, 1);
lean_inc(x_728);
if (lean_is_exclusive(x_727)) {
 lean_ctor_release(x_727, 0);
 lean_ctor_release(x_727, 1);
 x_729 = x_727;
} else {
 lean_dec_ref(x_727);
 x_729 = lean_box(0);
}
x_730 = l_Lean_Expr_mvarId_x21(x_724);
lean_dec(x_724);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_731 = l_Lean_MVarId_tryClear(x_730, x_3, x_4, x_5, x_6, x_7, x_728);
if (lean_obj_tag(x_731) == 0)
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; 
x_732 = lean_ctor_get(x_731, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_731, 1);
lean_inc(x_733);
lean_dec(x_731);
lean_inc(x_557);
x_734 = l_Lean_Meta_getCtorNumPropFields(x_557, x_4, x_5, x_6, x_7, x_733);
if (lean_obj_tag(x_734) == 0)
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; 
x_735 = lean_ctor_get(x_734, 0);
lean_inc(x_735);
x_736 = lean_ctor_get(x_734, 1);
lean_inc(x_736);
if (lean_is_exclusive(x_734)) {
 lean_ctor_release(x_734, 0);
 lean_ctor_release(x_734, 1);
 x_737 = x_734;
} else {
 lean_dec_ref(x_734);
 x_737 = lean_box(0);
}
x_738 = lean_ctor_get(x_557, 4);
lean_inc(x_738);
lean_dec(x_557);
x_739 = lean_nat_sub(x_738, x_735);
lean_dec(x_735);
lean_dec(x_738);
if (lean_is_scalar(x_729)) {
 x_740 = lean_alloc_ctor(1, 2, 0);
} else {
 x_740 = x_729;
 lean_ctor_set_tag(x_740, 1);
}
lean_ctor_set(x_740, 0, x_732);
lean_ctor_set(x_740, 1, x_739);
if (lean_is_scalar(x_737)) {
 x_741 = lean_alloc_ctor(0, 2, 0);
} else {
 x_741 = x_737;
}
lean_ctor_set(x_741, 0, x_740);
lean_ctor_set(x_741, 1, x_736);
return x_741;
}
else
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
lean_dec(x_732);
lean_dec(x_729);
lean_dec(x_557);
x_742 = lean_ctor_get(x_734, 0);
lean_inc(x_742);
x_743 = lean_ctor_get(x_734, 1);
lean_inc(x_743);
if (lean_is_exclusive(x_734)) {
 lean_ctor_release(x_734, 0);
 lean_ctor_release(x_734, 1);
 x_744 = x_734;
} else {
 lean_dec_ref(x_734);
 x_744 = lean_box(0);
}
if (lean_is_scalar(x_744)) {
 x_745 = lean_alloc_ctor(1, 2, 0);
} else {
 x_745 = x_744;
}
lean_ctor_set(x_745, 0, x_742);
lean_ctor_set(x_745, 1, x_743);
return x_745;
}
}
else
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; 
lean_dec(x_729);
lean_dec(x_557);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_746 = lean_ctor_get(x_731, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_731, 1);
lean_inc(x_747);
if (lean_is_exclusive(x_731)) {
 lean_ctor_release(x_731, 0);
 lean_ctor_release(x_731, 1);
 x_748 = x_731;
} else {
 lean_dec_ref(x_731);
 x_748 = lean_box(0);
}
if (lean_is_scalar(x_748)) {
 x_749 = lean_alloc_ctor(1, 2, 0);
} else {
 x_749 = x_748;
}
lean_ctor_set(x_749, 0, x_746);
lean_ctor_set(x_749, 1, x_747);
return x_749;
}
}
else
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; 
lean_dec(x_719);
lean_dec(x_700);
lean_dec(x_557);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_750 = lean_ctor_get(x_720, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_720, 1);
lean_inc(x_751);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 lean_ctor_release(x_720, 1);
 x_752 = x_720;
} else {
 lean_dec_ref(x_720);
 x_752 = lean_box(0);
}
if (lean_is_scalar(x_752)) {
 x_753 = lean_alloc_ctor(1, 2, 0);
} else {
 x_753 = x_752;
}
lean_ctor_set(x_753, 0, x_750);
lean_ctor_set(x_753, 1, x_751);
return x_753;
}
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; 
lean_dec(x_716);
lean_dec(x_700);
lean_dec(x_557);
lean_dec(x_3);
x_754 = lean_ctor_get(x_715, 1);
lean_inc(x_754);
lean_dec(x_715);
x_755 = l_Lean_Meta_injectionCore___lambda__1___closed__17;
x_756 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_755, x_4, x_5, x_6, x_7, x_754);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_756;
}
}
else
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; 
lean_dec(x_700);
lean_dec(x_557);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_757 = lean_ctor_get(x_715, 0);
lean_inc(x_757);
x_758 = lean_ctor_get(x_715, 1);
lean_inc(x_758);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 lean_ctor_release(x_715, 1);
 x_759 = x_715;
} else {
 lean_dec_ref(x_715);
 x_759 = lean_box(0);
}
if (lean_is_scalar(x_759)) {
 x_760 = lean_alloc_ctor(1, 2, 0);
} else {
 x_760 = x_759;
}
lean_ctor_set(x_760, 0, x_757);
lean_ctor_set(x_760, 1, x_758);
return x_760;
}
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; 
lean_dec(x_700);
lean_dec(x_557);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_761 = lean_ctor_get(x_712, 0);
lean_inc(x_761);
x_762 = lean_ctor_get(x_712, 1);
lean_inc(x_762);
if (lean_is_exclusive(x_712)) {
 lean_ctor_release(x_712, 0);
 lean_ctor_release(x_712, 1);
 x_763 = x_712;
} else {
 lean_dec_ref(x_712);
 x_763 = lean_box(0);
}
if (lean_is_scalar(x_763)) {
 x_764 = lean_alloc_ctor(1, 2, 0);
} else {
 x_764 = x_763;
}
lean_ctor_set(x_764, 0, x_761);
lean_ctor_set(x_764, 1, x_762);
return x_764;
}
}
}
else
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_765 = lean_ctor_get(x_699, 0);
lean_inc(x_765);
x_766 = lean_ctor_get(x_699, 1);
lean_inc(x_766);
if (lean_is_exclusive(x_699)) {
 lean_ctor_release(x_699, 0);
 lean_ctor_release(x_699, 1);
 x_767 = x_699;
} else {
 lean_dec_ref(x_699);
 x_767 = lean_box(0);
}
if (lean_is_scalar(x_767)) {
 x_768 = lean_alloc_ctor(1, 2, 0);
} else {
 x_768 = x_767;
}
lean_ctor_set(x_768, 0, x_765);
lean_ctor_set(x_768, 1, x_766);
return x_768;
}
}
}
}
}
else
{
uint8_t x_769; 
lean_dec(x_545);
lean_dec(x_542);
lean_dec(x_531);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_769 = !lean_is_exclusive(x_547);
if (x_769 == 0)
{
return x_547;
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; 
x_770 = lean_ctor_get(x_547, 0);
x_771 = lean_ctor_get(x_547, 1);
lean_inc(x_771);
lean_inc(x_770);
lean_dec(x_547);
x_772 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_772, 0, x_770);
lean_ctor_set(x_772, 1, x_771);
return x_772;
}
}
}
else
{
uint8_t x_773; 
lean_dec(x_542);
lean_dec(x_540);
lean_dec(x_531);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_773 = !lean_is_exclusive(x_544);
if (x_773 == 0)
{
return x_544;
}
else
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_774 = lean_ctor_get(x_544, 0);
x_775 = lean_ctor_get(x_544, 1);
lean_inc(x_775);
lean_inc(x_774);
lean_dec(x_544);
x_776 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_776, 0, x_774);
lean_ctor_set(x_776, 1, x_775);
return x_776;
}
}
}
else
{
uint8_t x_777; 
lean_dec(x_540);
lean_dec(x_539);
lean_dec(x_531);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_777 = !lean_is_exclusive(x_541);
if (x_777 == 0)
{
return x_541;
}
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_778 = lean_ctor_get(x_541, 0);
x_779 = lean_ctor_get(x_541, 1);
lean_inc(x_779);
lean_inc(x_778);
lean_dec(x_541);
x_780 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_780, 0, x_778);
lean_ctor_set(x_780, 1, x_779);
return x_780;
}
}
}
}
else
{
uint8_t x_781; 
lean_dec(x_528);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_781 = !lean_is_exclusive(x_530);
if (x_781 == 0)
{
return x_530;
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; 
x_782 = lean_ctor_get(x_530, 0);
x_783 = lean_ctor_get(x_530, 1);
lean_inc(x_783);
lean_inc(x_782);
lean_dec(x_530);
x_784 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_784, 0, x_782);
lean_ctor_set(x_784, 1, x_783);
return x_784;
}
}
}
else
{
uint8_t x_785; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_785 = !lean_is_exclusive(x_527);
if (x_785 == 0)
{
return x_527;
}
else
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; 
x_786 = lean_ctor_get(x_527, 0);
x_787 = lean_ctor_get(x_527, 1);
lean_inc(x_787);
lean_inc(x_786);
lean_dec(x_527);
x_788 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_788, 0, x_786);
lean_ctor_set(x_788, 1, x_787);
return x_788;
}
}
}
}
else
{
uint8_t x_789; 
lean_dec(x_276);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_789 = !lean_is_exclusive(x_277);
if (x_789 == 0)
{
return x_277;
}
else
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; 
x_790 = lean_ctor_get(x_277, 0);
x_791 = lean_ctor_get(x_277, 1);
lean_inc(x_791);
lean_inc(x_790);
lean_dec(x_277);
x_792 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_792, 0, x_790);
lean_ctor_set(x_792, 1, x_791);
return x_792;
}
}
}
}
else
{
uint8_t x_793; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_793 = !lean_is_exclusive(x_15);
if (x_793 == 0)
{
return x_15;
}
else
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; 
x_794 = lean_ctor_get(x_15, 0);
x_795 = lean_ctor_get(x_15, 1);
lean_inc(x_795);
lean_inc(x_794);
lean_dec(x_15);
x_796 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_796, 0, x_794);
lean_ctor_set(x_796, 1, x_795);
return x_796;
}
}
}
else
{
uint8_t x_797; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_797 = !lean_is_exclusive(x_11);
if (x_797 == 0)
{
return x_11;
}
else
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; 
x_798 = lean_ctor_get(x_11, 0);
x_799 = lean_ctor_get(x_11, 1);
lean_inc(x_799);
lean_inc(x_798);
lean_dec(x_11);
x_800 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_800, 0, x_798);
lean_ctor_set(x_800, 1, x_799);
return x_800;
}
}
}
else
{
uint8_t x_801; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_801 = !lean_is_exclusive(x_9);
if (x_801 == 0)
{
return x_9;
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; 
x_802 = lean_ctor_get(x_9, 0);
x_803 = lean_ctor_get(x_9, 1);
lean_inc(x_803);
lean_inc(x_802);
lean_dec(x_9);
x_804 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_804, 0, x_802);
lean_ctor_set(x_804, 1, x_803);
return x_804;
}
}
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("injection", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_injectionCore___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_Meta_injectionCore___closed__2;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_injectionCore___lambda__1), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_2);
x_10 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro_go(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_2, x_13);
lean_dec(x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_15; lean_object* x_16; 
x_15 = 0;
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Meta_intro1Core(x_3, x_15, x_6, x_7, x_8, x_9, x_10);
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
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Meta_heqToEq(x_20, x_19, x_1, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
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
x_26 = lean_array_push(x_4, x_24);
x_27 = lean_box(0);
x_2 = x_14;
x_3 = x_25;
x_4 = x_26;
x_5 = x_27;
x_10 = x_23;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
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
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_5, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_5, 1);
lean_inc(x_38);
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_39 = l_Lean_MVarId_intro(x_3, x_37, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_44 = l_Lean_Meta_heqToEq(x_43, x_42, x_1, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_array_push(x_4, x_47);
x_2 = x_14;
x_3 = x_48;
x_4 = x_49;
x_5 = x_38;
x_10 = x_46;
goto _start;
}
else
{
uint8_t x_51; 
lean_dec(x_38);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_44);
if (x_51 == 0)
{
return x_44;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_44, 0);
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_44);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_38);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
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
lean_object* x_59; lean_object* x_60; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_3);
lean_ctor_set(x_59, 1, x_4);
lean_ctor_set(x_59, 2, x_5);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_10);
return x_60;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Meta_injectionIntro_go(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_injectionIntro___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Lean_Meta_injectionIntro___closed__1;
x_11 = l_Lean_Meta_injectionIntro_go(x_4, x_2, x_1, x_10, x_3, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_injectionIntro(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_injectionCore(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = 1;
x_21 = l_Lean_Meta_injectionIntro(x_18, x_19, x_3, x_20, x_4, x_5, x_6, x_7, x_17);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
return x_9;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_9, 0);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_9);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at_Lean_Meta_injections_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___rarg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = l_Lean_Exception_isInterrupt(x_12);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = l_Lean_Exception_isRuntime(x_12);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_free_object(x_10);
x_16 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_13);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
else
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = l_Lean_Exception_isInterrupt(x_21);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = l_Lean_Exception_isRuntime(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = l_Lean_Meta_SavedState_restore(x_8, x_2, x_3, x_4, x_5, x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_8);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_27 = x_25;
} else {
 lean_dec_ref(x_25);
 x_27 = lean_box(0);
}
if (lean_is_scalar(x_27)) {
 x_28 = lean_alloc_ctor(1, 2, 0);
} else {
 x_28 = x_27;
 lean_ctor_set_tag(x_28, 1);
}
lean_ctor_set(x_28, 0, x_21);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_22);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_22);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections_go___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_12 = l_Lean_Meta_injection(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_13, 2);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_array_to_list(x_22);
x_25 = l_List_appendTR___rarg(x_24, x_4);
x_26 = lean_box(0);
x_27 = l_Lean_RBNode_insert___at_Lean_FVarIdSet_insert___spec__1(x_5, x_2, x_26);
lean_inc(x_21);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_injections_go), 10, 5);
lean_closure_set(x_28, 0, x_6);
lean_closure_set(x_28, 1, x_25);
lean_closure_set(x_28, 2, x_21);
lean_closure_set(x_28, 3, x_23);
lean_closure_set(x_28, 4, x_27);
x_29 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_21, x_28, x_7, x_8, x_9, x_10, x_20);
return x_29;
}
}
else
{
uint8_t x_30; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
static lean_object* _init_l_Lean_Meta_injections_go___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("injections", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injections_go___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_injections_go___closed__1;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_injections_go___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("recursion depth exceeded", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injections_go___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injections_go___closed__3;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injections_go___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injections_go___closed__4;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injections_go___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injections_go___closed__5;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_1, x_11);
if (x_12 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_4);
lean_ctor_set(x_13, 2, x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_1, x_17);
lean_dec(x_1);
x_19 = lean_nat_add(x_18, x_17);
x_20 = l_Lean_RBNode_findCore___at___private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux___spec__2(x_5, x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_inc(x_6);
lean_inc(x_15);
x_21 = l_Lean_FVarId_getType(x_15, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Meta_matchEqHEq_x3f(x_22, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec(x_18);
lean_dec(x_15);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_1 = x_19;
x_2 = x_16;
x_10 = x_26;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_24, 1);
lean_inc(x_30);
lean_dec(x_24);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_33 = lean_whnf(x_31, x_6, x_7, x_8, x_9, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_36 = lean_whnf(x_32, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_56; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_56 = l_Lean_Expr_isRawNatLit(x_34);
lean_dec(x_34);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_37);
x_57 = lean_box(0);
x_39 = x_57;
goto block_55;
}
else
{
uint8_t x_58; 
x_58 = l_Lean_Expr_isRawNatLit(x_37);
lean_dec(x_37);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = lean_box(0);
x_39 = x_59;
goto block_55;
}
else
{
lean_dec(x_18);
lean_dec(x_15);
x_1 = x_19;
x_2 = x_16;
x_10 = x_38;
goto _start;
}
}
block_55:
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_39);
lean_inc(x_5);
lean_inc(x_16);
lean_inc(x_4);
lean_inc(x_3);
x_40 = lean_alloc_closure((void*)(l_Lean_Meta_injections_go___lambda__1), 11, 6);
lean_closure_set(x_40, 0, x_3);
lean_closure_set(x_40, 1, x_15);
lean_closure_set(x_40, 2, x_4);
lean_closure_set(x_40, 3, x_16);
lean_closure_set(x_40, 4, x_5);
lean_closure_set(x_40, 5, x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_41 = l_Lean_commitIfNoEx___at_Lean_Meta_injections_go___spec__1(x_40, x_6, x_7, x_8, x_9, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_ctor_get(x_41, 1);
x_45 = l_Lean_Exception_isInterrupt(x_43);
if (x_45 == 0)
{
uint8_t x_46; 
x_46 = l_Lean_Exception_isRuntime(x_43);
if (x_46 == 0)
{
lean_free_object(x_41);
lean_dec(x_43);
x_1 = x_19;
x_2 = x_16;
x_10 = x_44;
goto _start;
}
else
{
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_41;
}
}
else
{
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_41;
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_41, 0);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_41);
x_50 = l_Lean_Exception_isInterrupt(x_48);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = l_Lean_Exception_isRuntime(x_48);
if (x_51 == 0)
{
lean_dec(x_48);
x_1 = x_19;
x_2 = x_16;
x_10 = x_49;
goto _start;
}
else
{
lean_object* x_53; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_49);
return x_53;
}
}
else
{
lean_object* x_54; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_48);
lean_ctor_set(x_54, 1, x_49);
return x_54;
}
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_34);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_61 = !lean_is_exclusive(x_36);
if (x_61 == 0)
{
return x_36;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_36, 0);
x_63 = lean_ctor_get(x_36, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_36);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_32);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_65 = !lean_is_exclusive(x_33);
if (x_65 == 0)
{
return x_33;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_33, 0);
x_67 = lean_ctor_get(x_33, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_33);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_69 = !lean_is_exclusive(x_24);
if (x_69 == 0)
{
return x_24;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_24, 0);
x_71 = lean_ctor_get(x_24, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_24);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_21);
if (x_73 == 0)
{
return x_21;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_21, 0);
x_75 = lean_ctor_get(x_21, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_21);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_15);
x_1 = x_19;
x_2 = x_16;
goto _start;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_78 = l_Lean_Meta_injections_go___closed__2;
x_79 = l_Lean_Meta_injections_go___closed__6;
x_80 = l_Lean_Meta_throwTacticEx___rarg(x_78, x_3, x_79, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_80;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = l_Lean_LocalContext_getFVarIds(x_10);
lean_dec(x_10);
x_12 = lean_array_to_list(x_11);
x_13 = l_Lean_Meta_injections_go(x_1, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_injections___lambda__1), 9, 4);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_4);
x_11 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Injection(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_injectionCore___lambda__1___closed__1 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__1);
l_Lean_Meta_injectionCore___lambda__1___closed__2 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__2);
l_Lean_Meta_injectionCore___lambda__1___closed__3 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__3);
l_Lean_Meta_injectionCore___lambda__1___closed__4 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__4();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__4);
l_Lean_Meta_injectionCore___lambda__1___closed__5 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__5();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__5);
l_Lean_Meta_injectionCore___lambda__1___closed__6 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__6();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__6);
l_Lean_Meta_injectionCore___lambda__1___closed__7 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__7();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__7);
l_Lean_Meta_injectionCore___lambda__1___closed__8 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__8();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__8);
l_Lean_Meta_injectionCore___lambda__1___closed__9 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__9();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__9);
l_Lean_Meta_injectionCore___lambda__1___closed__10 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__10();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__10);
l_Lean_Meta_injectionCore___lambda__1___closed__11 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__11();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__11);
l_Lean_Meta_injectionCore___lambda__1___closed__12 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__12();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__12);
l_Lean_Meta_injectionCore___lambda__1___closed__13 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__13();
l_Lean_Meta_injectionCore___lambda__1___closed__14 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__14();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__14);
l_Lean_Meta_injectionCore___lambda__1___closed__15 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__15();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__15);
l_Lean_Meta_injectionCore___lambda__1___closed__16 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__16();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__16);
l_Lean_Meta_injectionCore___lambda__1___closed__17 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__17();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__17);
l_Lean_Meta_injectionCore___closed__1 = _init_l_Lean_Meta_injectionCore___closed__1();
lean_mark_persistent(l_Lean_Meta_injectionCore___closed__1);
l_Lean_Meta_injectionCore___closed__2 = _init_l_Lean_Meta_injectionCore___closed__2();
lean_mark_persistent(l_Lean_Meta_injectionCore___closed__2);
l_Lean_Meta_injectionIntro___closed__1 = _init_l_Lean_Meta_injectionIntro___closed__1();
lean_mark_persistent(l_Lean_Meta_injectionIntro___closed__1);
l_Lean_Meta_injections_go___closed__1 = _init_l_Lean_Meta_injections_go___closed__1();
lean_mark_persistent(l_Lean_Meta_injections_go___closed__1);
l_Lean_Meta_injections_go___closed__2 = _init_l_Lean_Meta_injections_go___closed__2();
lean_mark_persistent(l_Lean_Meta_injections_go___closed__2);
l_Lean_Meta_injections_go___closed__3 = _init_l_Lean_Meta_injections_go___closed__3();
lean_mark_persistent(l_Lean_Meta_injections_go___closed__3);
l_Lean_Meta_injections_go___closed__4 = _init_l_Lean_Meta_injections_go___closed__4();
lean_mark_persistent(l_Lean_Meta_injections_go___closed__4);
l_Lean_Meta_injections_go___closed__5 = _init_l_Lean_Meta_injections_go___closed__5();
lean_mark_persistent(l_Lean_Meta_injections_go___closed__5);
l_Lean_Meta_injections_go___closed__6 = _init_l_Lean_Meta_injections_go___closed__6();
lean_mark_persistent(l_Lean_Meta_injections_go___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
