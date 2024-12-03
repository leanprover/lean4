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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_getCtorNumPropFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_getCtorNumPropFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_getCtorNumPropFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; 
x_16 = lean_nat_dec_lt(x_8, x_5);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_7, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_7, x_20);
lean_dec(x_7);
x_28 = lean_ctor_get(x_1, 3);
x_29 = lean_nat_add(x_28, x_8);
x_30 = lean_array_get_size(x_2);
x_31 = lean_nat_dec_lt(x_29, x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_29);
x_32 = l_Lean_instInhabitedExpr;
x_33 = l_outOfBounds___rarg(x_32);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_34 = lean_infer_type(x_33, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_37 = l_Lean_Meta_isProp(x_35, x_11, x_12, x_13, x_14, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_unbox(x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_10);
x_22 = x_41;
x_23 = x_40;
goto block_27;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_nat_add(x_10, x_20);
lean_dec(x_10);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_22 = x_44;
x_23 = x_42;
goto block_27;
}
}
else
{
uint8_t x_45; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
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
else
{
uint8_t x_49; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_49 = !lean_is_exclusive(x_34);
if (x_49 == 0)
{
return x_34;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_34, 0);
x_51 = lean_ctor_get(x_34, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_34);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_array_fget(x_2, x_29);
lean_dec(x_29);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_54 = lean_infer_type(x_53, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_57 = l_Lean_Meta_isProp(x_55, x_11, x_12, x_13, x_14, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_10);
x_22 = x_61;
x_23 = x_60;
goto block_27;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_57, 1);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_nat_add(x_10, x_20);
lean_dec(x_10);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_22 = x_64;
x_23 = x_62;
goto block_27;
}
}
else
{
uint8_t x_65; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_65 = !lean_is_exclusive(x_57);
if (x_65 == 0)
{
return x_57;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_57, 0);
x_67 = lean_ctor_get(x_57, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_57);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
uint8_t x_69; 
lean_dec(x_21);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
x_69 = !lean_is_exclusive(x_54);
if (x_69 == 0)
{
return x_54;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_54, 0);
x_71 = lean_ctor_get(x_54, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_54);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
block_27:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_nat_add(x_8, x_6);
lean_dec(x_8);
x_7 = x_21;
x_8 = x_25;
x_9 = lean_box(0);
x_10 = x_24;
x_15 = x_23;
goto _start;
}
}
else
{
lean_object* x_73; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_10);
lean_ctor_set(x_73, 1, x_15);
return x_73;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
lean_inc(x_9);
x_13 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_getCtorNumPropFields___spec__1(x_1, x_2, x_12, x_10, x_9, x_11, x_9, x_10, lean_box(0), x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
lean_dec(x_12);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_Lean_Meta_getCtorNumPropFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at_Lean_Meta_getCtorNumPropFields___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getCtorNumPropFields___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
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
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
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
x_48 = lean_ctor_get_uint64(x_4, sizeof(void*)*6);
x_49 = lean_ctor_get(x_4, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_4, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_4, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_4, 4);
lean_inc(x_52);
x_53 = lean_ctor_get(x_4, 5);
lean_inc(x_53);
x_54 = !lean_is_exclusive(x_44);
if (x_54 == 0)
{
uint8_t x_55; uint8_t x_56; uint8_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; lean_object* x_63; lean_object* x_64; 
x_55 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 8);
x_56 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 9);
x_57 = 1;
lean_ctor_set_uint8(x_44, 9, x_57);
x_58 = 2;
x_59 = lean_uint64_shift_right(x_48, x_58);
x_60 = lean_uint64_shift_left(x_59, x_58);
x_61 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_62 = lean_uint64_lor(x_60, x_61);
x_63 = lean_alloc_ctor(0, 6, 10);
lean_ctor_set(x_63, 0, x_44);
lean_ctor_set(x_63, 1, x_49);
lean_ctor_set(x_63, 2, x_50);
lean_ctor_set(x_63, 3, x_51);
lean_ctor_set(x_63, 4, x_52);
lean_ctor_set(x_63, 5, x_53);
lean_ctor_set_uint64(x_63, sizeof(void*)*6, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*6 + 8, x_55);
lean_ctor_set_uint8(x_63, sizeof(void*)*6 + 9, x_56);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_64 = l_Lean_Meta_mkNoConfusion(x_31, x_18, x_63, x_5, x_6, x_7, x_45);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_46, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec(x_67);
x_69 = lean_ctor_get(x_47, 0);
lean_inc(x_69);
lean_dec(x_47);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_name_eq(x_68, x_70);
lean_dec(x_70);
lean_dec(x_68);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_46);
lean_dec(x_3);
lean_dec(x_2);
x_72 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_65, x_4, x_5, x_6, x_7, x_66);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_72, 0);
lean_dec(x_74);
x_75 = lean_box(0);
lean_ctor_set(x_72, 0, x_75);
return x_72;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_dec(x_72);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_65);
x_79 = lean_infer_type(x_65, x_4, x_5, x_6, x_7, x_66);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_82 = l_Lean_Meta_whnfD(x_80, x_4, x_5, x_6, x_7, x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
if (lean_obj_tag(x_83) == 7)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_2);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = l_Lean_Expr_headBeta(x_85);
lean_inc(x_1);
x_87 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_84);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
lean_inc(x_4);
x_90 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_86, x_88, x_4, x_5, x_6, x_7, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_91);
x_93 = l_Lean_Expr_app___override(x_65, x_91);
x_94 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_93, x_4, x_5, x_6, x_7, x_92);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_94, 1);
x_97 = lean_ctor_get(x_94, 0);
lean_dec(x_97);
x_98 = l_Lean_Expr_mvarId_x21(x_91);
lean_dec(x_91);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_99 = l_Lean_MVarId_tryClear(x_98, x_3, x_4, x_5, x_6, x_7, x_96);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
lean_inc(x_46);
x_102 = l_Lean_Meta_getCtorNumPropFields(x_46, x_4, x_5, x_6, x_7, x_101);
if (lean_obj_tag(x_102) == 0)
{
uint8_t x_103; 
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_102, 0);
x_105 = lean_ctor_get(x_46, 4);
lean_inc(x_105);
lean_dec(x_46);
x_106 = lean_nat_sub(x_105, x_104);
lean_dec(x_104);
lean_dec(x_105);
lean_ctor_set_tag(x_94, 1);
lean_ctor_set(x_94, 1, x_106);
lean_ctor_set(x_94, 0, x_100);
lean_ctor_set(x_102, 0, x_94);
return x_102;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_102, 0);
x_108 = lean_ctor_get(x_102, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_102);
x_109 = lean_ctor_get(x_46, 4);
lean_inc(x_109);
lean_dec(x_46);
x_110 = lean_nat_sub(x_109, x_107);
lean_dec(x_107);
lean_dec(x_109);
lean_ctor_set_tag(x_94, 1);
lean_ctor_set(x_94, 1, x_110);
lean_ctor_set(x_94, 0, x_100);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_94);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
}
else
{
uint8_t x_112; 
lean_dec(x_100);
lean_free_object(x_94);
lean_dec(x_46);
x_112 = !lean_is_exclusive(x_102);
if (x_112 == 0)
{
return x_102;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_102, 0);
x_114 = lean_ctor_get(x_102, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_102);
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
lean_free_object(x_94);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_116 = !lean_is_exclusive(x_99);
if (x_116 == 0)
{
return x_99;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_99, 0);
x_118 = lean_ctor_get(x_99, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_99);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_94, 1);
lean_inc(x_120);
lean_dec(x_94);
x_121 = l_Lean_Expr_mvarId_x21(x_91);
lean_dec(x_91);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_122 = l_Lean_MVarId_tryClear(x_121, x_3, x_4, x_5, x_6, x_7, x_120);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
lean_inc(x_46);
x_125 = l_Lean_Meta_getCtorNumPropFields(x_46, x_4, x_5, x_6, x_7, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
x_129 = lean_ctor_get(x_46, 4);
lean_inc(x_129);
lean_dec(x_46);
x_130 = lean_nat_sub(x_129, x_126);
lean_dec(x_126);
lean_dec(x_129);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_123);
lean_ctor_set(x_131, 1, x_130);
if (lean_is_scalar(x_128)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_128;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_127);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_123);
lean_dec(x_46);
x_133 = lean_ctor_get(x_125, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_125, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_135 = x_125;
} else {
 lean_dec_ref(x_125);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_137 = lean_ctor_get(x_122, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_122, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_139 = x_122;
} else {
 lean_dec_ref(x_122);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_86);
lean_dec(x_65);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_141 = !lean_is_exclusive(x_87);
if (x_141 == 0)
{
return x_87;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_87, 0);
x_143 = lean_ctor_get(x_87, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_87);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_83);
lean_dec(x_65);
lean_dec(x_46);
lean_dec(x_3);
x_145 = lean_ctor_get(x_82, 1);
lean_inc(x_145);
lean_dec(x_82);
x_146 = l_Lean_Meta_injectionCore___lambda__1___closed__17;
x_147 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_146, x_4, x_5, x_6, x_7, x_145);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_147;
}
}
else
{
uint8_t x_148; 
lean_dec(x_65);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_82);
if (x_148 == 0)
{
return x_82;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_82, 0);
x_150 = lean_ctor_get(x_82, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_82);
x_151 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
}
else
{
uint8_t x_152; 
lean_dec(x_65);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_152 = !lean_is_exclusive(x_79);
if (x_152 == 0)
{
return x_79;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_79, 0);
x_154 = lean_ctor_get(x_79, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_79);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
else
{
uint8_t x_156; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_64);
if (x_156 == 0)
{
return x_64;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_64, 0);
x_158 = lean_ctor_get(x_64, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_64);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
else
{
uint8_t x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; uint8_t x_170; uint8_t x_171; uint8_t x_172; uint8_t x_173; uint8_t x_174; uint8_t x_175; uint8_t x_176; uint8_t x_177; uint8_t x_178; uint8_t x_179; lean_object* x_180; uint64_t x_181; uint64_t x_182; uint64_t x_183; uint64_t x_184; uint64_t x_185; lean_object* x_186; lean_object* x_187; 
x_160 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 8);
x_161 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 9);
x_162 = lean_ctor_get_uint8(x_44, 0);
x_163 = lean_ctor_get_uint8(x_44, 1);
x_164 = lean_ctor_get_uint8(x_44, 2);
x_165 = lean_ctor_get_uint8(x_44, 3);
x_166 = lean_ctor_get_uint8(x_44, 4);
x_167 = lean_ctor_get_uint8(x_44, 5);
x_168 = lean_ctor_get_uint8(x_44, 6);
x_169 = lean_ctor_get_uint8(x_44, 7);
x_170 = lean_ctor_get_uint8(x_44, 8);
x_171 = lean_ctor_get_uint8(x_44, 10);
x_172 = lean_ctor_get_uint8(x_44, 11);
x_173 = lean_ctor_get_uint8(x_44, 12);
x_174 = lean_ctor_get_uint8(x_44, 13);
x_175 = lean_ctor_get_uint8(x_44, 14);
x_176 = lean_ctor_get_uint8(x_44, 15);
x_177 = lean_ctor_get_uint8(x_44, 16);
x_178 = lean_ctor_get_uint8(x_44, 17);
lean_dec(x_44);
x_179 = 1;
x_180 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_180, 0, x_162);
lean_ctor_set_uint8(x_180, 1, x_163);
lean_ctor_set_uint8(x_180, 2, x_164);
lean_ctor_set_uint8(x_180, 3, x_165);
lean_ctor_set_uint8(x_180, 4, x_166);
lean_ctor_set_uint8(x_180, 5, x_167);
lean_ctor_set_uint8(x_180, 6, x_168);
lean_ctor_set_uint8(x_180, 7, x_169);
lean_ctor_set_uint8(x_180, 8, x_170);
lean_ctor_set_uint8(x_180, 9, x_179);
lean_ctor_set_uint8(x_180, 10, x_171);
lean_ctor_set_uint8(x_180, 11, x_172);
lean_ctor_set_uint8(x_180, 12, x_173);
lean_ctor_set_uint8(x_180, 13, x_174);
lean_ctor_set_uint8(x_180, 14, x_175);
lean_ctor_set_uint8(x_180, 15, x_176);
lean_ctor_set_uint8(x_180, 16, x_177);
lean_ctor_set_uint8(x_180, 17, x_178);
x_181 = 2;
x_182 = lean_uint64_shift_right(x_48, x_181);
x_183 = lean_uint64_shift_left(x_182, x_181);
x_184 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_185 = lean_uint64_lor(x_183, x_184);
x_186 = lean_alloc_ctor(0, 6, 10);
lean_ctor_set(x_186, 0, x_180);
lean_ctor_set(x_186, 1, x_49);
lean_ctor_set(x_186, 2, x_50);
lean_ctor_set(x_186, 3, x_51);
lean_ctor_set(x_186, 4, x_52);
lean_ctor_set(x_186, 5, x_53);
lean_ctor_set_uint64(x_186, sizeof(void*)*6, x_185);
lean_ctor_set_uint8(x_186, sizeof(void*)*6 + 8, x_160);
lean_ctor_set_uint8(x_186, sizeof(void*)*6 + 9, x_161);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_187 = l_Lean_Meta_mkNoConfusion(x_31, x_18, x_186, x_5, x_6, x_7, x_45);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_46, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
lean_dec(x_190);
x_192 = lean_ctor_get(x_47, 0);
lean_inc(x_192);
lean_dec(x_47);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
lean_dec(x_192);
x_194 = lean_name_eq(x_191, x_193);
lean_dec(x_193);
lean_dec(x_191);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_46);
lean_dec(x_3);
lean_dec(x_2);
x_195 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_188, x_4, x_5, x_6, x_7, x_189);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_196 = lean_ctor_get(x_195, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_197 = x_195;
} else {
 lean_dec_ref(x_195);
 x_197 = lean_box(0);
}
x_198 = lean_box(0);
if (lean_is_scalar(x_197)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_197;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_196);
return x_199;
}
else
{
lean_object* x_200; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_188);
x_200 = lean_infer_type(x_188, x_4, x_5, x_6, x_7, x_189);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_200, 1);
lean_inc(x_202);
lean_dec(x_200);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_203 = l_Lean_Meta_whnfD(x_201, x_4, x_5, x_6, x_7, x_202);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
if (lean_obj_tag(x_204) == 7)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_2);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = l_Lean_Expr_headBeta(x_206);
lean_inc(x_1);
x_208 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_205);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
lean_inc(x_4);
x_211 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_207, x_209, x_4, x_5, x_6, x_7, x_210);
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
lean_inc(x_212);
x_214 = l_Lean_Expr_app___override(x_188, x_212);
x_215 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_214, x_4, x_5, x_6, x_7, x_213);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_217 = x_215;
} else {
 lean_dec_ref(x_215);
 x_217 = lean_box(0);
}
x_218 = l_Lean_Expr_mvarId_x21(x_212);
lean_dec(x_212);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_219 = l_Lean_MVarId_tryClear(x_218, x_3, x_4, x_5, x_6, x_7, x_216);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_220 = lean_ctor_get(x_219, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_219, 1);
lean_inc(x_221);
lean_dec(x_219);
lean_inc(x_46);
x_222 = l_Lean_Meta_getCtorNumPropFields(x_46, x_4, x_5, x_6, x_7, x_221);
if (lean_obj_tag(x_222) == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_222, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_225 = x_222;
} else {
 lean_dec_ref(x_222);
 x_225 = lean_box(0);
}
x_226 = lean_ctor_get(x_46, 4);
lean_inc(x_226);
lean_dec(x_46);
x_227 = lean_nat_sub(x_226, x_223);
lean_dec(x_223);
lean_dec(x_226);
if (lean_is_scalar(x_217)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_217;
 lean_ctor_set_tag(x_228, 1);
}
lean_ctor_set(x_228, 0, x_220);
lean_ctor_set(x_228, 1, x_227);
if (lean_is_scalar(x_225)) {
 x_229 = lean_alloc_ctor(0, 2, 0);
} else {
 x_229 = x_225;
}
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_224);
return x_229;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_220);
lean_dec(x_217);
lean_dec(x_46);
x_230 = lean_ctor_get(x_222, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_222, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_232 = x_222;
} else {
 lean_dec_ref(x_222);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_217);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_234 = lean_ctor_get(x_219, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_219, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_236 = x_219;
} else {
 lean_dec_ref(x_219);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; 
lean_dec(x_207);
lean_dec(x_188);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_238 = lean_ctor_get(x_208, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_208, 1);
lean_inc(x_239);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_240 = x_208;
} else {
 lean_dec_ref(x_208);
 x_240 = lean_box(0);
}
if (lean_is_scalar(x_240)) {
 x_241 = lean_alloc_ctor(1, 2, 0);
} else {
 x_241 = x_240;
}
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_239);
return x_241;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_204);
lean_dec(x_188);
lean_dec(x_46);
lean_dec(x_3);
x_242 = lean_ctor_get(x_203, 1);
lean_inc(x_242);
lean_dec(x_203);
x_243 = l_Lean_Meta_injectionCore___lambda__1___closed__17;
x_244 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_243, x_4, x_5, x_6, x_7, x_242);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_244;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; 
lean_dec(x_188);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_245 = lean_ctor_get(x_203, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_203, 1);
lean_inc(x_246);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_247 = x_203;
} else {
 lean_dec_ref(x_203);
 x_247 = lean_box(0);
}
if (lean_is_scalar(x_247)) {
 x_248 = lean_alloc_ctor(1, 2, 0);
} else {
 x_248 = x_247;
}
lean_ctor_set(x_248, 0, x_245);
lean_ctor_set(x_248, 1, x_246);
return x_248;
}
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_188);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_249 = lean_ctor_get(x_200, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_200, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 x_251 = x_200;
} else {
 lean_dec_ref(x_200);
 x_251 = lean_box(0);
}
if (lean_is_scalar(x_251)) {
 x_252 = lean_alloc_ctor(1, 2, 0);
} else {
 x_252 = x_251;
}
lean_ctor_set(x_252, 0, x_249);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_253 = lean_ctor_get(x_187, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_187, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_255 = x_187;
} else {
 lean_dec_ref(x_187);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
}
}
}
else
{
uint8_t x_257; 
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
x_257 = !lean_is_exclusive(x_36);
if (x_257 == 0)
{
return x_36;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_36, 0);
x_259 = lean_ctor_get(x_36, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_36);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
else
{
uint8_t x_261; 
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
x_261 = !lean_is_exclusive(x_33);
if (x_261 == 0)
{
return x_33;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_33, 0);
x_263 = lean_ctor_get(x_33, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_33);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
else
{
uint8_t x_265; 
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
x_265 = !lean_is_exclusive(x_30);
if (x_265 == 0)
{
return x_30;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_30, 0);
x_267 = lean_ctor_get(x_30, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_30);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_266);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_269 = l_Lean_Expr_appFn_x21(x_16);
x_270 = l_Lean_Expr_appFn_x21(x_269);
x_271 = l_Lean_Expr_appFn_x21(x_270);
x_272 = l_Lean_Expr_appArg_x21(x_271);
lean_dec(x_271);
x_273 = l_Lean_Expr_appArg_x21(x_270);
lean_dec(x_270);
x_274 = l_Lean_Expr_appArg_x21(x_269);
lean_dec(x_269);
x_275 = l_Lean_Expr_appArg_x21(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_274);
x_276 = l_Lean_Meta_isExprDefEq(x_272, x_274, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_276) == 0)
{
lean_object* x_277; uint8_t x_278; 
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_unbox(x_277);
lean_dec(x_277);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
lean_dec(x_273);
x_279 = lean_ctor_get(x_276, 1);
lean_inc(x_279);
lean_dec(x_276);
x_280 = l_Lean_Meta_injectionCore___lambda__1___closed__4;
x_281 = lean_unsigned_to_nat(3u);
x_282 = l_Lean_Expr_isAppOfArity(x_16, x_280, x_281);
lean_dec(x_16);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_18);
lean_dec(x_3);
x_283 = l_Lean_Meta_injectionCore___lambda__1___closed__8;
x_284 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_283, x_4, x_5, x_6, x_7, x_279);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_284;
}
else
{
lean_object* x_285; 
lean_inc(x_1);
x_285 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_279);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_288 = l_Lean_Meta_isConstructorApp_x27_x3f(x_274, x_4, x_5, x_6, x_7, x_287);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_291 = l_Lean_Meta_isConstructorApp_x27_x3f(x_275, x_4, x_5, x_6, x_7, x_290);
if (lean_obj_tag(x_291) == 0)
{
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_286);
lean_dec(x_18);
lean_dec(x_3);
x_292 = lean_ctor_get(x_291, 1);
lean_inc(x_292);
lean_dec(x_291);
x_293 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_294 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_293, x_4, x_5, x_6, x_7, x_292);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_294;
}
else
{
lean_object* x_295; 
x_295 = lean_ctor_get(x_291, 0);
lean_inc(x_295);
if (lean_obj_tag(x_295) == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_289);
lean_dec(x_286);
lean_dec(x_18);
lean_dec(x_3);
x_296 = lean_ctor_get(x_291, 1);
lean_inc(x_296);
lean_dec(x_291);
x_297 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_298 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_297, x_4, x_5, x_6, x_7, x_296);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_298;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint64_t x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
x_299 = lean_ctor_get(x_4, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_291, 1);
lean_inc(x_300);
lean_dec(x_291);
x_301 = lean_ctor_get(x_289, 0);
lean_inc(x_301);
lean_dec(x_289);
x_302 = lean_ctor_get(x_295, 0);
lean_inc(x_302);
lean_dec(x_295);
x_303 = lean_ctor_get_uint64(x_4, sizeof(void*)*6);
x_304 = lean_ctor_get(x_4, 1);
lean_inc(x_304);
x_305 = lean_ctor_get(x_4, 2);
lean_inc(x_305);
x_306 = lean_ctor_get(x_4, 3);
lean_inc(x_306);
x_307 = lean_ctor_get(x_4, 4);
lean_inc(x_307);
x_308 = lean_ctor_get(x_4, 5);
lean_inc(x_308);
x_309 = !lean_is_exclusive(x_299);
if (x_309 == 0)
{
uint8_t x_310; uint8_t x_311; uint8_t x_312; uint64_t x_313; uint64_t x_314; uint64_t x_315; uint64_t x_316; uint64_t x_317; lean_object* x_318; lean_object* x_319; 
x_310 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 8);
x_311 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 9);
x_312 = 1;
lean_ctor_set_uint8(x_299, 9, x_312);
x_313 = 2;
x_314 = lean_uint64_shift_right(x_303, x_313);
x_315 = lean_uint64_shift_left(x_314, x_313);
x_316 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_317 = lean_uint64_lor(x_315, x_316);
x_318 = lean_alloc_ctor(0, 6, 10);
lean_ctor_set(x_318, 0, x_299);
lean_ctor_set(x_318, 1, x_304);
lean_ctor_set(x_318, 2, x_305);
lean_ctor_set(x_318, 3, x_306);
lean_ctor_set(x_318, 4, x_307);
lean_ctor_set(x_318, 5, x_308);
lean_ctor_set_uint64(x_318, sizeof(void*)*6, x_317);
lean_ctor_set_uint8(x_318, sizeof(void*)*6 + 8, x_310);
lean_ctor_set_uint8(x_318, sizeof(void*)*6 + 9, x_311);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_319 = l_Lean_Meta_mkNoConfusion(x_286, x_18, x_318, x_5, x_6, x_7, x_300);
if (lean_obj_tag(x_319) == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; 
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_319, 1);
lean_inc(x_321);
lean_dec(x_319);
x_322 = lean_ctor_get(x_301, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_322, 0);
lean_inc(x_323);
lean_dec(x_322);
x_324 = lean_ctor_get(x_302, 0);
lean_inc(x_324);
lean_dec(x_302);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
lean_dec(x_324);
x_326 = lean_name_eq(x_323, x_325);
lean_dec(x_325);
lean_dec(x_323);
if (x_326 == 0)
{
lean_object* x_327; uint8_t x_328; 
lean_dec(x_301);
lean_dec(x_3);
lean_dec(x_2);
x_327 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_320, x_4, x_5, x_6, x_7, x_321);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_328 = !lean_is_exclusive(x_327);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_327, 0);
lean_dec(x_329);
x_330 = lean_box(0);
lean_ctor_set(x_327, 0, x_330);
return x_327;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; 
x_331 = lean_ctor_get(x_327, 1);
lean_inc(x_331);
lean_dec(x_327);
x_332 = lean_box(0);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_332);
lean_ctor_set(x_333, 1, x_331);
return x_333;
}
}
else
{
lean_object* x_334; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_320);
x_334 = lean_infer_type(x_320, x_4, x_5, x_6, x_7, x_321);
if (lean_obj_tag(x_334) == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
x_335 = lean_ctor_get(x_334, 0);
lean_inc(x_335);
x_336 = lean_ctor_get(x_334, 1);
lean_inc(x_336);
lean_dec(x_334);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_337 = l_Lean_Meta_whnfD(x_335, x_4, x_5, x_6, x_7, x_336);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
if (lean_obj_tag(x_338) == 7)
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
lean_dec(x_2);
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = lean_ctor_get(x_338, 1);
lean_inc(x_340);
lean_dec(x_338);
x_341 = l_Lean_Expr_headBeta(x_340);
lean_inc(x_1);
x_342 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_339);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; uint8_t x_350; 
x_343 = lean_ctor_get(x_342, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_342, 1);
lean_inc(x_344);
lean_dec(x_342);
lean_inc(x_4);
x_345 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_341, x_343, x_4, x_5, x_6, x_7, x_344);
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
lean_inc(x_346);
x_348 = l_Lean_Expr_app___override(x_320, x_346);
x_349 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_348, x_4, x_5, x_6, x_7, x_347);
x_350 = !lean_is_exclusive(x_349);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; 
x_351 = lean_ctor_get(x_349, 1);
x_352 = lean_ctor_get(x_349, 0);
lean_dec(x_352);
x_353 = l_Lean_Expr_mvarId_x21(x_346);
lean_dec(x_346);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_354 = l_Lean_MVarId_tryClear(x_353, x_3, x_4, x_5, x_6, x_7, x_351);
if (lean_obj_tag(x_354) == 0)
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_354, 1);
lean_inc(x_356);
lean_dec(x_354);
lean_inc(x_301);
x_357 = l_Lean_Meta_getCtorNumPropFields(x_301, x_4, x_5, x_6, x_7, x_356);
if (lean_obj_tag(x_357) == 0)
{
uint8_t x_358; 
x_358 = !lean_is_exclusive(x_357);
if (x_358 == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_357, 0);
x_360 = lean_ctor_get(x_301, 4);
lean_inc(x_360);
lean_dec(x_301);
x_361 = lean_nat_sub(x_360, x_359);
lean_dec(x_359);
lean_dec(x_360);
lean_ctor_set_tag(x_349, 1);
lean_ctor_set(x_349, 1, x_361);
lean_ctor_set(x_349, 0, x_355);
lean_ctor_set(x_357, 0, x_349);
return x_357;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_362 = lean_ctor_get(x_357, 0);
x_363 = lean_ctor_get(x_357, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_357);
x_364 = lean_ctor_get(x_301, 4);
lean_inc(x_364);
lean_dec(x_301);
x_365 = lean_nat_sub(x_364, x_362);
lean_dec(x_362);
lean_dec(x_364);
lean_ctor_set_tag(x_349, 1);
lean_ctor_set(x_349, 1, x_365);
lean_ctor_set(x_349, 0, x_355);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_349);
lean_ctor_set(x_366, 1, x_363);
return x_366;
}
}
else
{
uint8_t x_367; 
lean_dec(x_355);
lean_free_object(x_349);
lean_dec(x_301);
x_367 = !lean_is_exclusive(x_357);
if (x_367 == 0)
{
return x_357;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_357, 0);
x_369 = lean_ctor_get(x_357, 1);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_357);
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
return x_370;
}
}
}
else
{
uint8_t x_371; 
lean_free_object(x_349);
lean_dec(x_301);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_371 = !lean_is_exclusive(x_354);
if (x_371 == 0)
{
return x_354;
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_372 = lean_ctor_get(x_354, 0);
x_373 = lean_ctor_get(x_354, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_354);
x_374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
return x_374;
}
}
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_349, 1);
lean_inc(x_375);
lean_dec(x_349);
x_376 = l_Lean_Expr_mvarId_x21(x_346);
lean_dec(x_346);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_377 = l_Lean_MVarId_tryClear(x_376, x_3, x_4, x_5, x_6, x_7, x_375);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
lean_inc(x_301);
x_380 = l_Lean_Meta_getCtorNumPropFields(x_301, x_4, x_5, x_6, x_7, x_379);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_383 = x_380;
} else {
 lean_dec_ref(x_380);
 x_383 = lean_box(0);
}
x_384 = lean_ctor_get(x_301, 4);
lean_inc(x_384);
lean_dec(x_301);
x_385 = lean_nat_sub(x_384, x_381);
lean_dec(x_381);
lean_dec(x_384);
x_386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_386, 0, x_378);
lean_ctor_set(x_386, 1, x_385);
if (lean_is_scalar(x_383)) {
 x_387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_387 = x_383;
}
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_382);
return x_387;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_378);
lean_dec(x_301);
x_388 = lean_ctor_get(x_380, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_380, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_390 = x_380;
} else {
 lean_dec_ref(x_380);
 x_390 = lean_box(0);
}
if (lean_is_scalar(x_390)) {
 x_391 = lean_alloc_ctor(1, 2, 0);
} else {
 x_391 = x_390;
}
lean_ctor_set(x_391, 0, x_388);
lean_ctor_set(x_391, 1, x_389);
return x_391;
}
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_301);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_392 = lean_ctor_get(x_377, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_377, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_394 = x_377;
} else {
 lean_dec_ref(x_377);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 2, 0);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_392);
lean_ctor_set(x_395, 1, x_393);
return x_395;
}
}
}
else
{
uint8_t x_396; 
lean_dec(x_341);
lean_dec(x_320);
lean_dec(x_301);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_396 = !lean_is_exclusive(x_342);
if (x_396 == 0)
{
return x_342;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; 
x_397 = lean_ctor_get(x_342, 0);
x_398 = lean_ctor_get(x_342, 1);
lean_inc(x_398);
lean_inc(x_397);
lean_dec(x_342);
x_399 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_399, 0, x_397);
lean_ctor_set(x_399, 1, x_398);
return x_399;
}
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_338);
lean_dec(x_320);
lean_dec(x_301);
lean_dec(x_3);
x_400 = lean_ctor_get(x_337, 1);
lean_inc(x_400);
lean_dec(x_337);
x_401 = l_Lean_Meta_injectionCore___lambda__1___closed__17;
x_402 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_401, x_4, x_5, x_6, x_7, x_400);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_402;
}
}
else
{
uint8_t x_403; 
lean_dec(x_320);
lean_dec(x_301);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_403 = !lean_is_exclusive(x_337);
if (x_403 == 0)
{
return x_337;
}
else
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_337, 0);
x_405 = lean_ctor_get(x_337, 1);
lean_inc(x_405);
lean_inc(x_404);
lean_dec(x_337);
x_406 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_406, 0, x_404);
lean_ctor_set(x_406, 1, x_405);
return x_406;
}
}
}
else
{
uint8_t x_407; 
lean_dec(x_320);
lean_dec(x_301);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_407 = !lean_is_exclusive(x_334);
if (x_407 == 0)
{
return x_334;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_334, 0);
x_409 = lean_ctor_get(x_334, 1);
lean_inc(x_409);
lean_inc(x_408);
lean_dec(x_334);
x_410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
return x_410;
}
}
}
}
else
{
uint8_t x_411; 
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_411 = !lean_is_exclusive(x_319);
if (x_411 == 0)
{
return x_319;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; 
x_412 = lean_ctor_get(x_319, 0);
x_413 = lean_ctor_get(x_319, 1);
lean_inc(x_413);
lean_inc(x_412);
lean_dec(x_319);
x_414 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_414, 0, x_412);
lean_ctor_set(x_414, 1, x_413);
return x_414;
}
}
}
else
{
uint8_t x_415; uint8_t x_416; uint8_t x_417; uint8_t x_418; uint8_t x_419; uint8_t x_420; uint8_t x_421; uint8_t x_422; uint8_t x_423; uint8_t x_424; uint8_t x_425; uint8_t x_426; uint8_t x_427; uint8_t x_428; uint8_t x_429; uint8_t x_430; uint8_t x_431; uint8_t x_432; uint8_t x_433; uint8_t x_434; lean_object* x_435; uint64_t x_436; uint64_t x_437; uint64_t x_438; uint64_t x_439; uint64_t x_440; lean_object* x_441; lean_object* x_442; 
x_415 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 8);
x_416 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 9);
x_417 = lean_ctor_get_uint8(x_299, 0);
x_418 = lean_ctor_get_uint8(x_299, 1);
x_419 = lean_ctor_get_uint8(x_299, 2);
x_420 = lean_ctor_get_uint8(x_299, 3);
x_421 = lean_ctor_get_uint8(x_299, 4);
x_422 = lean_ctor_get_uint8(x_299, 5);
x_423 = lean_ctor_get_uint8(x_299, 6);
x_424 = lean_ctor_get_uint8(x_299, 7);
x_425 = lean_ctor_get_uint8(x_299, 8);
x_426 = lean_ctor_get_uint8(x_299, 10);
x_427 = lean_ctor_get_uint8(x_299, 11);
x_428 = lean_ctor_get_uint8(x_299, 12);
x_429 = lean_ctor_get_uint8(x_299, 13);
x_430 = lean_ctor_get_uint8(x_299, 14);
x_431 = lean_ctor_get_uint8(x_299, 15);
x_432 = lean_ctor_get_uint8(x_299, 16);
x_433 = lean_ctor_get_uint8(x_299, 17);
lean_dec(x_299);
x_434 = 1;
x_435 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_435, 0, x_417);
lean_ctor_set_uint8(x_435, 1, x_418);
lean_ctor_set_uint8(x_435, 2, x_419);
lean_ctor_set_uint8(x_435, 3, x_420);
lean_ctor_set_uint8(x_435, 4, x_421);
lean_ctor_set_uint8(x_435, 5, x_422);
lean_ctor_set_uint8(x_435, 6, x_423);
lean_ctor_set_uint8(x_435, 7, x_424);
lean_ctor_set_uint8(x_435, 8, x_425);
lean_ctor_set_uint8(x_435, 9, x_434);
lean_ctor_set_uint8(x_435, 10, x_426);
lean_ctor_set_uint8(x_435, 11, x_427);
lean_ctor_set_uint8(x_435, 12, x_428);
lean_ctor_set_uint8(x_435, 13, x_429);
lean_ctor_set_uint8(x_435, 14, x_430);
lean_ctor_set_uint8(x_435, 15, x_431);
lean_ctor_set_uint8(x_435, 16, x_432);
lean_ctor_set_uint8(x_435, 17, x_433);
x_436 = 2;
x_437 = lean_uint64_shift_right(x_303, x_436);
x_438 = lean_uint64_shift_left(x_437, x_436);
x_439 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_440 = lean_uint64_lor(x_438, x_439);
x_441 = lean_alloc_ctor(0, 6, 10);
lean_ctor_set(x_441, 0, x_435);
lean_ctor_set(x_441, 1, x_304);
lean_ctor_set(x_441, 2, x_305);
lean_ctor_set(x_441, 3, x_306);
lean_ctor_set(x_441, 4, x_307);
lean_ctor_set(x_441, 5, x_308);
lean_ctor_set_uint64(x_441, sizeof(void*)*6, x_440);
lean_ctor_set_uint8(x_441, sizeof(void*)*6 + 8, x_415);
lean_ctor_set_uint8(x_441, sizeof(void*)*6 + 9, x_416);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_442 = l_Lean_Meta_mkNoConfusion(x_286, x_18, x_441, x_5, x_6, x_7, x_300);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
x_445 = lean_ctor_get(x_301, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
lean_dec(x_445);
x_447 = lean_ctor_get(x_302, 0);
lean_inc(x_447);
lean_dec(x_302);
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
lean_dec(x_447);
x_449 = lean_name_eq(x_446, x_448);
lean_dec(x_448);
lean_dec(x_446);
if (x_449 == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
lean_dec(x_301);
lean_dec(x_3);
lean_dec(x_2);
x_450 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_443, x_4, x_5, x_6, x_7, x_444);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_451 = lean_ctor_get(x_450, 1);
lean_inc(x_451);
if (lean_is_exclusive(x_450)) {
 lean_ctor_release(x_450, 0);
 lean_ctor_release(x_450, 1);
 x_452 = x_450;
} else {
 lean_dec_ref(x_450);
 x_452 = lean_box(0);
}
x_453 = lean_box(0);
if (lean_is_scalar(x_452)) {
 x_454 = lean_alloc_ctor(0, 2, 0);
} else {
 x_454 = x_452;
}
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_451);
return x_454;
}
else
{
lean_object* x_455; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_443);
x_455 = lean_infer_type(x_443, x_4, x_5, x_6, x_7, x_444);
if (lean_obj_tag(x_455) == 0)
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_456 = lean_ctor_get(x_455, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_455, 1);
lean_inc(x_457);
lean_dec(x_455);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_458 = l_Lean_Meta_whnfD(x_456, x_4, x_5, x_6, x_7, x_457);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; 
x_459 = lean_ctor_get(x_458, 0);
lean_inc(x_459);
if (lean_obj_tag(x_459) == 7)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_2);
x_460 = lean_ctor_get(x_458, 1);
lean_inc(x_460);
lean_dec(x_458);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
lean_dec(x_459);
x_462 = l_Lean_Expr_headBeta(x_461);
lean_inc(x_1);
x_463 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_460);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_464 = lean_ctor_get(x_463, 0);
lean_inc(x_464);
x_465 = lean_ctor_get(x_463, 1);
lean_inc(x_465);
lean_dec(x_463);
lean_inc(x_4);
x_466 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_462, x_464, x_4, x_5, x_6, x_7, x_465);
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_466, 1);
lean_inc(x_468);
lean_dec(x_466);
lean_inc(x_467);
x_469 = l_Lean_Expr_app___override(x_443, x_467);
x_470 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_469, x_4, x_5, x_6, x_7, x_468);
x_471 = lean_ctor_get(x_470, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_470)) {
 lean_ctor_release(x_470, 0);
 lean_ctor_release(x_470, 1);
 x_472 = x_470;
} else {
 lean_dec_ref(x_470);
 x_472 = lean_box(0);
}
x_473 = l_Lean_Expr_mvarId_x21(x_467);
lean_dec(x_467);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_474 = l_Lean_MVarId_tryClear(x_473, x_3, x_4, x_5, x_6, x_7, x_471);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_474, 1);
lean_inc(x_476);
lean_dec(x_474);
lean_inc(x_301);
x_477 = l_Lean_Meta_getCtorNumPropFields(x_301, x_4, x_5, x_6, x_7, x_476);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_477, 1);
lean_inc(x_479);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 x_480 = x_477;
} else {
 lean_dec_ref(x_477);
 x_480 = lean_box(0);
}
x_481 = lean_ctor_get(x_301, 4);
lean_inc(x_481);
lean_dec(x_301);
x_482 = lean_nat_sub(x_481, x_478);
lean_dec(x_478);
lean_dec(x_481);
if (lean_is_scalar(x_472)) {
 x_483 = lean_alloc_ctor(1, 2, 0);
} else {
 x_483 = x_472;
 lean_ctor_set_tag(x_483, 1);
}
lean_ctor_set(x_483, 0, x_475);
lean_ctor_set(x_483, 1, x_482);
if (lean_is_scalar(x_480)) {
 x_484 = lean_alloc_ctor(0, 2, 0);
} else {
 x_484 = x_480;
}
lean_ctor_set(x_484, 0, x_483);
lean_ctor_set(x_484, 1, x_479);
return x_484;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_475);
lean_dec(x_472);
lean_dec(x_301);
x_485 = lean_ctor_get(x_477, 0);
lean_inc(x_485);
x_486 = lean_ctor_get(x_477, 1);
lean_inc(x_486);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 x_487 = x_477;
} else {
 lean_dec_ref(x_477);
 x_487 = lean_box(0);
}
if (lean_is_scalar(x_487)) {
 x_488 = lean_alloc_ctor(1, 2, 0);
} else {
 x_488 = x_487;
}
lean_ctor_set(x_488, 0, x_485);
lean_ctor_set(x_488, 1, x_486);
return x_488;
}
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_472);
lean_dec(x_301);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_489 = lean_ctor_get(x_474, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_474, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_491 = x_474;
} else {
 lean_dec_ref(x_474);
 x_491 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_492 = lean_alloc_ctor(1, 2, 0);
} else {
 x_492 = x_491;
}
lean_ctor_set(x_492, 0, x_489);
lean_ctor_set(x_492, 1, x_490);
return x_492;
}
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_462);
lean_dec(x_443);
lean_dec(x_301);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_493 = lean_ctor_get(x_463, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_463, 1);
lean_inc(x_494);
if (lean_is_exclusive(x_463)) {
 lean_ctor_release(x_463, 0);
 lean_ctor_release(x_463, 1);
 x_495 = x_463;
} else {
 lean_dec_ref(x_463);
 x_495 = lean_box(0);
}
if (lean_is_scalar(x_495)) {
 x_496 = lean_alloc_ctor(1, 2, 0);
} else {
 x_496 = x_495;
}
lean_ctor_set(x_496, 0, x_493);
lean_ctor_set(x_496, 1, x_494);
return x_496;
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; 
lean_dec(x_459);
lean_dec(x_443);
lean_dec(x_301);
lean_dec(x_3);
x_497 = lean_ctor_get(x_458, 1);
lean_inc(x_497);
lean_dec(x_458);
x_498 = l_Lean_Meta_injectionCore___lambda__1___closed__17;
x_499 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_498, x_4, x_5, x_6, x_7, x_497);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_499;
}
}
else
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
lean_dec(x_443);
lean_dec(x_301);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_500 = lean_ctor_get(x_458, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_458, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_502 = x_458;
} else {
 lean_dec_ref(x_458);
 x_502 = lean_box(0);
}
if (lean_is_scalar(x_502)) {
 x_503 = lean_alloc_ctor(1, 2, 0);
} else {
 x_503 = x_502;
}
lean_ctor_set(x_503, 0, x_500);
lean_ctor_set(x_503, 1, x_501);
return x_503;
}
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_443);
lean_dec(x_301);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_504 = lean_ctor_get(x_455, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_455, 1);
lean_inc(x_505);
if (lean_is_exclusive(x_455)) {
 lean_ctor_release(x_455, 0);
 lean_ctor_release(x_455, 1);
 x_506 = x_455;
} else {
 lean_dec_ref(x_455);
 x_506 = lean_box(0);
}
if (lean_is_scalar(x_506)) {
 x_507 = lean_alloc_ctor(1, 2, 0);
} else {
 x_507 = x_506;
}
lean_ctor_set(x_507, 0, x_504);
lean_ctor_set(x_507, 1, x_505);
return x_507;
}
}
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; 
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_508 = lean_ctor_get(x_442, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_442, 1);
lean_inc(x_509);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_510 = x_442;
} else {
 lean_dec_ref(x_442);
 x_510 = lean_box(0);
}
if (lean_is_scalar(x_510)) {
 x_511 = lean_alloc_ctor(1, 2, 0);
} else {
 x_511 = x_510;
}
lean_ctor_set(x_511, 0, x_508);
lean_ctor_set(x_511, 1, x_509);
return x_511;
}
}
}
}
}
else
{
uint8_t x_512; 
lean_dec(x_289);
lean_dec(x_286);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_512 = !lean_is_exclusive(x_291);
if (x_512 == 0)
{
return x_291;
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_513 = lean_ctor_get(x_291, 0);
x_514 = lean_ctor_get(x_291, 1);
lean_inc(x_514);
lean_inc(x_513);
lean_dec(x_291);
x_515 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_515, 0, x_513);
lean_ctor_set(x_515, 1, x_514);
return x_515;
}
}
}
else
{
uint8_t x_516; 
lean_dec(x_286);
lean_dec(x_275);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_516 = !lean_is_exclusive(x_288);
if (x_516 == 0)
{
return x_288;
}
else
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; 
x_517 = lean_ctor_get(x_288, 0);
x_518 = lean_ctor_get(x_288, 1);
lean_inc(x_518);
lean_inc(x_517);
lean_dec(x_288);
x_519 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_519, 0, x_517);
lean_ctor_set(x_519, 1, x_518);
return x_519;
}
}
}
else
{
uint8_t x_520; 
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_520 = !lean_is_exclusive(x_285);
if (x_520 == 0)
{
return x_285;
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_521 = lean_ctor_get(x_285, 0);
x_522 = lean_ctor_get(x_285, 1);
lean_inc(x_522);
lean_inc(x_521);
lean_dec(x_285);
x_523 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_523, 0, x_521);
lean_ctor_set(x_523, 1, x_522);
return x_523;
}
}
}
}
else
{
lean_object* x_524; lean_object* x_525; 
lean_dec(x_274);
lean_dec(x_16);
x_524 = lean_ctor_get(x_276, 1);
lean_inc(x_524);
lean_dec(x_276);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_525 = l_Lean_Meta_mkEq(x_273, x_275, x_4, x_5, x_6, x_7, x_524);
if (lean_obj_tag(x_525) == 0)
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; 
x_526 = lean_ctor_get(x_525, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_525, 1);
lean_inc(x_527);
lean_dec(x_525);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_528 = l_Lean_Meta_mkEqOfHEq(x_18, x_4, x_5, x_6, x_7, x_527);
if (lean_obj_tag(x_528) == 0)
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; uint8_t x_533; 
x_529 = lean_ctor_get(x_528, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_528, 1);
lean_inc(x_530);
lean_dec(x_528);
x_531 = l_Lean_Meta_injectionCore___lambda__1___closed__4;
x_532 = lean_unsigned_to_nat(3u);
x_533 = l_Lean_Expr_isAppOfArity(x_526, x_531, x_532);
if (x_533 == 0)
{
lean_object* x_534; lean_object* x_535; 
lean_dec(x_529);
lean_dec(x_526);
lean_dec(x_3);
x_534 = l_Lean_Meta_injectionCore___lambda__1___closed__8;
x_535 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_534, x_4, x_5, x_6, x_7, x_530);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_535;
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_536 = l_Lean_Expr_appFn_x21(x_526);
x_537 = l_Lean_Expr_appArg_x21(x_536);
lean_dec(x_536);
x_538 = l_Lean_Expr_appArg_x21(x_526);
lean_dec(x_526);
lean_inc(x_1);
x_539 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_530);
if (lean_obj_tag(x_539) == 0)
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_540 = lean_ctor_get(x_539, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_539, 1);
lean_inc(x_541);
lean_dec(x_539);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_542 = l_Lean_Meta_isConstructorApp_x27_x3f(x_537, x_4, x_5, x_6, x_7, x_541);
if (lean_obj_tag(x_542) == 0)
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_543 = lean_ctor_get(x_542, 0);
lean_inc(x_543);
x_544 = lean_ctor_get(x_542, 1);
lean_inc(x_544);
lean_dec(x_542);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_545 = l_Lean_Meta_isConstructorApp_x27_x3f(x_538, x_4, x_5, x_6, x_7, x_544);
if (lean_obj_tag(x_545) == 0)
{
if (lean_obj_tag(x_543) == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_dec(x_540);
lean_dec(x_529);
lean_dec(x_3);
x_546 = lean_ctor_get(x_545, 1);
lean_inc(x_546);
lean_dec(x_545);
x_547 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_548 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_547, x_4, x_5, x_6, x_7, x_546);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_548;
}
else
{
lean_object* x_549; 
x_549 = lean_ctor_get(x_545, 0);
lean_inc(x_549);
if (lean_obj_tag(x_549) == 0)
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_543);
lean_dec(x_540);
lean_dec(x_529);
lean_dec(x_3);
x_550 = lean_ctor_get(x_545, 1);
lean_inc(x_550);
lean_dec(x_545);
x_551 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_552 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_551, x_4, x_5, x_6, x_7, x_550);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_552;
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; uint64_t x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; uint8_t x_563; 
x_553 = lean_ctor_get(x_4, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_545, 1);
lean_inc(x_554);
lean_dec(x_545);
x_555 = lean_ctor_get(x_543, 0);
lean_inc(x_555);
lean_dec(x_543);
x_556 = lean_ctor_get(x_549, 0);
lean_inc(x_556);
lean_dec(x_549);
x_557 = lean_ctor_get_uint64(x_4, sizeof(void*)*6);
x_558 = lean_ctor_get(x_4, 1);
lean_inc(x_558);
x_559 = lean_ctor_get(x_4, 2);
lean_inc(x_559);
x_560 = lean_ctor_get(x_4, 3);
lean_inc(x_560);
x_561 = lean_ctor_get(x_4, 4);
lean_inc(x_561);
x_562 = lean_ctor_get(x_4, 5);
lean_inc(x_562);
x_563 = !lean_is_exclusive(x_553);
if (x_563 == 0)
{
uint8_t x_564; uint8_t x_565; uint8_t x_566; uint64_t x_567; uint64_t x_568; uint64_t x_569; uint64_t x_570; uint64_t x_571; lean_object* x_572; lean_object* x_573; 
x_564 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 8);
x_565 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 9);
x_566 = 1;
lean_ctor_set_uint8(x_553, 9, x_566);
x_567 = 2;
x_568 = lean_uint64_shift_right(x_557, x_567);
x_569 = lean_uint64_shift_left(x_568, x_567);
x_570 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_571 = lean_uint64_lor(x_569, x_570);
x_572 = lean_alloc_ctor(0, 6, 10);
lean_ctor_set(x_572, 0, x_553);
lean_ctor_set(x_572, 1, x_558);
lean_ctor_set(x_572, 2, x_559);
lean_ctor_set(x_572, 3, x_560);
lean_ctor_set(x_572, 4, x_561);
lean_ctor_set(x_572, 5, x_562);
lean_ctor_set_uint64(x_572, sizeof(void*)*6, x_571);
lean_ctor_set_uint8(x_572, sizeof(void*)*6 + 8, x_564);
lean_ctor_set_uint8(x_572, sizeof(void*)*6 + 9, x_565);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_573 = l_Lean_Meta_mkNoConfusion(x_540, x_529, x_572, x_5, x_6, x_7, x_554);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; uint8_t x_580; 
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
lean_dec(x_573);
x_576 = lean_ctor_get(x_555, 0);
lean_inc(x_576);
x_577 = lean_ctor_get(x_576, 0);
lean_inc(x_577);
lean_dec(x_576);
x_578 = lean_ctor_get(x_556, 0);
lean_inc(x_578);
lean_dec(x_556);
x_579 = lean_ctor_get(x_578, 0);
lean_inc(x_579);
lean_dec(x_578);
x_580 = lean_name_eq(x_577, x_579);
lean_dec(x_579);
lean_dec(x_577);
if (x_580 == 0)
{
lean_object* x_581; uint8_t x_582; 
lean_dec(x_555);
lean_dec(x_3);
lean_dec(x_2);
x_581 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_574, x_4, x_5, x_6, x_7, x_575);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_582 = !lean_is_exclusive(x_581);
if (x_582 == 0)
{
lean_object* x_583; lean_object* x_584; 
x_583 = lean_ctor_get(x_581, 0);
lean_dec(x_583);
x_584 = lean_box(0);
lean_ctor_set(x_581, 0, x_584);
return x_581;
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_585 = lean_ctor_get(x_581, 1);
lean_inc(x_585);
lean_dec(x_581);
x_586 = lean_box(0);
x_587 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_587, 0, x_586);
lean_ctor_set(x_587, 1, x_585);
return x_587;
}
}
else
{
lean_object* x_588; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_574);
x_588 = lean_infer_type(x_574, x_4, x_5, x_6, x_7, x_575);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_588, 1);
lean_inc(x_590);
lean_dec(x_588);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_591 = l_Lean_Meta_whnfD(x_589, x_4, x_5, x_6, x_7, x_590);
if (lean_obj_tag(x_591) == 0)
{
lean_object* x_592; 
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
if (lean_obj_tag(x_592) == 7)
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; 
lean_dec(x_2);
x_593 = lean_ctor_get(x_591, 1);
lean_inc(x_593);
lean_dec(x_591);
x_594 = lean_ctor_get(x_592, 1);
lean_inc(x_594);
lean_dec(x_592);
x_595 = l_Lean_Expr_headBeta(x_594);
lean_inc(x_1);
x_596 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_593);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; uint8_t x_604; 
x_597 = lean_ctor_get(x_596, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_596, 1);
lean_inc(x_598);
lean_dec(x_596);
lean_inc(x_4);
x_599 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_595, x_597, x_4, x_5, x_6, x_7, x_598);
x_600 = lean_ctor_get(x_599, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_599, 1);
lean_inc(x_601);
lean_dec(x_599);
lean_inc(x_600);
x_602 = l_Lean_Expr_app___override(x_574, x_600);
x_603 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_602, x_4, x_5, x_6, x_7, x_601);
x_604 = !lean_is_exclusive(x_603);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_605 = lean_ctor_get(x_603, 1);
x_606 = lean_ctor_get(x_603, 0);
lean_dec(x_606);
x_607 = l_Lean_Expr_mvarId_x21(x_600);
lean_dec(x_600);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_608 = l_Lean_MVarId_tryClear(x_607, x_3, x_4, x_5, x_6, x_7, x_605);
if (lean_obj_tag(x_608) == 0)
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_608, 1);
lean_inc(x_610);
lean_dec(x_608);
lean_inc(x_555);
x_611 = l_Lean_Meta_getCtorNumPropFields(x_555, x_4, x_5, x_6, x_7, x_610);
if (lean_obj_tag(x_611) == 0)
{
uint8_t x_612; 
x_612 = !lean_is_exclusive(x_611);
if (x_612 == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_613 = lean_ctor_get(x_611, 0);
x_614 = lean_ctor_get(x_555, 4);
lean_inc(x_614);
lean_dec(x_555);
x_615 = lean_nat_sub(x_614, x_613);
lean_dec(x_613);
lean_dec(x_614);
lean_ctor_set_tag(x_603, 1);
lean_ctor_set(x_603, 1, x_615);
lean_ctor_set(x_603, 0, x_609);
lean_ctor_set(x_611, 0, x_603);
return x_611;
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_616 = lean_ctor_get(x_611, 0);
x_617 = lean_ctor_get(x_611, 1);
lean_inc(x_617);
lean_inc(x_616);
lean_dec(x_611);
x_618 = lean_ctor_get(x_555, 4);
lean_inc(x_618);
lean_dec(x_555);
x_619 = lean_nat_sub(x_618, x_616);
lean_dec(x_616);
lean_dec(x_618);
lean_ctor_set_tag(x_603, 1);
lean_ctor_set(x_603, 1, x_619);
lean_ctor_set(x_603, 0, x_609);
x_620 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_620, 0, x_603);
lean_ctor_set(x_620, 1, x_617);
return x_620;
}
}
else
{
uint8_t x_621; 
lean_dec(x_609);
lean_free_object(x_603);
lean_dec(x_555);
x_621 = !lean_is_exclusive(x_611);
if (x_621 == 0)
{
return x_611;
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; 
x_622 = lean_ctor_get(x_611, 0);
x_623 = lean_ctor_get(x_611, 1);
lean_inc(x_623);
lean_inc(x_622);
lean_dec(x_611);
x_624 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_624, 0, x_622);
lean_ctor_set(x_624, 1, x_623);
return x_624;
}
}
}
else
{
uint8_t x_625; 
lean_free_object(x_603);
lean_dec(x_555);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_625 = !lean_is_exclusive(x_608);
if (x_625 == 0)
{
return x_608;
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_626 = lean_ctor_get(x_608, 0);
x_627 = lean_ctor_get(x_608, 1);
lean_inc(x_627);
lean_inc(x_626);
lean_dec(x_608);
x_628 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_628, 0, x_626);
lean_ctor_set(x_628, 1, x_627);
return x_628;
}
}
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; 
x_629 = lean_ctor_get(x_603, 1);
lean_inc(x_629);
lean_dec(x_603);
x_630 = l_Lean_Expr_mvarId_x21(x_600);
lean_dec(x_600);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_631 = l_Lean_MVarId_tryClear(x_630, x_3, x_4, x_5, x_6, x_7, x_629);
if (lean_obj_tag(x_631) == 0)
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_632 = lean_ctor_get(x_631, 0);
lean_inc(x_632);
x_633 = lean_ctor_get(x_631, 1);
lean_inc(x_633);
lean_dec(x_631);
lean_inc(x_555);
x_634 = l_Lean_Meta_getCtorNumPropFields(x_555, x_4, x_5, x_6, x_7, x_633);
if (lean_obj_tag(x_634) == 0)
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_635 = lean_ctor_get(x_634, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_634, 1);
lean_inc(x_636);
if (lean_is_exclusive(x_634)) {
 lean_ctor_release(x_634, 0);
 lean_ctor_release(x_634, 1);
 x_637 = x_634;
} else {
 lean_dec_ref(x_634);
 x_637 = lean_box(0);
}
x_638 = lean_ctor_get(x_555, 4);
lean_inc(x_638);
lean_dec(x_555);
x_639 = lean_nat_sub(x_638, x_635);
lean_dec(x_635);
lean_dec(x_638);
x_640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_640, 0, x_632);
lean_ctor_set(x_640, 1, x_639);
if (lean_is_scalar(x_637)) {
 x_641 = lean_alloc_ctor(0, 2, 0);
} else {
 x_641 = x_637;
}
lean_ctor_set(x_641, 0, x_640);
lean_ctor_set(x_641, 1, x_636);
return x_641;
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; 
lean_dec(x_632);
lean_dec(x_555);
x_642 = lean_ctor_get(x_634, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_634, 1);
lean_inc(x_643);
if (lean_is_exclusive(x_634)) {
 lean_ctor_release(x_634, 0);
 lean_ctor_release(x_634, 1);
 x_644 = x_634;
} else {
 lean_dec_ref(x_634);
 x_644 = lean_box(0);
}
if (lean_is_scalar(x_644)) {
 x_645 = lean_alloc_ctor(1, 2, 0);
} else {
 x_645 = x_644;
}
lean_ctor_set(x_645, 0, x_642);
lean_ctor_set(x_645, 1, x_643);
return x_645;
}
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; 
lean_dec(x_555);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_646 = lean_ctor_get(x_631, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_631, 1);
lean_inc(x_647);
if (lean_is_exclusive(x_631)) {
 lean_ctor_release(x_631, 0);
 lean_ctor_release(x_631, 1);
 x_648 = x_631;
} else {
 lean_dec_ref(x_631);
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
}
else
{
uint8_t x_650; 
lean_dec(x_595);
lean_dec(x_574);
lean_dec(x_555);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_650 = !lean_is_exclusive(x_596);
if (x_650 == 0)
{
return x_596;
}
else
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_651 = lean_ctor_get(x_596, 0);
x_652 = lean_ctor_get(x_596, 1);
lean_inc(x_652);
lean_inc(x_651);
lean_dec(x_596);
x_653 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_653, 0, x_651);
lean_ctor_set(x_653, 1, x_652);
return x_653;
}
}
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; 
lean_dec(x_592);
lean_dec(x_574);
lean_dec(x_555);
lean_dec(x_3);
x_654 = lean_ctor_get(x_591, 1);
lean_inc(x_654);
lean_dec(x_591);
x_655 = l_Lean_Meta_injectionCore___lambda__1___closed__17;
x_656 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_655, x_4, x_5, x_6, x_7, x_654);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_656;
}
}
else
{
uint8_t x_657; 
lean_dec(x_574);
lean_dec(x_555);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_657 = !lean_is_exclusive(x_591);
if (x_657 == 0)
{
return x_591;
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_658 = lean_ctor_get(x_591, 0);
x_659 = lean_ctor_get(x_591, 1);
lean_inc(x_659);
lean_inc(x_658);
lean_dec(x_591);
x_660 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_660, 0, x_658);
lean_ctor_set(x_660, 1, x_659);
return x_660;
}
}
}
else
{
uint8_t x_661; 
lean_dec(x_574);
lean_dec(x_555);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_661 = !lean_is_exclusive(x_588);
if (x_661 == 0)
{
return x_588;
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_662 = lean_ctor_get(x_588, 0);
x_663 = lean_ctor_get(x_588, 1);
lean_inc(x_663);
lean_inc(x_662);
lean_dec(x_588);
x_664 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_664, 0, x_662);
lean_ctor_set(x_664, 1, x_663);
return x_664;
}
}
}
}
else
{
uint8_t x_665; 
lean_dec(x_556);
lean_dec(x_555);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_665 = !lean_is_exclusive(x_573);
if (x_665 == 0)
{
return x_573;
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_666 = lean_ctor_get(x_573, 0);
x_667 = lean_ctor_get(x_573, 1);
lean_inc(x_667);
lean_inc(x_666);
lean_dec(x_573);
x_668 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_668, 0, x_666);
lean_ctor_set(x_668, 1, x_667);
return x_668;
}
}
}
else
{
uint8_t x_669; uint8_t x_670; uint8_t x_671; uint8_t x_672; uint8_t x_673; uint8_t x_674; uint8_t x_675; uint8_t x_676; uint8_t x_677; uint8_t x_678; uint8_t x_679; uint8_t x_680; uint8_t x_681; uint8_t x_682; uint8_t x_683; uint8_t x_684; uint8_t x_685; uint8_t x_686; uint8_t x_687; uint8_t x_688; lean_object* x_689; uint64_t x_690; uint64_t x_691; uint64_t x_692; uint64_t x_693; uint64_t x_694; lean_object* x_695; lean_object* x_696; 
x_669 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 8);
x_670 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 9);
x_671 = lean_ctor_get_uint8(x_553, 0);
x_672 = lean_ctor_get_uint8(x_553, 1);
x_673 = lean_ctor_get_uint8(x_553, 2);
x_674 = lean_ctor_get_uint8(x_553, 3);
x_675 = lean_ctor_get_uint8(x_553, 4);
x_676 = lean_ctor_get_uint8(x_553, 5);
x_677 = lean_ctor_get_uint8(x_553, 6);
x_678 = lean_ctor_get_uint8(x_553, 7);
x_679 = lean_ctor_get_uint8(x_553, 8);
x_680 = lean_ctor_get_uint8(x_553, 10);
x_681 = lean_ctor_get_uint8(x_553, 11);
x_682 = lean_ctor_get_uint8(x_553, 12);
x_683 = lean_ctor_get_uint8(x_553, 13);
x_684 = lean_ctor_get_uint8(x_553, 14);
x_685 = lean_ctor_get_uint8(x_553, 15);
x_686 = lean_ctor_get_uint8(x_553, 16);
x_687 = lean_ctor_get_uint8(x_553, 17);
lean_dec(x_553);
x_688 = 1;
x_689 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_689, 0, x_671);
lean_ctor_set_uint8(x_689, 1, x_672);
lean_ctor_set_uint8(x_689, 2, x_673);
lean_ctor_set_uint8(x_689, 3, x_674);
lean_ctor_set_uint8(x_689, 4, x_675);
lean_ctor_set_uint8(x_689, 5, x_676);
lean_ctor_set_uint8(x_689, 6, x_677);
lean_ctor_set_uint8(x_689, 7, x_678);
lean_ctor_set_uint8(x_689, 8, x_679);
lean_ctor_set_uint8(x_689, 9, x_688);
lean_ctor_set_uint8(x_689, 10, x_680);
lean_ctor_set_uint8(x_689, 11, x_681);
lean_ctor_set_uint8(x_689, 12, x_682);
lean_ctor_set_uint8(x_689, 13, x_683);
lean_ctor_set_uint8(x_689, 14, x_684);
lean_ctor_set_uint8(x_689, 15, x_685);
lean_ctor_set_uint8(x_689, 16, x_686);
lean_ctor_set_uint8(x_689, 17, x_687);
x_690 = 2;
x_691 = lean_uint64_shift_right(x_557, x_690);
x_692 = lean_uint64_shift_left(x_691, x_690);
x_693 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_694 = lean_uint64_lor(x_692, x_693);
x_695 = lean_alloc_ctor(0, 6, 10);
lean_ctor_set(x_695, 0, x_689);
lean_ctor_set(x_695, 1, x_558);
lean_ctor_set(x_695, 2, x_559);
lean_ctor_set(x_695, 3, x_560);
lean_ctor_set(x_695, 4, x_561);
lean_ctor_set(x_695, 5, x_562);
lean_ctor_set_uint64(x_695, sizeof(void*)*6, x_694);
lean_ctor_set_uint8(x_695, sizeof(void*)*6 + 8, x_669);
lean_ctor_set_uint8(x_695, sizeof(void*)*6 + 9, x_670);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_696 = l_Lean_Meta_mkNoConfusion(x_540, x_529, x_695, x_5, x_6, x_7, x_554);
if (lean_obj_tag(x_696) == 0)
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; uint8_t x_703; 
x_697 = lean_ctor_get(x_696, 0);
lean_inc(x_697);
x_698 = lean_ctor_get(x_696, 1);
lean_inc(x_698);
lean_dec(x_696);
x_699 = lean_ctor_get(x_555, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_699, 0);
lean_inc(x_700);
lean_dec(x_699);
x_701 = lean_ctor_get(x_556, 0);
lean_inc(x_701);
lean_dec(x_556);
x_702 = lean_ctor_get(x_701, 0);
lean_inc(x_702);
lean_dec(x_701);
x_703 = lean_name_eq(x_700, x_702);
lean_dec(x_702);
lean_dec(x_700);
if (x_703 == 0)
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
lean_dec(x_555);
lean_dec(x_3);
lean_dec(x_2);
x_704 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_697, x_4, x_5, x_6, x_7, x_698);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_705 = lean_ctor_get(x_704, 1);
lean_inc(x_705);
if (lean_is_exclusive(x_704)) {
 lean_ctor_release(x_704, 0);
 lean_ctor_release(x_704, 1);
 x_706 = x_704;
} else {
 lean_dec_ref(x_704);
 x_706 = lean_box(0);
}
x_707 = lean_box(0);
if (lean_is_scalar(x_706)) {
 x_708 = lean_alloc_ctor(0, 2, 0);
} else {
 x_708 = x_706;
}
lean_ctor_set(x_708, 0, x_707);
lean_ctor_set(x_708, 1, x_705);
return x_708;
}
else
{
lean_object* x_709; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_697);
x_709 = lean_infer_type(x_697, x_4, x_5, x_6, x_7, x_698);
if (lean_obj_tag(x_709) == 0)
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; 
x_710 = lean_ctor_get(x_709, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_709, 1);
lean_inc(x_711);
lean_dec(x_709);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_712 = l_Lean_Meta_whnfD(x_710, x_4, x_5, x_6, x_7, x_711);
if (lean_obj_tag(x_712) == 0)
{
lean_object* x_713; 
x_713 = lean_ctor_get(x_712, 0);
lean_inc(x_713);
if (lean_obj_tag(x_713) == 7)
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
lean_dec(x_2);
x_714 = lean_ctor_get(x_712, 1);
lean_inc(x_714);
lean_dec(x_712);
x_715 = lean_ctor_get(x_713, 1);
lean_inc(x_715);
lean_dec(x_713);
x_716 = l_Lean_Expr_headBeta(x_715);
lean_inc(x_1);
x_717 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_714);
if (lean_obj_tag(x_717) == 0)
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
x_719 = lean_ctor_get(x_717, 1);
lean_inc(x_719);
lean_dec(x_717);
lean_inc(x_4);
x_720 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_716, x_718, x_4, x_5, x_6, x_7, x_719);
x_721 = lean_ctor_get(x_720, 0);
lean_inc(x_721);
x_722 = lean_ctor_get(x_720, 1);
lean_inc(x_722);
lean_dec(x_720);
lean_inc(x_721);
x_723 = l_Lean_Expr_app___override(x_697, x_721);
x_724 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_723, x_4, x_5, x_6, x_7, x_722);
x_725 = lean_ctor_get(x_724, 1);
lean_inc(x_725);
if (lean_is_exclusive(x_724)) {
 lean_ctor_release(x_724, 0);
 lean_ctor_release(x_724, 1);
 x_726 = x_724;
} else {
 lean_dec_ref(x_724);
 x_726 = lean_box(0);
}
x_727 = l_Lean_Expr_mvarId_x21(x_721);
lean_dec(x_721);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_728 = l_Lean_MVarId_tryClear(x_727, x_3, x_4, x_5, x_6, x_7, x_725);
if (lean_obj_tag(x_728) == 0)
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; 
x_729 = lean_ctor_get(x_728, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_728, 1);
lean_inc(x_730);
lean_dec(x_728);
lean_inc(x_555);
x_731 = l_Lean_Meta_getCtorNumPropFields(x_555, x_4, x_5, x_6, x_7, x_730);
if (lean_obj_tag(x_731) == 0)
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; 
x_732 = lean_ctor_get(x_731, 0);
lean_inc(x_732);
x_733 = lean_ctor_get(x_731, 1);
lean_inc(x_733);
if (lean_is_exclusive(x_731)) {
 lean_ctor_release(x_731, 0);
 lean_ctor_release(x_731, 1);
 x_734 = x_731;
} else {
 lean_dec_ref(x_731);
 x_734 = lean_box(0);
}
x_735 = lean_ctor_get(x_555, 4);
lean_inc(x_735);
lean_dec(x_555);
x_736 = lean_nat_sub(x_735, x_732);
lean_dec(x_732);
lean_dec(x_735);
if (lean_is_scalar(x_726)) {
 x_737 = lean_alloc_ctor(1, 2, 0);
} else {
 x_737 = x_726;
 lean_ctor_set_tag(x_737, 1);
}
lean_ctor_set(x_737, 0, x_729);
lean_ctor_set(x_737, 1, x_736);
if (lean_is_scalar(x_734)) {
 x_738 = lean_alloc_ctor(0, 2, 0);
} else {
 x_738 = x_734;
}
lean_ctor_set(x_738, 0, x_737);
lean_ctor_set(x_738, 1, x_733);
return x_738;
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
lean_dec(x_729);
lean_dec(x_726);
lean_dec(x_555);
x_739 = lean_ctor_get(x_731, 0);
lean_inc(x_739);
x_740 = lean_ctor_get(x_731, 1);
lean_inc(x_740);
if (lean_is_exclusive(x_731)) {
 lean_ctor_release(x_731, 0);
 lean_ctor_release(x_731, 1);
 x_741 = x_731;
} else {
 lean_dec_ref(x_731);
 x_741 = lean_box(0);
}
if (lean_is_scalar(x_741)) {
 x_742 = lean_alloc_ctor(1, 2, 0);
} else {
 x_742 = x_741;
}
lean_ctor_set(x_742, 0, x_739);
lean_ctor_set(x_742, 1, x_740);
return x_742;
}
}
else
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; 
lean_dec(x_726);
lean_dec(x_555);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_743 = lean_ctor_get(x_728, 0);
lean_inc(x_743);
x_744 = lean_ctor_get(x_728, 1);
lean_inc(x_744);
if (lean_is_exclusive(x_728)) {
 lean_ctor_release(x_728, 0);
 lean_ctor_release(x_728, 1);
 x_745 = x_728;
} else {
 lean_dec_ref(x_728);
 x_745 = lean_box(0);
}
if (lean_is_scalar(x_745)) {
 x_746 = lean_alloc_ctor(1, 2, 0);
} else {
 x_746 = x_745;
}
lean_ctor_set(x_746, 0, x_743);
lean_ctor_set(x_746, 1, x_744);
return x_746;
}
}
else
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
lean_dec(x_716);
lean_dec(x_697);
lean_dec(x_555);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_747 = lean_ctor_get(x_717, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_717, 1);
lean_inc(x_748);
if (lean_is_exclusive(x_717)) {
 lean_ctor_release(x_717, 0);
 lean_ctor_release(x_717, 1);
 x_749 = x_717;
} else {
 lean_dec_ref(x_717);
 x_749 = lean_box(0);
}
if (lean_is_scalar(x_749)) {
 x_750 = lean_alloc_ctor(1, 2, 0);
} else {
 x_750 = x_749;
}
lean_ctor_set(x_750, 0, x_747);
lean_ctor_set(x_750, 1, x_748);
return x_750;
}
}
else
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; 
lean_dec(x_713);
lean_dec(x_697);
lean_dec(x_555);
lean_dec(x_3);
x_751 = lean_ctor_get(x_712, 1);
lean_inc(x_751);
lean_dec(x_712);
x_752 = l_Lean_Meta_injectionCore___lambda__1___closed__17;
x_753 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_752, x_4, x_5, x_6, x_7, x_751);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_753;
}
}
else
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; 
lean_dec(x_697);
lean_dec(x_555);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_754 = lean_ctor_get(x_712, 0);
lean_inc(x_754);
x_755 = lean_ctor_get(x_712, 1);
lean_inc(x_755);
if (lean_is_exclusive(x_712)) {
 lean_ctor_release(x_712, 0);
 lean_ctor_release(x_712, 1);
 x_756 = x_712;
} else {
 lean_dec_ref(x_712);
 x_756 = lean_box(0);
}
if (lean_is_scalar(x_756)) {
 x_757 = lean_alloc_ctor(1, 2, 0);
} else {
 x_757 = x_756;
}
lean_ctor_set(x_757, 0, x_754);
lean_ctor_set(x_757, 1, x_755);
return x_757;
}
}
else
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
lean_dec(x_697);
lean_dec(x_555);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_758 = lean_ctor_get(x_709, 0);
lean_inc(x_758);
x_759 = lean_ctor_get(x_709, 1);
lean_inc(x_759);
if (lean_is_exclusive(x_709)) {
 lean_ctor_release(x_709, 0);
 lean_ctor_release(x_709, 1);
 x_760 = x_709;
} else {
 lean_dec_ref(x_709);
 x_760 = lean_box(0);
}
if (lean_is_scalar(x_760)) {
 x_761 = lean_alloc_ctor(1, 2, 0);
} else {
 x_761 = x_760;
}
lean_ctor_set(x_761, 0, x_758);
lean_ctor_set(x_761, 1, x_759);
return x_761;
}
}
}
else
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; 
lean_dec(x_556);
lean_dec(x_555);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_762 = lean_ctor_get(x_696, 0);
lean_inc(x_762);
x_763 = lean_ctor_get(x_696, 1);
lean_inc(x_763);
if (lean_is_exclusive(x_696)) {
 lean_ctor_release(x_696, 0);
 lean_ctor_release(x_696, 1);
 x_764 = x_696;
} else {
 lean_dec_ref(x_696);
 x_764 = lean_box(0);
}
if (lean_is_scalar(x_764)) {
 x_765 = lean_alloc_ctor(1, 2, 0);
} else {
 x_765 = x_764;
}
lean_ctor_set(x_765, 0, x_762);
lean_ctor_set(x_765, 1, x_763);
return x_765;
}
}
}
}
}
else
{
uint8_t x_766; 
lean_dec(x_543);
lean_dec(x_540);
lean_dec(x_529);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_766 = !lean_is_exclusive(x_545);
if (x_766 == 0)
{
return x_545;
}
else
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; 
x_767 = lean_ctor_get(x_545, 0);
x_768 = lean_ctor_get(x_545, 1);
lean_inc(x_768);
lean_inc(x_767);
lean_dec(x_545);
x_769 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_769, 0, x_767);
lean_ctor_set(x_769, 1, x_768);
return x_769;
}
}
}
else
{
uint8_t x_770; 
lean_dec(x_540);
lean_dec(x_538);
lean_dec(x_529);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_770 = !lean_is_exclusive(x_542);
if (x_770 == 0)
{
return x_542;
}
else
{
lean_object* x_771; lean_object* x_772; lean_object* x_773; 
x_771 = lean_ctor_get(x_542, 0);
x_772 = lean_ctor_get(x_542, 1);
lean_inc(x_772);
lean_inc(x_771);
lean_dec(x_542);
x_773 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_773, 0, x_771);
lean_ctor_set(x_773, 1, x_772);
return x_773;
}
}
}
else
{
uint8_t x_774; 
lean_dec(x_538);
lean_dec(x_537);
lean_dec(x_529);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_774 = !lean_is_exclusive(x_539);
if (x_774 == 0)
{
return x_539;
}
else
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; 
x_775 = lean_ctor_get(x_539, 0);
x_776 = lean_ctor_get(x_539, 1);
lean_inc(x_776);
lean_inc(x_775);
lean_dec(x_539);
x_777 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_777, 0, x_775);
lean_ctor_set(x_777, 1, x_776);
return x_777;
}
}
}
}
else
{
uint8_t x_778; 
lean_dec(x_526);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_778 = !lean_is_exclusive(x_528);
if (x_778 == 0)
{
return x_528;
}
else
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; 
x_779 = lean_ctor_get(x_528, 0);
x_780 = lean_ctor_get(x_528, 1);
lean_inc(x_780);
lean_inc(x_779);
lean_dec(x_528);
x_781 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_781, 0, x_779);
lean_ctor_set(x_781, 1, x_780);
return x_781;
}
}
}
else
{
uint8_t x_782; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_782 = !lean_is_exclusive(x_525);
if (x_782 == 0)
{
return x_525;
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_783 = lean_ctor_get(x_525, 0);
x_784 = lean_ctor_get(x_525, 1);
lean_inc(x_784);
lean_inc(x_783);
lean_dec(x_525);
x_785 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_785, 0, x_783);
lean_ctor_set(x_785, 1, x_784);
return x_785;
}
}
}
}
else
{
uint8_t x_786; 
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_786 = !lean_is_exclusive(x_276);
if (x_786 == 0)
{
return x_276;
}
else
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; 
x_787 = lean_ctor_get(x_276, 0);
x_788 = lean_ctor_get(x_276, 1);
lean_inc(x_788);
lean_inc(x_787);
lean_dec(x_276);
x_789 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_789, 0, x_787);
lean_ctor_set(x_789, 1, x_788);
return x_789;
}
}
}
}
else
{
uint8_t x_790; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_790 = !lean_is_exclusive(x_15);
if (x_790 == 0)
{
return x_15;
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_791 = lean_ctor_get(x_15, 0);
x_792 = lean_ctor_get(x_15, 1);
lean_inc(x_792);
lean_inc(x_791);
lean_dec(x_15);
x_793 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_793, 0, x_791);
lean_ctor_set(x_793, 1, x_792);
return x_793;
}
}
}
else
{
uint8_t x_794; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_794 = !lean_is_exclusive(x_11);
if (x_794 == 0)
{
return x_11;
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; 
x_795 = lean_ctor_get(x_11, 0);
x_796 = lean_ctor_get(x_11, 1);
lean_inc(x_796);
lean_inc(x_795);
lean_dec(x_11);
x_797 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_797, 0, x_795);
lean_ctor_set(x_797, 1, x_796);
return x_797;
}
}
}
else
{
uint8_t x_798; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_798 = !lean_is_exclusive(x_9);
if (x_798 == 0)
{
return x_9;
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; 
x_799 = lean_ctor_get(x_9, 0);
x_800 = lean_ctor_get(x_9, 1);
lean_inc(x_800);
lean_inc(x_799);
lean_dec(x_9);
x_801 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_801, 0, x_799);
lean_ctor_set(x_801, 1, x_800);
return x_801;
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
x_10 = lean_ctor_get(x_5, 1);
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
