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
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEqHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__10;
static lean_object* l_Lean_Meta_injectionCore___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__1;
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__6;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__5;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__6;
lean_object* l_outOfBounds___rarg(lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__12;
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__4;
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__5;
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__7;
static lean_object* l_Lean_Meta_injectionIntro___closed__1;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__1;
static lean_object* l_Lean_Meta_injectionCore___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_getCtorNumPropFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__15;
lean_object* l_Lean_Meta_heqToEq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__3;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__13;
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__9;
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__4;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_getCtorNumPropFields___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__14;
static lean_object* l_Lean_Meta_injections_go___closed__2;
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__8;
LEAN_EXPORT lean_object* l_Lean_Meta_injections_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_getCtorNumPropFields___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_le(x_5, x_4);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_3, x_16);
lean_dec(x_3);
x_24 = lean_ctor_get(x_1, 3);
x_25 = lean_nat_add(x_24, x_4);
x_26 = lean_array_get_size(x_2);
x_27 = lean_nat_dec_lt(x_25, x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
x_28 = l_Lean_instInhabitedExpr;
x_29 = l_outOfBounds___rarg(x_28);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_30 = lean_infer_type(x_29, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_33 = l_Lean_Meta_isProp(x_31, x_8, x_9, x_10, x_11, x_32);
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
lean_ctor_set(x_37, 0, x_7);
x_18 = x_37;
x_19 = x_36;
goto block_23;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_nat_add(x_7, x_16);
lean_dec(x_7);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_18 = x_40;
x_19 = x_38;
goto block_23;
}
}
else
{
uint8_t x_41; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
return x_33;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_33, 0);
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_33);
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
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_45 = !lean_is_exclusive(x_30);
if (x_45 == 0)
{
return x_30;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_30, 0);
x_47 = lean_ctor_get(x_30, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_30);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_array_fget(x_2, x_25);
lean_dec(x_25);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_50 = lean_infer_type(x_49, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_53 = l_Lean_Meta_isProp(x_51, x_8, x_9, x_10, x_11, x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_7);
x_18 = x_57;
x_19 = x_56;
goto block_23;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_dec(x_53);
x_59 = lean_nat_add(x_7, x_16);
lean_dec(x_7);
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_18 = x_60;
x_19 = x_58;
goto block_23;
}
}
else
{
uint8_t x_61; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_53);
if (x_61 == 0)
{
return x_53;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_53, 0);
x_63 = lean_ctor_get(x_53, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_53);
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
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_50);
if (x_65 == 0)
{
return x_50;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_50, 0);
x_67 = lean_ctor_get(x_50, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_50);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
block_23:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_nat_add(x_4, x_6);
lean_dec(x_4);
x_3 = x_17;
x_4 = x_21;
x_7 = x_20;
x_12 = x_19;
goto _start;
}
}
else
{
lean_object* x_69; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_7);
lean_ctor_set(x_69, 1, x_12);
return x_69;
}
}
else
{
lean_object* x_70; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_7);
lean_ctor_set(x_70, 1, x_12);
return x_70;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
x_12 = l_Std_Range_forIn_loop___at_Lean_Meta_getCtorNumPropFields___spec__1(x_1, x_2, x_9, x_10, x_9, x_11, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_9);
lean_dec(x_1);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_getCtorNumPropFields___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_loop___at_Lean_Meta_getCtorNumPropFields___spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
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
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("ill-formed noConfusion auxiliary construction", 45, 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__14;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__15;
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
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
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
x_48 = lean_ctor_get(x_4, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_4, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_4, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_4, 4);
lean_inc(x_51);
x_52 = lean_ctor_get(x_4, 5);
lean_inc(x_52);
x_53 = !lean_is_exclusive(x_44);
if (x_53 == 0)
{
uint8_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_55 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_56 = 1;
lean_ctor_set_uint8(x_44, 9, x_56);
x_57 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_57, 0, x_44);
lean_ctor_set(x_57, 1, x_48);
lean_ctor_set(x_57, 2, x_49);
lean_ctor_set(x_57, 3, x_50);
lean_ctor_set(x_57, 4, x_51);
lean_ctor_set(x_57, 5, x_52);
lean_ctor_set_uint8(x_57, sizeof(void*)*6, x_54);
lean_ctor_set_uint8(x_57, sizeof(void*)*6 + 1, x_55);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_58 = l_Lean_Meta_mkNoConfusion(x_31, x_18, x_57, x_5, x_6, x_7, x_45);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_46, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_ctor_get(x_47, 0);
lean_inc(x_63);
lean_dec(x_47);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_name_eq(x_62, x_64);
lean_dec(x_64);
lean_dec(x_62);
if (x_65 == 0)
{
lean_object* x_66; uint8_t x_67; 
lean_dec(x_46);
lean_dec(x_3);
lean_dec(x_2);
x_66 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_59, x_4, x_5, x_6, x_7, x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_67 = !lean_is_exclusive(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 0);
lean_dec(x_68);
x_69 = lean_box(0);
lean_ctor_set(x_66, 0, x_69);
return x_66;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_66, 1);
lean_inc(x_70);
lean_dec(x_66);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_59);
x_73 = lean_infer_type(x_59, x_4, x_5, x_6, x_7, x_60);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_76 = l_Lean_Meta_whnfD(x_74, x_4, x_5, x_6, x_7, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 7)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_2);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Expr_headBeta(x_79);
lean_inc(x_1);
x_81 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_4);
x_84 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_80, x_82, x_4, x_5, x_6, x_7, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_85);
x_87 = l_Lean_Expr_app___override(x_59, x_85);
x_88 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_87, x_4, x_5, x_6, x_7, x_86);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_88, 1);
x_91 = lean_ctor_get(x_88, 0);
lean_dec(x_91);
x_92 = l_Lean_Expr_mvarId_x21(x_85);
lean_dec(x_85);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_93 = l_Lean_MVarId_tryClear(x_92, x_3, x_4, x_5, x_6, x_7, x_90);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_46);
x_96 = l_Lean_Meta_getCtorNumPropFields(x_46, x_4, x_5, x_6, x_7, x_95);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_46, 4);
lean_inc(x_99);
lean_dec(x_46);
x_100 = lean_nat_sub(x_99, x_98);
lean_dec(x_98);
lean_dec(x_99);
lean_ctor_set_tag(x_88, 1);
lean_ctor_set(x_88, 1, x_100);
lean_ctor_set(x_88, 0, x_94);
lean_ctor_set(x_96, 0, x_88);
return x_96;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_101 = lean_ctor_get(x_96, 0);
x_102 = lean_ctor_get(x_96, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_96);
x_103 = lean_ctor_get(x_46, 4);
lean_inc(x_103);
lean_dec(x_46);
x_104 = lean_nat_sub(x_103, x_101);
lean_dec(x_101);
lean_dec(x_103);
lean_ctor_set_tag(x_88, 1);
lean_ctor_set(x_88, 1, x_104);
lean_ctor_set(x_88, 0, x_94);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_88);
lean_ctor_set(x_105, 1, x_102);
return x_105;
}
}
else
{
uint8_t x_106; 
lean_dec(x_94);
lean_free_object(x_88);
lean_dec(x_46);
x_106 = !lean_is_exclusive(x_96);
if (x_106 == 0)
{
return x_96;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_96, 0);
x_108 = lean_ctor_get(x_96, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_96);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_free_object(x_88);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_110 = !lean_is_exclusive(x_93);
if (x_110 == 0)
{
return x_93;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_93, 0);
x_112 = lean_ctor_get(x_93, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_93);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_88, 1);
lean_inc(x_114);
lean_dec(x_88);
x_115 = l_Lean_Expr_mvarId_x21(x_85);
lean_dec(x_85);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_116 = l_Lean_MVarId_tryClear(x_115, x_3, x_4, x_5, x_6, x_7, x_114);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_46);
x_119 = l_Lean_Meta_getCtorNumPropFields(x_46, x_4, x_5, x_6, x_7, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_122 = x_119;
} else {
 lean_dec_ref(x_119);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_46, 4);
lean_inc(x_123);
lean_dec(x_46);
x_124 = lean_nat_sub(x_123, x_120);
lean_dec(x_120);
lean_dec(x_123);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_117);
lean_ctor_set(x_125, 1, x_124);
if (lean_is_scalar(x_122)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_122;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_121);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_117);
lean_dec(x_46);
x_127 = lean_ctor_get(x_119, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_119, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_129 = x_119;
} else {
 lean_dec_ref(x_119);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_131 = lean_ctor_get(x_116, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_116, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_133 = x_116;
} else {
 lean_dec_ref(x_116);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_80);
lean_dec(x_59);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_81);
if (x_135 == 0)
{
return x_81;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_81, 0);
x_137 = lean_ctor_get(x_81, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_81);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_77);
lean_dec(x_59);
lean_dec(x_46);
lean_dec(x_3);
x_139 = lean_ctor_get(x_76, 1);
lean_inc(x_139);
lean_dec(x_76);
x_140 = l_Lean_Meta_injectionCore___lambda__1___closed__16;
x_141 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_140, x_4, x_5, x_6, x_7, x_139);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_141;
}
}
else
{
uint8_t x_142; 
lean_dec(x_59);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_76);
if (x_142 == 0)
{
return x_76;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_76, 0);
x_144 = lean_ctor_get(x_76, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_76);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_59);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_146 = !lean_is_exclusive(x_73);
if (x_146 == 0)
{
return x_73;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_73, 0);
x_148 = lean_ctor_get(x_73, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_73);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_58);
if (x_150 == 0)
{
return x_58;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_58, 0);
x_152 = lean_ctor_get(x_58, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_58);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
else
{
uint8_t x_154; uint8_t x_155; uint8_t x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; uint8_t x_160; uint8_t x_161; uint8_t x_162; uint8_t x_163; uint8_t x_164; uint8_t x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_154 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_155 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_156 = lean_ctor_get_uint8(x_44, 0);
x_157 = lean_ctor_get_uint8(x_44, 1);
x_158 = lean_ctor_get_uint8(x_44, 2);
x_159 = lean_ctor_get_uint8(x_44, 3);
x_160 = lean_ctor_get_uint8(x_44, 4);
x_161 = lean_ctor_get_uint8(x_44, 5);
x_162 = lean_ctor_get_uint8(x_44, 6);
x_163 = lean_ctor_get_uint8(x_44, 7);
x_164 = lean_ctor_get_uint8(x_44, 8);
x_165 = lean_ctor_get_uint8(x_44, 10);
x_166 = lean_ctor_get_uint8(x_44, 11);
x_167 = lean_ctor_get_uint8(x_44, 12);
lean_dec(x_44);
x_168 = 1;
x_169 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_169, 0, x_156);
lean_ctor_set_uint8(x_169, 1, x_157);
lean_ctor_set_uint8(x_169, 2, x_158);
lean_ctor_set_uint8(x_169, 3, x_159);
lean_ctor_set_uint8(x_169, 4, x_160);
lean_ctor_set_uint8(x_169, 5, x_161);
lean_ctor_set_uint8(x_169, 6, x_162);
lean_ctor_set_uint8(x_169, 7, x_163);
lean_ctor_set_uint8(x_169, 8, x_164);
lean_ctor_set_uint8(x_169, 9, x_168);
lean_ctor_set_uint8(x_169, 10, x_165);
lean_ctor_set_uint8(x_169, 11, x_166);
lean_ctor_set_uint8(x_169, 12, x_167);
x_170 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_48);
lean_ctor_set(x_170, 2, x_49);
lean_ctor_set(x_170, 3, x_50);
lean_ctor_set(x_170, 4, x_51);
lean_ctor_set(x_170, 5, x_52);
lean_ctor_set_uint8(x_170, sizeof(void*)*6, x_154);
lean_ctor_set_uint8(x_170, sizeof(void*)*6 + 1, x_155);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_171 = l_Lean_Meta_mkNoConfusion(x_31, x_18, x_170, x_5, x_6, x_7, x_45);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_ctor_get(x_46, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
lean_dec(x_174);
x_176 = lean_ctor_get(x_47, 0);
lean_inc(x_176);
lean_dec(x_47);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
lean_dec(x_176);
x_178 = lean_name_eq(x_175, x_177);
lean_dec(x_177);
lean_dec(x_175);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_46);
lean_dec(x_3);
lean_dec(x_2);
x_179 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_172, x_4, x_5, x_6, x_7, x_173);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_181 = x_179;
} else {
 lean_dec_ref(x_179);
 x_181 = lean_box(0);
}
x_182 = lean_box(0);
if (lean_is_scalar(x_181)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_181;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_180);
return x_183;
}
else
{
lean_object* x_184; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_172);
x_184 = lean_infer_type(x_172, x_4, x_5, x_6, x_7, x_173);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_187 = l_Lean_Meta_whnfD(x_185, x_4, x_5, x_6, x_7, x_186);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
if (lean_obj_tag(x_188) == 7)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
lean_dec(x_2);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_Expr_headBeta(x_190);
lean_inc(x_1);
x_192 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_189);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
lean_inc(x_4);
x_195 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_191, x_193, x_4, x_5, x_6, x_7, x_194);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
lean_inc(x_196);
x_198 = l_Lean_Expr_app___override(x_172, x_196);
x_199 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_198, x_4, x_5, x_6, x_7, x_197);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_201 = x_199;
} else {
 lean_dec_ref(x_199);
 x_201 = lean_box(0);
}
x_202 = l_Lean_Expr_mvarId_x21(x_196);
lean_dec(x_196);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_203 = l_Lean_MVarId_tryClear(x_202, x_3, x_4, x_5, x_6, x_7, x_200);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
lean_inc(x_46);
x_206 = l_Lean_Meta_getCtorNumPropFields(x_46, x_4, x_5, x_6, x_7, x_205);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_209 = x_206;
} else {
 lean_dec_ref(x_206);
 x_209 = lean_box(0);
}
x_210 = lean_ctor_get(x_46, 4);
lean_inc(x_210);
lean_dec(x_46);
x_211 = lean_nat_sub(x_210, x_207);
lean_dec(x_207);
lean_dec(x_210);
if (lean_is_scalar(x_201)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_201;
 lean_ctor_set_tag(x_212, 1);
}
lean_ctor_set(x_212, 0, x_204);
lean_ctor_set(x_212, 1, x_211);
if (lean_is_scalar(x_209)) {
 x_213 = lean_alloc_ctor(0, 2, 0);
} else {
 x_213 = x_209;
}
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_208);
return x_213;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_204);
lean_dec(x_201);
lean_dec(x_46);
x_214 = lean_ctor_get(x_206, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_206, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_216 = x_206;
} else {
 lean_dec_ref(x_206);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_201);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_218 = lean_ctor_get(x_203, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_203, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_220 = x_203;
} else {
 lean_dec_ref(x_203);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(1, 2, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
lean_dec(x_191);
lean_dec(x_172);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_222 = lean_ctor_get(x_192, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_192, 1);
lean_inc(x_223);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_224 = x_192;
} else {
 lean_dec_ref(x_192);
 x_224 = lean_box(0);
}
if (lean_is_scalar(x_224)) {
 x_225 = lean_alloc_ctor(1, 2, 0);
} else {
 x_225 = x_224;
}
lean_ctor_set(x_225, 0, x_222);
lean_ctor_set(x_225, 1, x_223);
return x_225;
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_188);
lean_dec(x_172);
lean_dec(x_46);
lean_dec(x_3);
x_226 = lean_ctor_get(x_187, 1);
lean_inc(x_226);
lean_dec(x_187);
x_227 = l_Lean_Meta_injectionCore___lambda__1___closed__16;
x_228 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_227, x_4, x_5, x_6, x_7, x_226);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_172);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_229 = lean_ctor_get(x_187, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_187, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_231 = x_187;
} else {
 lean_dec_ref(x_187);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_172);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_233 = lean_ctor_get(x_184, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_184, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_235 = x_184;
} else {
 lean_dec_ref(x_184);
 x_235 = lean_box(0);
}
if (lean_is_scalar(x_235)) {
 x_236 = lean_alloc_ctor(1, 2, 0);
} else {
 x_236 = x_235;
}
lean_ctor_set(x_236, 0, x_233);
lean_ctor_set(x_236, 1, x_234);
return x_236;
}
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_237 = lean_ctor_get(x_171, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_171, 1);
lean_inc(x_238);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_239 = x_171;
} else {
 lean_dec_ref(x_171);
 x_239 = lean_box(0);
}
if (lean_is_scalar(x_239)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_239;
}
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_238);
return x_240;
}
}
}
}
}
else
{
uint8_t x_241; 
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
x_241 = !lean_is_exclusive(x_36);
if (x_241 == 0)
{
return x_36;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_36, 0);
x_243 = lean_ctor_get(x_36, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_36);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
else
{
uint8_t x_245; 
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
x_245 = !lean_is_exclusive(x_33);
if (x_245 == 0)
{
return x_33;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_33, 0);
x_247 = lean_ctor_get(x_33, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_33);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
else
{
uint8_t x_249; 
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
x_249 = !lean_is_exclusive(x_30);
if (x_249 == 0)
{
return x_30;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_30, 0);
x_251 = lean_ctor_get(x_30, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_30);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_253 = l_Lean_Expr_appFn_x21(x_16);
x_254 = l_Lean_Expr_appFn_x21(x_253);
x_255 = l_Lean_Expr_appFn_x21(x_254);
x_256 = l_Lean_Expr_appArg_x21(x_255);
lean_dec(x_255);
x_257 = l_Lean_Expr_appArg_x21(x_254);
lean_dec(x_254);
x_258 = l_Lean_Expr_appArg_x21(x_253);
lean_dec(x_253);
x_259 = l_Lean_Expr_appArg_x21(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_258);
x_260 = l_Lean_Meta_isExprDefEq(x_256, x_258, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_260) == 0)
{
lean_object* x_261; uint8_t x_262; 
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_unbox(x_261);
lean_dec(x_261);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
lean_dec(x_257);
x_263 = lean_ctor_get(x_260, 1);
lean_inc(x_263);
lean_dec(x_260);
x_264 = l_Lean_Meta_injectionCore___lambda__1___closed__4;
x_265 = lean_unsigned_to_nat(3u);
x_266 = l_Lean_Expr_isAppOfArity(x_16, x_264, x_265);
lean_dec(x_16);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; 
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_18);
lean_dec(x_3);
x_267 = l_Lean_Meta_injectionCore___lambda__1___closed__8;
x_268 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_267, x_4, x_5, x_6, x_7, x_263);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_268;
}
else
{
lean_object* x_269; 
lean_inc(x_1);
x_269 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_263);
if (lean_obj_tag(x_269) == 0)
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_272 = l_Lean_Meta_isConstructorApp_x27_x3f(x_258, x_4, x_5, x_6, x_7, x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
lean_dec(x_272);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_275 = l_Lean_Meta_isConstructorApp_x27_x3f(x_259, x_4, x_5, x_6, x_7, x_274);
if (lean_obj_tag(x_275) == 0)
{
if (lean_obj_tag(x_273) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_270);
lean_dec(x_18);
lean_dec(x_3);
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
lean_dec(x_275);
x_277 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_278 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_277, x_4, x_5, x_6, x_7, x_276);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_278;
}
else
{
lean_object* x_279; 
x_279 = lean_ctor_get(x_275, 0);
lean_inc(x_279);
if (lean_obj_tag(x_279) == 0)
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_273);
lean_dec(x_270);
lean_dec(x_18);
lean_dec(x_3);
x_280 = lean_ctor_get(x_275, 1);
lean_inc(x_280);
lean_dec(x_275);
x_281 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_282 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_281, x_4, x_5, x_6, x_7, x_280);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_282;
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; 
x_283 = lean_ctor_get(x_4, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_275, 1);
lean_inc(x_284);
lean_dec(x_275);
x_285 = lean_ctor_get(x_273, 0);
lean_inc(x_285);
lean_dec(x_273);
x_286 = lean_ctor_get(x_279, 0);
lean_inc(x_286);
lean_dec(x_279);
x_287 = lean_ctor_get(x_4, 1);
lean_inc(x_287);
x_288 = lean_ctor_get(x_4, 2);
lean_inc(x_288);
x_289 = lean_ctor_get(x_4, 3);
lean_inc(x_289);
x_290 = lean_ctor_get(x_4, 4);
lean_inc(x_290);
x_291 = lean_ctor_get(x_4, 5);
lean_inc(x_291);
x_292 = !lean_is_exclusive(x_283);
if (x_292 == 0)
{
uint8_t x_293; uint8_t x_294; uint8_t x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_294 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_295 = 1;
lean_ctor_set_uint8(x_283, 9, x_295);
x_296 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_296, 0, x_283);
lean_ctor_set(x_296, 1, x_287);
lean_ctor_set(x_296, 2, x_288);
lean_ctor_set(x_296, 3, x_289);
lean_ctor_set(x_296, 4, x_290);
lean_ctor_set(x_296, 5, x_291);
lean_ctor_set_uint8(x_296, sizeof(void*)*6, x_293);
lean_ctor_set_uint8(x_296, sizeof(void*)*6 + 1, x_294);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_297 = l_Lean_Meta_mkNoConfusion(x_270, x_18, x_296, x_5, x_6, x_7, x_284);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; uint8_t x_304; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_300 = lean_ctor_get(x_285, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
lean_dec(x_300);
x_302 = lean_ctor_get(x_286, 0);
lean_inc(x_302);
lean_dec(x_286);
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
lean_dec(x_302);
x_304 = lean_name_eq(x_301, x_303);
lean_dec(x_303);
lean_dec(x_301);
if (x_304 == 0)
{
lean_object* x_305; uint8_t x_306; 
lean_dec(x_285);
lean_dec(x_3);
lean_dec(x_2);
x_305 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_298, x_4, x_5, x_6, x_7, x_299);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_306 = !lean_is_exclusive(x_305);
if (x_306 == 0)
{
lean_object* x_307; lean_object* x_308; 
x_307 = lean_ctor_get(x_305, 0);
lean_dec(x_307);
x_308 = lean_box(0);
lean_ctor_set(x_305, 0, x_308);
return x_305;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_305, 1);
lean_inc(x_309);
lean_dec(x_305);
x_310 = lean_box(0);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set(x_311, 1, x_309);
return x_311;
}
}
else
{
lean_object* x_312; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_298);
x_312 = lean_infer_type(x_298, x_4, x_5, x_6, x_7, x_299);
if (lean_obj_tag(x_312) == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_312, 0);
lean_inc(x_313);
x_314 = lean_ctor_get(x_312, 1);
lean_inc(x_314);
lean_dec(x_312);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_315 = l_Lean_Meta_whnfD(x_313, x_4, x_5, x_6, x_7, x_314);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
if (lean_obj_tag(x_316) == 7)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_2);
x_317 = lean_ctor_get(x_315, 1);
lean_inc(x_317);
lean_dec(x_315);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_319 = l_Lean_Expr_headBeta(x_318);
lean_inc(x_1);
x_320 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_317);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; uint8_t x_328; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
lean_inc(x_4);
x_323 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_319, x_321, x_4, x_5, x_6, x_7, x_322);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
lean_dec(x_323);
lean_inc(x_324);
x_326 = l_Lean_Expr_app___override(x_298, x_324);
x_327 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_326, x_4, x_5, x_6, x_7, x_325);
x_328 = !lean_is_exclusive(x_327);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_329 = lean_ctor_get(x_327, 1);
x_330 = lean_ctor_get(x_327, 0);
lean_dec(x_330);
x_331 = l_Lean_Expr_mvarId_x21(x_324);
lean_dec(x_324);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_332 = l_Lean_MVarId_tryClear(x_331, x_3, x_4, x_5, x_6, x_7, x_329);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
lean_inc(x_285);
x_335 = l_Lean_Meta_getCtorNumPropFields(x_285, x_4, x_5, x_6, x_7, x_334);
if (lean_obj_tag(x_335) == 0)
{
uint8_t x_336; 
x_336 = !lean_is_exclusive(x_335);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_335, 0);
x_338 = lean_ctor_get(x_285, 4);
lean_inc(x_338);
lean_dec(x_285);
x_339 = lean_nat_sub(x_338, x_337);
lean_dec(x_337);
lean_dec(x_338);
lean_ctor_set_tag(x_327, 1);
lean_ctor_set(x_327, 1, x_339);
lean_ctor_set(x_327, 0, x_333);
lean_ctor_set(x_335, 0, x_327);
return x_335;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
x_340 = lean_ctor_get(x_335, 0);
x_341 = lean_ctor_get(x_335, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_335);
x_342 = lean_ctor_get(x_285, 4);
lean_inc(x_342);
lean_dec(x_285);
x_343 = lean_nat_sub(x_342, x_340);
lean_dec(x_340);
lean_dec(x_342);
lean_ctor_set_tag(x_327, 1);
lean_ctor_set(x_327, 1, x_343);
lean_ctor_set(x_327, 0, x_333);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_327);
lean_ctor_set(x_344, 1, x_341);
return x_344;
}
}
else
{
uint8_t x_345; 
lean_dec(x_333);
lean_free_object(x_327);
lean_dec(x_285);
x_345 = !lean_is_exclusive(x_335);
if (x_345 == 0)
{
return x_335;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_346 = lean_ctor_get(x_335, 0);
x_347 = lean_ctor_get(x_335, 1);
lean_inc(x_347);
lean_inc(x_346);
lean_dec(x_335);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
return x_348;
}
}
}
else
{
uint8_t x_349; 
lean_free_object(x_327);
lean_dec(x_285);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_349 = !lean_is_exclusive(x_332);
if (x_349 == 0)
{
return x_332;
}
else
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; 
x_350 = lean_ctor_get(x_332, 0);
x_351 = lean_ctor_get(x_332, 1);
lean_inc(x_351);
lean_inc(x_350);
lean_dec(x_332);
x_352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
return x_352;
}
}
}
else
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_353 = lean_ctor_get(x_327, 1);
lean_inc(x_353);
lean_dec(x_327);
x_354 = l_Lean_Expr_mvarId_x21(x_324);
lean_dec(x_324);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_355 = l_Lean_MVarId_tryClear(x_354, x_3, x_4, x_5, x_6, x_7, x_353);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
lean_inc(x_285);
x_358 = l_Lean_Meta_getCtorNumPropFields(x_285, x_4, x_5, x_6, x_7, x_357);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_361 = x_358;
} else {
 lean_dec_ref(x_358);
 x_361 = lean_box(0);
}
x_362 = lean_ctor_get(x_285, 4);
lean_inc(x_362);
lean_dec(x_285);
x_363 = lean_nat_sub(x_362, x_359);
lean_dec(x_359);
lean_dec(x_362);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_356);
lean_ctor_set(x_364, 1, x_363);
if (lean_is_scalar(x_361)) {
 x_365 = lean_alloc_ctor(0, 2, 0);
} else {
 x_365 = x_361;
}
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_360);
return x_365;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_356);
lean_dec(x_285);
x_366 = lean_ctor_get(x_358, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_358, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_368 = x_358;
} else {
 lean_dec_ref(x_358);
 x_368 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_369 = lean_alloc_ctor(1, 2, 0);
} else {
 x_369 = x_368;
}
lean_ctor_set(x_369, 0, x_366);
lean_ctor_set(x_369, 1, x_367);
return x_369;
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_285);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_370 = lean_ctor_get(x_355, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_355, 1);
lean_inc(x_371);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_372 = x_355;
} else {
 lean_dec_ref(x_355);
 x_372 = lean_box(0);
}
if (lean_is_scalar(x_372)) {
 x_373 = lean_alloc_ctor(1, 2, 0);
} else {
 x_373 = x_372;
}
lean_ctor_set(x_373, 0, x_370);
lean_ctor_set(x_373, 1, x_371);
return x_373;
}
}
}
else
{
uint8_t x_374; 
lean_dec(x_319);
lean_dec(x_298);
lean_dec(x_285);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_374 = !lean_is_exclusive(x_320);
if (x_374 == 0)
{
return x_320;
}
else
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_320, 0);
x_376 = lean_ctor_get(x_320, 1);
lean_inc(x_376);
lean_inc(x_375);
lean_dec(x_320);
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
lean_dec(x_316);
lean_dec(x_298);
lean_dec(x_285);
lean_dec(x_3);
x_378 = lean_ctor_get(x_315, 1);
lean_inc(x_378);
lean_dec(x_315);
x_379 = l_Lean_Meta_injectionCore___lambda__1___closed__16;
x_380 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_379, x_4, x_5, x_6, x_7, x_378);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_380;
}
}
else
{
uint8_t x_381; 
lean_dec(x_298);
lean_dec(x_285);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_381 = !lean_is_exclusive(x_315);
if (x_381 == 0)
{
return x_315;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_315, 0);
x_383 = lean_ctor_get(x_315, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_315);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
else
{
uint8_t x_385; 
lean_dec(x_298);
lean_dec(x_285);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_385 = !lean_is_exclusive(x_312);
if (x_385 == 0)
{
return x_312;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_312, 0);
x_387 = lean_ctor_get(x_312, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_312);
x_388 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
return x_388;
}
}
}
}
else
{
uint8_t x_389; 
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_389 = !lean_is_exclusive(x_297);
if (x_389 == 0)
{
return x_297;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_297, 0);
x_391 = lean_ctor_get(x_297, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_297);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
return x_392;
}
}
}
else
{
uint8_t x_393; uint8_t x_394; uint8_t x_395; uint8_t x_396; uint8_t x_397; uint8_t x_398; uint8_t x_399; uint8_t x_400; uint8_t x_401; uint8_t x_402; uint8_t x_403; uint8_t x_404; uint8_t x_405; uint8_t x_406; uint8_t x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_393 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_394 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_395 = lean_ctor_get_uint8(x_283, 0);
x_396 = lean_ctor_get_uint8(x_283, 1);
x_397 = lean_ctor_get_uint8(x_283, 2);
x_398 = lean_ctor_get_uint8(x_283, 3);
x_399 = lean_ctor_get_uint8(x_283, 4);
x_400 = lean_ctor_get_uint8(x_283, 5);
x_401 = lean_ctor_get_uint8(x_283, 6);
x_402 = lean_ctor_get_uint8(x_283, 7);
x_403 = lean_ctor_get_uint8(x_283, 8);
x_404 = lean_ctor_get_uint8(x_283, 10);
x_405 = lean_ctor_get_uint8(x_283, 11);
x_406 = lean_ctor_get_uint8(x_283, 12);
lean_dec(x_283);
x_407 = 1;
x_408 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_408, 0, x_395);
lean_ctor_set_uint8(x_408, 1, x_396);
lean_ctor_set_uint8(x_408, 2, x_397);
lean_ctor_set_uint8(x_408, 3, x_398);
lean_ctor_set_uint8(x_408, 4, x_399);
lean_ctor_set_uint8(x_408, 5, x_400);
lean_ctor_set_uint8(x_408, 6, x_401);
lean_ctor_set_uint8(x_408, 7, x_402);
lean_ctor_set_uint8(x_408, 8, x_403);
lean_ctor_set_uint8(x_408, 9, x_407);
lean_ctor_set_uint8(x_408, 10, x_404);
lean_ctor_set_uint8(x_408, 11, x_405);
lean_ctor_set_uint8(x_408, 12, x_406);
x_409 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_287);
lean_ctor_set(x_409, 2, x_288);
lean_ctor_set(x_409, 3, x_289);
lean_ctor_set(x_409, 4, x_290);
lean_ctor_set(x_409, 5, x_291);
lean_ctor_set_uint8(x_409, sizeof(void*)*6, x_393);
lean_ctor_set_uint8(x_409, sizeof(void*)*6 + 1, x_394);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_410 = l_Lean_Meta_mkNoConfusion(x_270, x_18, x_409, x_5, x_6, x_7, x_284);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; uint8_t x_417; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
lean_dec(x_410);
x_413 = lean_ctor_get(x_285, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_413, 0);
lean_inc(x_414);
lean_dec(x_413);
x_415 = lean_ctor_get(x_286, 0);
lean_inc(x_415);
lean_dec(x_286);
x_416 = lean_ctor_get(x_415, 0);
lean_inc(x_416);
lean_dec(x_415);
x_417 = lean_name_eq(x_414, x_416);
lean_dec(x_416);
lean_dec(x_414);
if (x_417 == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_285);
lean_dec(x_3);
lean_dec(x_2);
x_418 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_411, x_4, x_5, x_6, x_7, x_412);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_419 = lean_ctor_get(x_418, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 lean_ctor_release(x_418, 1);
 x_420 = x_418;
} else {
 lean_dec_ref(x_418);
 x_420 = lean_box(0);
}
x_421 = lean_box(0);
if (lean_is_scalar(x_420)) {
 x_422 = lean_alloc_ctor(0, 2, 0);
} else {
 x_422 = x_420;
}
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_419);
return x_422;
}
else
{
lean_object* x_423; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_411);
x_423 = lean_infer_type(x_411, x_4, x_5, x_6, x_7, x_412);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
lean_dec(x_423);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_426 = l_Lean_Meta_whnfD(x_424, x_4, x_5, x_6, x_7, x_425);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; 
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
if (lean_obj_tag(x_427) == 7)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_2);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec(x_426);
x_429 = lean_ctor_get(x_427, 1);
lean_inc(x_429);
lean_dec(x_427);
x_430 = l_Lean_Expr_headBeta(x_429);
lean_inc(x_1);
x_431 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_428);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
x_433 = lean_ctor_get(x_431, 1);
lean_inc(x_433);
lean_dec(x_431);
lean_inc(x_4);
x_434 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_430, x_432, x_4, x_5, x_6, x_7, x_433);
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_434, 1);
lean_inc(x_436);
lean_dec(x_434);
lean_inc(x_435);
x_437 = l_Lean_Expr_app___override(x_411, x_435);
x_438 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_437, x_4, x_5, x_6, x_7, x_436);
x_439 = lean_ctor_get(x_438, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_438)) {
 lean_ctor_release(x_438, 0);
 lean_ctor_release(x_438, 1);
 x_440 = x_438;
} else {
 lean_dec_ref(x_438);
 x_440 = lean_box(0);
}
x_441 = l_Lean_Expr_mvarId_x21(x_435);
lean_dec(x_435);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_442 = l_Lean_MVarId_tryClear(x_441, x_3, x_4, x_5, x_6, x_7, x_439);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
lean_inc(x_285);
x_445 = l_Lean_Meta_getCtorNumPropFields(x_285, x_4, x_5, x_6, x_7, x_444);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_448 = x_445;
} else {
 lean_dec_ref(x_445);
 x_448 = lean_box(0);
}
x_449 = lean_ctor_get(x_285, 4);
lean_inc(x_449);
lean_dec(x_285);
x_450 = lean_nat_sub(x_449, x_446);
lean_dec(x_446);
lean_dec(x_449);
if (lean_is_scalar(x_440)) {
 x_451 = lean_alloc_ctor(1, 2, 0);
} else {
 x_451 = x_440;
 lean_ctor_set_tag(x_451, 1);
}
lean_ctor_set(x_451, 0, x_443);
lean_ctor_set(x_451, 1, x_450);
if (lean_is_scalar(x_448)) {
 x_452 = lean_alloc_ctor(0, 2, 0);
} else {
 x_452 = x_448;
}
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_447);
return x_452;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
lean_dec(x_443);
lean_dec(x_440);
lean_dec(x_285);
x_453 = lean_ctor_get(x_445, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_445, 1);
lean_inc(x_454);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_455 = x_445;
} else {
 lean_dec_ref(x_445);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(1, 2, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_453);
lean_ctor_set(x_456, 1, x_454);
return x_456;
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_440);
lean_dec(x_285);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_457 = lean_ctor_get(x_442, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_442, 1);
lean_inc(x_458);
if (lean_is_exclusive(x_442)) {
 lean_ctor_release(x_442, 0);
 lean_ctor_release(x_442, 1);
 x_459 = x_442;
} else {
 lean_dec_ref(x_442);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(1, 2, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_457);
lean_ctor_set(x_460, 1, x_458);
return x_460;
}
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
lean_dec(x_430);
lean_dec(x_411);
lean_dec(x_285);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_461 = lean_ctor_get(x_431, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_431, 1);
lean_inc(x_462);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_463 = x_431;
} else {
 lean_dec_ref(x_431);
 x_463 = lean_box(0);
}
if (lean_is_scalar(x_463)) {
 x_464 = lean_alloc_ctor(1, 2, 0);
} else {
 x_464 = x_463;
}
lean_ctor_set(x_464, 0, x_461);
lean_ctor_set(x_464, 1, x_462);
return x_464;
}
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; 
lean_dec(x_427);
lean_dec(x_411);
lean_dec(x_285);
lean_dec(x_3);
x_465 = lean_ctor_get(x_426, 1);
lean_inc(x_465);
lean_dec(x_426);
x_466 = l_Lean_Meta_injectionCore___lambda__1___closed__16;
x_467 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_466, x_4, x_5, x_6, x_7, x_465);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_467;
}
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
lean_dec(x_411);
lean_dec(x_285);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_468 = lean_ctor_get(x_426, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_426, 1);
lean_inc(x_469);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 x_470 = x_426;
} else {
 lean_dec_ref(x_426);
 x_470 = lean_box(0);
}
if (lean_is_scalar(x_470)) {
 x_471 = lean_alloc_ctor(1, 2, 0);
} else {
 x_471 = x_470;
}
lean_ctor_set(x_471, 0, x_468);
lean_ctor_set(x_471, 1, x_469);
return x_471;
}
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
lean_dec(x_411);
lean_dec(x_285);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_472 = lean_ctor_get(x_423, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_423, 1);
lean_inc(x_473);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_474 = x_423;
} else {
 lean_dec_ref(x_423);
 x_474 = lean_box(0);
}
if (lean_is_scalar(x_474)) {
 x_475 = lean_alloc_ctor(1, 2, 0);
} else {
 x_475 = x_474;
}
lean_ctor_set(x_475, 0, x_472);
lean_ctor_set(x_475, 1, x_473);
return x_475;
}
}
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_476 = lean_ctor_get(x_410, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_410, 1);
lean_inc(x_477);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_478 = x_410;
} else {
 lean_dec_ref(x_410);
 x_478 = lean_box(0);
}
if (lean_is_scalar(x_478)) {
 x_479 = lean_alloc_ctor(1, 2, 0);
} else {
 x_479 = x_478;
}
lean_ctor_set(x_479, 0, x_476);
lean_ctor_set(x_479, 1, x_477);
return x_479;
}
}
}
}
}
else
{
uint8_t x_480; 
lean_dec(x_273);
lean_dec(x_270);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_480 = !lean_is_exclusive(x_275);
if (x_480 == 0)
{
return x_275;
}
else
{
lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_481 = lean_ctor_get(x_275, 0);
x_482 = lean_ctor_get(x_275, 1);
lean_inc(x_482);
lean_inc(x_481);
lean_dec(x_275);
x_483 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_483, 0, x_481);
lean_ctor_set(x_483, 1, x_482);
return x_483;
}
}
}
else
{
uint8_t x_484; 
lean_dec(x_270);
lean_dec(x_259);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_484 = !lean_is_exclusive(x_272);
if (x_484 == 0)
{
return x_272;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_485 = lean_ctor_get(x_272, 0);
x_486 = lean_ctor_get(x_272, 1);
lean_inc(x_486);
lean_inc(x_485);
lean_dec(x_272);
x_487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_487, 0, x_485);
lean_ctor_set(x_487, 1, x_486);
return x_487;
}
}
}
else
{
uint8_t x_488; 
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_488 = !lean_is_exclusive(x_269);
if (x_488 == 0)
{
return x_269;
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; 
x_489 = lean_ctor_get(x_269, 0);
x_490 = lean_ctor_get(x_269, 1);
lean_inc(x_490);
lean_inc(x_489);
lean_dec(x_269);
x_491 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_491, 0, x_489);
lean_ctor_set(x_491, 1, x_490);
return x_491;
}
}
}
}
else
{
lean_object* x_492; lean_object* x_493; 
lean_dec(x_258);
lean_dec(x_16);
x_492 = lean_ctor_get(x_260, 1);
lean_inc(x_492);
lean_dec(x_260);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_493 = l_Lean_Meta_mkEq(x_257, x_259, x_4, x_5, x_6, x_7, x_492);
if (lean_obj_tag(x_493) == 0)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; 
x_494 = lean_ctor_get(x_493, 0);
lean_inc(x_494);
x_495 = lean_ctor_get(x_493, 1);
lean_inc(x_495);
lean_dec(x_493);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_496 = l_Lean_Meta_mkEqOfHEq(x_18, x_4, x_5, x_6, x_7, x_495);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; uint8_t x_501; 
x_497 = lean_ctor_get(x_496, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_496, 1);
lean_inc(x_498);
lean_dec(x_496);
x_499 = l_Lean_Meta_injectionCore___lambda__1___closed__4;
x_500 = lean_unsigned_to_nat(3u);
x_501 = l_Lean_Expr_isAppOfArity(x_494, x_499, x_500);
if (x_501 == 0)
{
lean_object* x_502; lean_object* x_503; 
lean_dec(x_497);
lean_dec(x_494);
lean_dec(x_3);
x_502 = l_Lean_Meta_injectionCore___lambda__1___closed__8;
x_503 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_502, x_4, x_5, x_6, x_7, x_498);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_503;
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
x_504 = l_Lean_Expr_appFn_x21(x_494);
x_505 = l_Lean_Expr_appArg_x21(x_504);
lean_dec(x_504);
x_506 = l_Lean_Expr_appArg_x21(x_494);
lean_dec(x_494);
lean_inc(x_1);
x_507 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_498);
if (lean_obj_tag(x_507) == 0)
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_508 = lean_ctor_get(x_507, 0);
lean_inc(x_508);
x_509 = lean_ctor_get(x_507, 1);
lean_inc(x_509);
lean_dec(x_507);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_510 = l_Lean_Meta_isConstructorApp_x27_x3f(x_505, x_4, x_5, x_6, x_7, x_509);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_510, 1);
lean_inc(x_512);
lean_dec(x_510);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_513 = l_Lean_Meta_isConstructorApp_x27_x3f(x_506, x_4, x_5, x_6, x_7, x_512);
if (lean_obj_tag(x_513) == 0)
{
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
lean_dec(x_508);
lean_dec(x_497);
lean_dec(x_3);
x_514 = lean_ctor_get(x_513, 1);
lean_inc(x_514);
lean_dec(x_513);
x_515 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_516 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_515, x_4, x_5, x_6, x_7, x_514);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_516;
}
else
{
lean_object* x_517; 
x_517 = lean_ctor_get(x_513, 0);
lean_inc(x_517);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
lean_dec(x_511);
lean_dec(x_508);
lean_dec(x_497);
lean_dec(x_3);
x_518 = lean_ctor_get(x_513, 1);
lean_inc(x_518);
lean_dec(x_513);
x_519 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_520 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_519, x_4, x_5, x_6, x_7, x_518);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_520;
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; uint8_t x_530; 
x_521 = lean_ctor_get(x_4, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_513, 1);
lean_inc(x_522);
lean_dec(x_513);
x_523 = lean_ctor_get(x_511, 0);
lean_inc(x_523);
lean_dec(x_511);
x_524 = lean_ctor_get(x_517, 0);
lean_inc(x_524);
lean_dec(x_517);
x_525 = lean_ctor_get(x_4, 1);
lean_inc(x_525);
x_526 = lean_ctor_get(x_4, 2);
lean_inc(x_526);
x_527 = lean_ctor_get(x_4, 3);
lean_inc(x_527);
x_528 = lean_ctor_get(x_4, 4);
lean_inc(x_528);
x_529 = lean_ctor_get(x_4, 5);
lean_inc(x_529);
x_530 = !lean_is_exclusive(x_521);
if (x_530 == 0)
{
uint8_t x_531; uint8_t x_532; uint8_t x_533; lean_object* x_534; lean_object* x_535; 
x_531 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_532 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_533 = 1;
lean_ctor_set_uint8(x_521, 9, x_533);
x_534 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_534, 0, x_521);
lean_ctor_set(x_534, 1, x_525);
lean_ctor_set(x_534, 2, x_526);
lean_ctor_set(x_534, 3, x_527);
lean_ctor_set(x_534, 4, x_528);
lean_ctor_set(x_534, 5, x_529);
lean_ctor_set_uint8(x_534, sizeof(void*)*6, x_531);
lean_ctor_set_uint8(x_534, sizeof(void*)*6 + 1, x_532);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_535 = l_Lean_Meta_mkNoConfusion(x_508, x_497, x_534, x_5, x_6, x_7, x_522);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; uint8_t x_542; 
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_535, 1);
lean_inc(x_537);
lean_dec(x_535);
x_538 = lean_ctor_get(x_523, 0);
lean_inc(x_538);
x_539 = lean_ctor_get(x_538, 0);
lean_inc(x_539);
lean_dec(x_538);
x_540 = lean_ctor_get(x_524, 0);
lean_inc(x_540);
lean_dec(x_524);
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
lean_dec(x_540);
x_542 = lean_name_eq(x_539, x_541);
lean_dec(x_541);
lean_dec(x_539);
if (x_542 == 0)
{
lean_object* x_543; uint8_t x_544; 
lean_dec(x_523);
lean_dec(x_3);
lean_dec(x_2);
x_543 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_536, x_4, x_5, x_6, x_7, x_537);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_544 = !lean_is_exclusive(x_543);
if (x_544 == 0)
{
lean_object* x_545; lean_object* x_546; 
x_545 = lean_ctor_get(x_543, 0);
lean_dec(x_545);
x_546 = lean_box(0);
lean_ctor_set(x_543, 0, x_546);
return x_543;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_547 = lean_ctor_get(x_543, 1);
lean_inc(x_547);
lean_dec(x_543);
x_548 = lean_box(0);
x_549 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_549, 0, x_548);
lean_ctor_set(x_549, 1, x_547);
return x_549;
}
}
else
{
lean_object* x_550; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_536);
x_550 = lean_infer_type(x_536, x_4, x_5, x_6, x_7, x_537);
if (lean_obj_tag(x_550) == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_551 = lean_ctor_get(x_550, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_550, 1);
lean_inc(x_552);
lean_dec(x_550);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_553 = l_Lean_Meta_whnfD(x_551, x_4, x_5, x_6, x_7, x_552);
if (lean_obj_tag(x_553) == 0)
{
lean_object* x_554; 
x_554 = lean_ctor_get(x_553, 0);
lean_inc(x_554);
if (lean_obj_tag(x_554) == 7)
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; 
lean_dec(x_2);
x_555 = lean_ctor_get(x_553, 1);
lean_inc(x_555);
lean_dec(x_553);
x_556 = lean_ctor_get(x_554, 1);
lean_inc(x_556);
lean_dec(x_554);
x_557 = l_Lean_Expr_headBeta(x_556);
lean_inc(x_1);
x_558 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_555);
if (lean_obj_tag(x_558) == 0)
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; uint8_t x_566; 
x_559 = lean_ctor_get(x_558, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_558, 1);
lean_inc(x_560);
lean_dec(x_558);
lean_inc(x_4);
x_561 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_557, x_559, x_4, x_5, x_6, x_7, x_560);
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_561, 1);
lean_inc(x_563);
lean_dec(x_561);
lean_inc(x_562);
x_564 = l_Lean_Expr_app___override(x_536, x_562);
x_565 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_564, x_4, x_5, x_6, x_7, x_563);
x_566 = !lean_is_exclusive(x_565);
if (x_566 == 0)
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_567 = lean_ctor_get(x_565, 1);
x_568 = lean_ctor_get(x_565, 0);
lean_dec(x_568);
x_569 = l_Lean_Expr_mvarId_x21(x_562);
lean_dec(x_562);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_570 = l_Lean_MVarId_tryClear(x_569, x_3, x_4, x_5, x_6, x_7, x_567);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_570, 1);
lean_inc(x_572);
lean_dec(x_570);
lean_inc(x_523);
x_573 = l_Lean_Meta_getCtorNumPropFields(x_523, x_4, x_5, x_6, x_7, x_572);
if (lean_obj_tag(x_573) == 0)
{
uint8_t x_574; 
x_574 = !lean_is_exclusive(x_573);
if (x_574 == 0)
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_575 = lean_ctor_get(x_573, 0);
x_576 = lean_ctor_get(x_523, 4);
lean_inc(x_576);
lean_dec(x_523);
x_577 = lean_nat_sub(x_576, x_575);
lean_dec(x_575);
lean_dec(x_576);
lean_ctor_set_tag(x_565, 1);
lean_ctor_set(x_565, 1, x_577);
lean_ctor_set(x_565, 0, x_571);
lean_ctor_set(x_573, 0, x_565);
return x_573;
}
else
{
lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_578 = lean_ctor_get(x_573, 0);
x_579 = lean_ctor_get(x_573, 1);
lean_inc(x_579);
lean_inc(x_578);
lean_dec(x_573);
x_580 = lean_ctor_get(x_523, 4);
lean_inc(x_580);
lean_dec(x_523);
x_581 = lean_nat_sub(x_580, x_578);
lean_dec(x_578);
lean_dec(x_580);
lean_ctor_set_tag(x_565, 1);
lean_ctor_set(x_565, 1, x_581);
lean_ctor_set(x_565, 0, x_571);
x_582 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_582, 0, x_565);
lean_ctor_set(x_582, 1, x_579);
return x_582;
}
}
else
{
uint8_t x_583; 
lean_dec(x_571);
lean_free_object(x_565);
lean_dec(x_523);
x_583 = !lean_is_exclusive(x_573);
if (x_583 == 0)
{
return x_573;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_573, 0);
x_585 = lean_ctor_get(x_573, 1);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_573);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_584);
lean_ctor_set(x_586, 1, x_585);
return x_586;
}
}
}
else
{
uint8_t x_587; 
lean_free_object(x_565);
lean_dec(x_523);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_587 = !lean_is_exclusive(x_570);
if (x_587 == 0)
{
return x_570;
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_588 = lean_ctor_get(x_570, 0);
x_589 = lean_ctor_get(x_570, 1);
lean_inc(x_589);
lean_inc(x_588);
lean_dec(x_570);
x_590 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_590, 0, x_588);
lean_ctor_set(x_590, 1, x_589);
return x_590;
}
}
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; 
x_591 = lean_ctor_get(x_565, 1);
lean_inc(x_591);
lean_dec(x_565);
x_592 = l_Lean_Expr_mvarId_x21(x_562);
lean_dec(x_562);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_593 = l_Lean_MVarId_tryClear(x_592, x_3, x_4, x_5, x_6, x_7, x_591);
if (lean_obj_tag(x_593) == 0)
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; 
x_594 = lean_ctor_get(x_593, 0);
lean_inc(x_594);
x_595 = lean_ctor_get(x_593, 1);
lean_inc(x_595);
lean_dec(x_593);
lean_inc(x_523);
x_596 = l_Lean_Meta_getCtorNumPropFields(x_523, x_4, x_5, x_6, x_7, x_595);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_597 = lean_ctor_get(x_596, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_596, 1);
lean_inc(x_598);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_599 = x_596;
} else {
 lean_dec_ref(x_596);
 x_599 = lean_box(0);
}
x_600 = lean_ctor_get(x_523, 4);
lean_inc(x_600);
lean_dec(x_523);
x_601 = lean_nat_sub(x_600, x_597);
lean_dec(x_597);
lean_dec(x_600);
x_602 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_602, 0, x_594);
lean_ctor_set(x_602, 1, x_601);
if (lean_is_scalar(x_599)) {
 x_603 = lean_alloc_ctor(0, 2, 0);
} else {
 x_603 = x_599;
}
lean_ctor_set(x_603, 0, x_602);
lean_ctor_set(x_603, 1, x_598);
return x_603;
}
else
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
lean_dec(x_594);
lean_dec(x_523);
x_604 = lean_ctor_get(x_596, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_596, 1);
lean_inc(x_605);
if (lean_is_exclusive(x_596)) {
 lean_ctor_release(x_596, 0);
 lean_ctor_release(x_596, 1);
 x_606 = x_596;
} else {
 lean_dec_ref(x_596);
 x_606 = lean_box(0);
}
if (lean_is_scalar(x_606)) {
 x_607 = lean_alloc_ctor(1, 2, 0);
} else {
 x_607 = x_606;
}
lean_ctor_set(x_607, 0, x_604);
lean_ctor_set(x_607, 1, x_605);
return x_607;
}
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_dec(x_523);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_608 = lean_ctor_get(x_593, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_593, 1);
lean_inc(x_609);
if (lean_is_exclusive(x_593)) {
 lean_ctor_release(x_593, 0);
 lean_ctor_release(x_593, 1);
 x_610 = x_593;
} else {
 lean_dec_ref(x_593);
 x_610 = lean_box(0);
}
if (lean_is_scalar(x_610)) {
 x_611 = lean_alloc_ctor(1, 2, 0);
} else {
 x_611 = x_610;
}
lean_ctor_set(x_611, 0, x_608);
lean_ctor_set(x_611, 1, x_609);
return x_611;
}
}
}
else
{
uint8_t x_612; 
lean_dec(x_557);
lean_dec(x_536);
lean_dec(x_523);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_612 = !lean_is_exclusive(x_558);
if (x_612 == 0)
{
return x_558;
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_613 = lean_ctor_get(x_558, 0);
x_614 = lean_ctor_get(x_558, 1);
lean_inc(x_614);
lean_inc(x_613);
lean_dec(x_558);
x_615 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_615, 0, x_613);
lean_ctor_set(x_615, 1, x_614);
return x_615;
}
}
}
else
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; 
lean_dec(x_554);
lean_dec(x_536);
lean_dec(x_523);
lean_dec(x_3);
x_616 = lean_ctor_get(x_553, 1);
lean_inc(x_616);
lean_dec(x_553);
x_617 = l_Lean_Meta_injectionCore___lambda__1___closed__16;
x_618 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_617, x_4, x_5, x_6, x_7, x_616);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_618;
}
}
else
{
uint8_t x_619; 
lean_dec(x_536);
lean_dec(x_523);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_619 = !lean_is_exclusive(x_553);
if (x_619 == 0)
{
return x_553;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_620 = lean_ctor_get(x_553, 0);
x_621 = lean_ctor_get(x_553, 1);
lean_inc(x_621);
lean_inc(x_620);
lean_dec(x_553);
x_622 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_622, 0, x_620);
lean_ctor_set(x_622, 1, x_621);
return x_622;
}
}
}
else
{
uint8_t x_623; 
lean_dec(x_536);
lean_dec(x_523);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_623 = !lean_is_exclusive(x_550);
if (x_623 == 0)
{
return x_550;
}
else
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; 
x_624 = lean_ctor_get(x_550, 0);
x_625 = lean_ctor_get(x_550, 1);
lean_inc(x_625);
lean_inc(x_624);
lean_dec(x_550);
x_626 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_626, 0, x_624);
lean_ctor_set(x_626, 1, x_625);
return x_626;
}
}
}
}
else
{
uint8_t x_627; 
lean_dec(x_524);
lean_dec(x_523);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_627 = !lean_is_exclusive(x_535);
if (x_627 == 0)
{
return x_535;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = lean_ctor_get(x_535, 0);
x_629 = lean_ctor_get(x_535, 1);
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_535);
x_630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set(x_630, 1, x_629);
return x_630;
}
}
}
else
{
uint8_t x_631; uint8_t x_632; uint8_t x_633; uint8_t x_634; uint8_t x_635; uint8_t x_636; uint8_t x_637; uint8_t x_638; uint8_t x_639; uint8_t x_640; uint8_t x_641; uint8_t x_642; uint8_t x_643; uint8_t x_644; uint8_t x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_631 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_632 = lean_ctor_get_uint8(x_4, sizeof(void*)*6 + 1);
x_633 = lean_ctor_get_uint8(x_521, 0);
x_634 = lean_ctor_get_uint8(x_521, 1);
x_635 = lean_ctor_get_uint8(x_521, 2);
x_636 = lean_ctor_get_uint8(x_521, 3);
x_637 = lean_ctor_get_uint8(x_521, 4);
x_638 = lean_ctor_get_uint8(x_521, 5);
x_639 = lean_ctor_get_uint8(x_521, 6);
x_640 = lean_ctor_get_uint8(x_521, 7);
x_641 = lean_ctor_get_uint8(x_521, 8);
x_642 = lean_ctor_get_uint8(x_521, 10);
x_643 = lean_ctor_get_uint8(x_521, 11);
x_644 = lean_ctor_get_uint8(x_521, 12);
lean_dec(x_521);
x_645 = 1;
x_646 = lean_alloc_ctor(0, 0, 13);
lean_ctor_set_uint8(x_646, 0, x_633);
lean_ctor_set_uint8(x_646, 1, x_634);
lean_ctor_set_uint8(x_646, 2, x_635);
lean_ctor_set_uint8(x_646, 3, x_636);
lean_ctor_set_uint8(x_646, 4, x_637);
lean_ctor_set_uint8(x_646, 5, x_638);
lean_ctor_set_uint8(x_646, 6, x_639);
lean_ctor_set_uint8(x_646, 7, x_640);
lean_ctor_set_uint8(x_646, 8, x_641);
lean_ctor_set_uint8(x_646, 9, x_645);
lean_ctor_set_uint8(x_646, 10, x_642);
lean_ctor_set_uint8(x_646, 11, x_643);
lean_ctor_set_uint8(x_646, 12, x_644);
x_647 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_647, 0, x_646);
lean_ctor_set(x_647, 1, x_525);
lean_ctor_set(x_647, 2, x_526);
lean_ctor_set(x_647, 3, x_527);
lean_ctor_set(x_647, 4, x_528);
lean_ctor_set(x_647, 5, x_529);
lean_ctor_set_uint8(x_647, sizeof(void*)*6, x_631);
lean_ctor_set_uint8(x_647, sizeof(void*)*6 + 1, x_632);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_648 = l_Lean_Meta_mkNoConfusion(x_508, x_497, x_647, x_5, x_6, x_7, x_522);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; uint8_t x_655; 
x_649 = lean_ctor_get(x_648, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_648, 1);
lean_inc(x_650);
lean_dec(x_648);
x_651 = lean_ctor_get(x_523, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_651, 0);
lean_inc(x_652);
lean_dec(x_651);
x_653 = lean_ctor_get(x_524, 0);
lean_inc(x_653);
lean_dec(x_524);
x_654 = lean_ctor_get(x_653, 0);
lean_inc(x_654);
lean_dec(x_653);
x_655 = lean_name_eq(x_652, x_654);
lean_dec(x_654);
lean_dec(x_652);
if (x_655 == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
lean_dec(x_523);
lean_dec(x_3);
lean_dec(x_2);
x_656 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_649, x_4, x_5, x_6, x_7, x_650);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_657 = lean_ctor_get(x_656, 1);
lean_inc(x_657);
if (lean_is_exclusive(x_656)) {
 lean_ctor_release(x_656, 0);
 lean_ctor_release(x_656, 1);
 x_658 = x_656;
} else {
 lean_dec_ref(x_656);
 x_658 = lean_box(0);
}
x_659 = lean_box(0);
if (lean_is_scalar(x_658)) {
 x_660 = lean_alloc_ctor(0, 2, 0);
} else {
 x_660 = x_658;
}
lean_ctor_set(x_660, 0, x_659);
lean_ctor_set(x_660, 1, x_657);
return x_660;
}
else
{
lean_object* x_661; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_649);
x_661 = lean_infer_type(x_649, x_4, x_5, x_6, x_7, x_650);
if (lean_obj_tag(x_661) == 0)
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_661, 1);
lean_inc(x_663);
lean_dec(x_661);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_664 = l_Lean_Meta_whnfD(x_662, x_4, x_5, x_6, x_7, x_663);
if (lean_obj_tag(x_664) == 0)
{
lean_object* x_665; 
x_665 = lean_ctor_get(x_664, 0);
lean_inc(x_665);
if (lean_obj_tag(x_665) == 7)
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
lean_dec(x_2);
x_666 = lean_ctor_get(x_664, 1);
lean_inc(x_666);
lean_dec(x_664);
x_667 = lean_ctor_get(x_665, 1);
lean_inc(x_667);
lean_dec(x_665);
x_668 = l_Lean_Expr_headBeta(x_667);
lean_inc(x_1);
x_669 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_666);
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_669, 1);
lean_inc(x_671);
lean_dec(x_669);
lean_inc(x_4);
x_672 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_668, x_670, x_4, x_5, x_6, x_7, x_671);
x_673 = lean_ctor_get(x_672, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_672, 1);
lean_inc(x_674);
lean_dec(x_672);
lean_inc(x_673);
x_675 = l_Lean_Expr_app___override(x_649, x_673);
x_676 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_675, x_4, x_5, x_6, x_7, x_674);
x_677 = lean_ctor_get(x_676, 1);
lean_inc(x_677);
if (lean_is_exclusive(x_676)) {
 lean_ctor_release(x_676, 0);
 lean_ctor_release(x_676, 1);
 x_678 = x_676;
} else {
 lean_dec_ref(x_676);
 x_678 = lean_box(0);
}
x_679 = l_Lean_Expr_mvarId_x21(x_673);
lean_dec(x_673);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_680 = l_Lean_MVarId_tryClear(x_679, x_3, x_4, x_5, x_6, x_7, x_677);
if (lean_obj_tag(x_680) == 0)
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; 
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
lean_dec(x_680);
lean_inc(x_523);
x_683 = l_Lean_Meta_getCtorNumPropFields(x_523, x_4, x_5, x_6, x_7, x_682);
if (lean_obj_tag(x_683) == 0)
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_684 = lean_ctor_get(x_683, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_683, 1);
lean_inc(x_685);
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 lean_ctor_release(x_683, 1);
 x_686 = x_683;
} else {
 lean_dec_ref(x_683);
 x_686 = lean_box(0);
}
x_687 = lean_ctor_get(x_523, 4);
lean_inc(x_687);
lean_dec(x_523);
x_688 = lean_nat_sub(x_687, x_684);
lean_dec(x_684);
lean_dec(x_687);
if (lean_is_scalar(x_678)) {
 x_689 = lean_alloc_ctor(1, 2, 0);
} else {
 x_689 = x_678;
 lean_ctor_set_tag(x_689, 1);
}
lean_ctor_set(x_689, 0, x_681);
lean_ctor_set(x_689, 1, x_688);
if (lean_is_scalar(x_686)) {
 x_690 = lean_alloc_ctor(0, 2, 0);
} else {
 x_690 = x_686;
}
lean_ctor_set(x_690, 0, x_689);
lean_ctor_set(x_690, 1, x_685);
return x_690;
}
else
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; 
lean_dec(x_681);
lean_dec(x_678);
lean_dec(x_523);
x_691 = lean_ctor_get(x_683, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_683, 1);
lean_inc(x_692);
if (lean_is_exclusive(x_683)) {
 lean_ctor_release(x_683, 0);
 lean_ctor_release(x_683, 1);
 x_693 = x_683;
} else {
 lean_dec_ref(x_683);
 x_693 = lean_box(0);
}
if (lean_is_scalar(x_693)) {
 x_694 = lean_alloc_ctor(1, 2, 0);
} else {
 x_694 = x_693;
}
lean_ctor_set(x_694, 0, x_691);
lean_ctor_set(x_694, 1, x_692);
return x_694;
}
}
else
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
lean_dec(x_678);
lean_dec(x_523);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_695 = lean_ctor_get(x_680, 0);
lean_inc(x_695);
x_696 = lean_ctor_get(x_680, 1);
lean_inc(x_696);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_697 = x_680;
} else {
 lean_dec_ref(x_680);
 x_697 = lean_box(0);
}
if (lean_is_scalar(x_697)) {
 x_698 = lean_alloc_ctor(1, 2, 0);
} else {
 x_698 = x_697;
}
lean_ctor_set(x_698, 0, x_695);
lean_ctor_set(x_698, 1, x_696);
return x_698;
}
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; 
lean_dec(x_668);
lean_dec(x_649);
lean_dec(x_523);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_699 = lean_ctor_get(x_669, 0);
lean_inc(x_699);
x_700 = lean_ctor_get(x_669, 1);
lean_inc(x_700);
if (lean_is_exclusive(x_669)) {
 lean_ctor_release(x_669, 0);
 lean_ctor_release(x_669, 1);
 x_701 = x_669;
} else {
 lean_dec_ref(x_669);
 x_701 = lean_box(0);
}
if (lean_is_scalar(x_701)) {
 x_702 = lean_alloc_ctor(1, 2, 0);
} else {
 x_702 = x_701;
}
lean_ctor_set(x_702, 0, x_699);
lean_ctor_set(x_702, 1, x_700);
return x_702;
}
}
else
{
lean_object* x_703; lean_object* x_704; lean_object* x_705; 
lean_dec(x_665);
lean_dec(x_649);
lean_dec(x_523);
lean_dec(x_3);
x_703 = lean_ctor_get(x_664, 1);
lean_inc(x_703);
lean_dec(x_664);
x_704 = l_Lean_Meta_injectionCore___lambda__1___closed__16;
x_705 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_704, x_4, x_5, x_6, x_7, x_703);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_705;
}
}
else
{
lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
lean_dec(x_649);
lean_dec(x_523);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_706 = lean_ctor_get(x_664, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_664, 1);
lean_inc(x_707);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 lean_ctor_release(x_664, 1);
 x_708 = x_664;
} else {
 lean_dec_ref(x_664);
 x_708 = lean_box(0);
}
if (lean_is_scalar(x_708)) {
 x_709 = lean_alloc_ctor(1, 2, 0);
} else {
 x_709 = x_708;
}
lean_ctor_set(x_709, 0, x_706);
lean_ctor_set(x_709, 1, x_707);
return x_709;
}
}
else
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
lean_dec(x_649);
lean_dec(x_523);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_710 = lean_ctor_get(x_661, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_661, 1);
lean_inc(x_711);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 x_712 = x_661;
} else {
 lean_dec_ref(x_661);
 x_712 = lean_box(0);
}
if (lean_is_scalar(x_712)) {
 x_713 = lean_alloc_ctor(1, 2, 0);
} else {
 x_713 = x_712;
}
lean_ctor_set(x_713, 0, x_710);
lean_ctor_set(x_713, 1, x_711);
return x_713;
}
}
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; 
lean_dec(x_524);
lean_dec(x_523);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_714 = lean_ctor_get(x_648, 0);
lean_inc(x_714);
x_715 = lean_ctor_get(x_648, 1);
lean_inc(x_715);
if (lean_is_exclusive(x_648)) {
 lean_ctor_release(x_648, 0);
 lean_ctor_release(x_648, 1);
 x_716 = x_648;
} else {
 lean_dec_ref(x_648);
 x_716 = lean_box(0);
}
if (lean_is_scalar(x_716)) {
 x_717 = lean_alloc_ctor(1, 2, 0);
} else {
 x_717 = x_716;
}
lean_ctor_set(x_717, 0, x_714);
lean_ctor_set(x_717, 1, x_715);
return x_717;
}
}
}
}
}
else
{
uint8_t x_718; 
lean_dec(x_511);
lean_dec(x_508);
lean_dec(x_497);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_718 = !lean_is_exclusive(x_513);
if (x_718 == 0)
{
return x_513;
}
else
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; 
x_719 = lean_ctor_get(x_513, 0);
x_720 = lean_ctor_get(x_513, 1);
lean_inc(x_720);
lean_inc(x_719);
lean_dec(x_513);
x_721 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_721, 0, x_719);
lean_ctor_set(x_721, 1, x_720);
return x_721;
}
}
}
else
{
uint8_t x_722; 
lean_dec(x_508);
lean_dec(x_506);
lean_dec(x_497);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_722 = !lean_is_exclusive(x_510);
if (x_722 == 0)
{
return x_510;
}
else
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_723 = lean_ctor_get(x_510, 0);
x_724 = lean_ctor_get(x_510, 1);
lean_inc(x_724);
lean_inc(x_723);
lean_dec(x_510);
x_725 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_725, 0, x_723);
lean_ctor_set(x_725, 1, x_724);
return x_725;
}
}
}
else
{
uint8_t x_726; 
lean_dec(x_506);
lean_dec(x_505);
lean_dec(x_497);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_726 = !lean_is_exclusive(x_507);
if (x_726 == 0)
{
return x_507;
}
else
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; 
x_727 = lean_ctor_get(x_507, 0);
x_728 = lean_ctor_get(x_507, 1);
lean_inc(x_728);
lean_inc(x_727);
lean_dec(x_507);
x_729 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_729, 0, x_727);
lean_ctor_set(x_729, 1, x_728);
return x_729;
}
}
}
}
else
{
uint8_t x_730; 
lean_dec(x_494);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_730 = !lean_is_exclusive(x_496);
if (x_730 == 0)
{
return x_496;
}
else
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; 
x_731 = lean_ctor_get(x_496, 0);
x_732 = lean_ctor_get(x_496, 1);
lean_inc(x_732);
lean_inc(x_731);
lean_dec(x_496);
x_733 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_733, 0, x_731);
lean_ctor_set(x_733, 1, x_732);
return x_733;
}
}
}
else
{
uint8_t x_734; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_734 = !lean_is_exclusive(x_493);
if (x_734 == 0)
{
return x_493;
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; 
x_735 = lean_ctor_get(x_493, 0);
x_736 = lean_ctor_get(x_493, 1);
lean_inc(x_736);
lean_inc(x_735);
lean_dec(x_493);
x_737 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_737, 0, x_735);
lean_ctor_set(x_737, 1, x_736);
return x_737;
}
}
}
}
else
{
uint8_t x_738; 
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_738 = !lean_is_exclusive(x_260);
if (x_738 == 0)
{
return x_260;
}
else
{
lean_object* x_739; lean_object* x_740; lean_object* x_741; 
x_739 = lean_ctor_get(x_260, 0);
x_740 = lean_ctor_get(x_260, 1);
lean_inc(x_740);
lean_inc(x_739);
lean_dec(x_260);
x_741 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_741, 0, x_739);
lean_ctor_set(x_741, 1, x_740);
return x_741;
}
}
}
}
else
{
uint8_t x_742; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_742 = !lean_is_exclusive(x_15);
if (x_742 == 0)
{
return x_15;
}
else
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_743 = lean_ctor_get(x_15, 0);
x_744 = lean_ctor_get(x_15, 1);
lean_inc(x_744);
lean_inc(x_743);
lean_dec(x_15);
x_745 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_745, 0, x_743);
lean_ctor_set(x_745, 1, x_744);
return x_745;
}
}
}
else
{
uint8_t x_746; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_746 = !lean_is_exclusive(x_11);
if (x_746 == 0)
{
return x_11;
}
else
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; 
x_747 = lean_ctor_get(x_11, 0);
x_748 = lean_ctor_get(x_11, 1);
lean_inc(x_748);
lean_inc(x_747);
lean_dec(x_11);
x_749 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_749, 0, x_747);
lean_ctor_set(x_749, 1, x_748);
return x_749;
}
}
}
else
{
uint8_t x_750; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_750 = !lean_is_exclusive(x_9);
if (x_750 == 0)
{
return x_9;
}
else
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_751 = lean_ctor_get(x_9, 0);
x_752 = lean_ctor_get(x_9, 1);
lean_inc(x_752);
lean_inc(x_751);
lean_dec(x_9);
x_753 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_753, 0, x_751);
lean_ctor_set(x_753, 1, x_752);
return x_753;
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
x_12 = lean_nat_dec_eq(x_2, x_11);
if (x_12 == 0)
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_sub(x_2, x_17);
lean_dec(x_2);
x_19 = lean_nat_add(x_18, x_17);
lean_inc(x_6);
lean_inc(x_15);
x_20 = l_Lean_FVarId_getType(x_15, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_23 = l_Lean_Meta_matchEqHEq_x3f(x_21, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
lean_dec(x_18);
lean_dec(x_15);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_2 = x_19;
x_3 = x_16;
x_10 = x_25;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_32 = lean_whnf(x_30, x_6, x_7, x_8, x_9, x_29);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_35 = lean_whnf(x_31, x_6, x_7, x_8, x_9, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_81; 
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
x_81 = l_Lean_Expr_isRawNatLit(x_33);
lean_dec(x_33);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_36);
x_82 = lean_box(0);
x_39 = x_82;
goto block_80;
}
else
{
uint8_t x_83; 
x_83 = l_Lean_Expr_isRawNatLit(x_36);
lean_dec(x_36);
if (x_83 == 0)
{
lean_object* x_84; 
x_84 = lean_box(0);
x_39 = x_84;
goto block_80;
}
else
{
lean_dec(x_38);
lean_dec(x_18);
lean_dec(x_15);
x_2 = x_19;
x_3 = x_16;
x_10 = x_37;
goto _start;
}
}
block_80:
{
lean_object* x_40; lean_object* x_41; lean_object* x_56; 
lean_dec(x_39);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_56 = l_Lean_Meta_injection(x_4, x_15, x_5, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
lean_dec(x_38);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_56, 0);
lean_dec(x_59);
x_60 = lean_box(0);
lean_ctor_set(x_56, 0, x_60);
return x_56;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
lean_dec(x_56);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_ctor_get(x_56, 1);
lean_inc(x_64);
lean_dec(x_56);
x_65 = lean_ctor_get(x_57, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_57, 2);
lean_inc(x_67);
lean_dec(x_57);
x_68 = lean_array_to_list(x_66);
lean_inc(x_16);
x_69 = l_List_appendTR___rarg(x_68, x_16);
lean_inc(x_65);
lean_inc(x_1);
x_70 = lean_alloc_closure((void*)(l_Lean_Meta_injections_go), 10, 5);
lean_closure_set(x_70, 0, x_1);
lean_closure_set(x_70, 1, x_18);
lean_closure_set(x_70, 2, x_69);
lean_closure_set(x_70, 3, x_65);
lean_closure_set(x_70, 4, x_67);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_71 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_65, x_70, x_6, x_7, x_8, x_9, x_64);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
lean_dec(x_38);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
return x_71;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_ctor_get(x_71, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_71);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_71, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_71, 1);
lean_inc(x_77);
lean_dec(x_71);
x_40 = x_76;
x_41 = x_77;
goto block_55;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_18);
x_78 = lean_ctor_get(x_56, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_56, 1);
lean_inc(x_79);
lean_dec(x_56);
x_40 = x_78;
x_41 = x_79;
goto block_55;
}
block_55:
{
uint8_t x_42; 
x_42 = l_Lean_Exception_isInterrupt(x_40);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Exception_isRuntime(x_40);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_40);
lean_dec(x_38);
x_44 = l_Lean_Meta_injections_go(x_1, x_19, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
return x_44;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_44);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_44);
if (x_49 == 0)
{
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_44, 0);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_44);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
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
lean_dec(x_1);
if (lean_is_scalar(x_38)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_38;
 lean_ctor_set_tag(x_53, 1);
}
lean_ctor_set(x_53, 0, x_40);
lean_ctor_set(x_53, 1, x_41);
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
lean_dec(x_1);
if (lean_is_scalar(x_38)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_38;
 lean_ctor_set_tag(x_54, 1);
}
lean_ctor_set(x_54, 0, x_40);
lean_ctor_set(x_54, 1, x_41);
return x_54;
}
}
}
}
else
{
uint8_t x_86; 
lean_dec(x_33);
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
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_35);
if (x_86 == 0)
{
return x_35;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_35, 0);
x_88 = lean_ctor_get(x_35, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_35);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_31);
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
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_32);
if (x_90 == 0)
{
return x_32;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_32, 0);
x_92 = lean_ctor_get(x_32, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_32);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
else
{
uint8_t x_94; 
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
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_23);
if (x_94 == 0)
{
return x_23;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_23, 0);
x_96 = lean_ctor_get(x_23, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_23);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
uint8_t x_98; 
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
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_20);
if (x_98 == 0)
{
return x_20;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_20, 0);
x_100 = lean_ctor_get(x_20, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_20);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_102 = l_Lean_Meta_injections_go___closed__2;
x_103 = l_Lean_Meta_injections_go___closed__6;
x_104 = l_Lean_Meta_throwTacticEx___rarg(x_102, x_1, x_103, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_104;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = l_Lean_LocalContext_getFVarIds(x_9);
lean_dec(x_9);
x_11 = lean_array_to_list(x_10);
lean_inc(x_1);
x_12 = l_Lean_Meta_injections_go(x_1, x_2, x_11, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_injections___lambda__1), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_2);
x_10 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
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
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__13);
l_Lean_Meta_injectionCore___lambda__1___closed__14 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__14();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__14);
l_Lean_Meta_injectionCore___lambda__1___closed__15 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__15();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__15);
l_Lean_Meta_injectionCore___lambda__1___closed__16 = _init_l_Lean_Meta_injectionCore___lambda__1___closed__16();
lean_mark_persistent(l_Lean_Meta_injectionCore___lambda__1___closed__16);
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
