// Lean compiler output
// Module: Lean.Meta.Tactic.Injection
// Imports: Init Lean.Meta.AppBuilder Lean.Meta.MatchUtil Lean.Meta.Tactic.Clear Lean.Meta.Tactic.Subst Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Intro
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
lean_object* l___private_Init_Util_0__outOfBounds___rarg(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEqHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__10;
static lean_object* l_Lean_Meta_injectionCore___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isNatLit(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__1;
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__6;
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR___rarg(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injections_go___closed__5;
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__12;
lean_object* lean_array_to_list(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_FVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_isConstructorApp_x3f(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__4;
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__5;
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__7;
static lean_object* l_Lean_Meta_injectionIntro___closed__1;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__1;
static lean_object* l_Lean_Meta_injectionCore___closed__1;
LEAN_EXPORT lean_object* l_Std_Range_forIn_loop___at_Lean_Meta_getCtorNumPropFields___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
x_29 = l___private_Init_Util_0__outOfBounds___rarg(x_28);
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_getCtorNumPropFields___lambda__1___boxed), 8, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Meta_forallTelescopeReducing___at_Lean_Meta_getParamNames___spec__2___rarg(x_8, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
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
x_1 = lean_mk_string_from_bytes("HEq", 3);
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
x_1 = lean_mk_string_from_bytes("Eq", 2);
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
x_1 = lean_mk_string_from_bytes("equality expected", 17);
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
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("equality of constructor applications expected", 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__8;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__9;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("ill-formed noConfusion auxiliary construction", 45);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__11;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___lambda__1___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_injectionCore___lambda__1___closed__12;
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_6);
lean_inc(x_4);
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
x_25 = l_Lean_Meta_injectionCore___lambda__1___closed__7;
x_26 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_25, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_7);
lean_dec(x_5);
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
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_30 = lean_whnf(x_28, x_4, x_5, x_6, x_7, x_17);
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
x_33 = lean_whnf(x_29, x_4, x_5, x_6, x_7, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_1);
x_36 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_st_ref_get(x_7, x_38);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
lean_dec(x_40);
lean_inc(x_42);
x_43 = l_Lean_Expr_isConstructorApp_x3f(x_42, x_31);
lean_dec(x_31);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_42);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_18);
lean_dec(x_3);
x_44 = l_Lean_Meta_injectionCore___lambda__1___closed__10;
x_45 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_44, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_7);
lean_dec(x_5);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
lean_dec(x_43);
x_47 = l_Lean_Expr_isConstructorApp_x3f(x_42, x_34);
lean_dec(x_34);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_46);
lean_dec(x_37);
lean_dec(x_18);
lean_dec(x_3);
x_48 = l_Lean_Meta_injectionCore___lambda__1___closed__10;
x_49 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_48, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_7);
lean_dec(x_5);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_47, 0);
lean_inc(x_50);
lean_dec(x_47);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_51 = l_Lean_Meta_mkNoConfusion(x_37, x_18, x_4, x_5, x_6, x_7, x_41);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_46, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_ctor_get(x_50, 0);
lean_inc(x_56);
lean_dec(x_50);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
x_58 = lean_name_eq(x_55, x_57);
lean_dec(x_57);
lean_dec(x_55);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
lean_dec(x_46);
lean_dec(x_3);
lean_dec(x_2);
x_59 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_52, x_4, x_5, x_6, x_7, x_53);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
lean_dec(x_61);
x_62 = lean_box(0);
lean_ctor_set(x_59, 0, x_62);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = lean_box(0);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
}
else
{
lean_object* x_66; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_52);
x_66 = lean_infer_type(x_52, x_4, x_5, x_6, x_7, x_53);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_69 = lean_whnf(x_67, x_4, x_5, x_6, x_7, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 7)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_2);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = l_Lean_Expr_headBeta(x_72);
lean_inc(x_1);
x_74 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_71);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_4);
x_77 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_73, x_75, x_4, x_5, x_6, x_7, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
lean_inc(x_78);
x_80 = l_Lean_Expr_app___override(x_52, x_78);
x_81 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_80, x_4, x_5, x_6, x_7, x_79);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l_Lean_Expr_mvarId_x21(x_78);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_84 = l_Lean_MVarId_tryClear(x_83, x_3, x_4, x_5, x_6, x_7, x_82);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
lean_inc(x_46);
x_87 = l_Lean_Meta_getCtorNumPropFields(x_46, x_4, x_5, x_6, x_7, x_86);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_ctor_get(x_46, 4);
lean_inc(x_90);
lean_dec(x_46);
x_91 = lean_nat_sub(x_90, x_89);
lean_dec(x_89);
lean_dec(x_90);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_85);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_87, 0, x_92);
return x_87;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_93 = lean_ctor_get(x_87, 0);
x_94 = lean_ctor_get(x_87, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_87);
x_95 = lean_ctor_get(x_46, 4);
lean_inc(x_95);
lean_dec(x_46);
x_96 = lean_nat_sub(x_95, x_93);
lean_dec(x_93);
lean_dec(x_95);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_85);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
return x_98;
}
}
else
{
uint8_t x_99; 
lean_dec(x_85);
lean_dec(x_46);
x_99 = !lean_is_exclusive(x_87);
if (x_99 == 0)
{
return x_87;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_87, 0);
x_101 = lean_ctor_get(x_87, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_87);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
else
{
uint8_t x_103; 
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_103 = !lean_is_exclusive(x_84);
if (x_103 == 0)
{
return x_84;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_84, 0);
x_105 = lean_ctor_get(x_84, 1);
lean_inc(x_105);
lean_inc(x_104);
lean_dec(x_84);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_73);
lean_dec(x_52);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_74);
if (x_107 == 0)
{
return x_74;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_74, 0);
x_109 = lean_ctor_get(x_74, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_74);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_70);
lean_dec(x_52);
lean_dec(x_46);
lean_dec(x_3);
x_111 = lean_ctor_get(x_69, 1);
lean_inc(x_111);
lean_dec(x_69);
x_112 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_113 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_112, x_4, x_5, x_6, x_7, x_111);
lean_dec(x_7);
lean_dec(x_5);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_52);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_69);
if (x_114 == 0)
{
return x_69;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_69, 0);
x_116 = lean_ctor_get(x_69, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_69);
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
lean_dec(x_52);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_66);
if (x_118 == 0)
{
return x_66;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_66, 0);
x_120 = lean_ctor_get(x_66, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_66);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
}
else
{
uint8_t x_122; 
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_51);
if (x_122 == 0)
{
return x_51;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_51, 0);
x_124 = lean_ctor_get(x_51, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_51);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
}
else
{
uint8_t x_126; 
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
x_126 = !lean_is_exclusive(x_36);
if (x_126 == 0)
{
return x_36;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_36, 0);
x_128 = lean_ctor_get(x_36, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_36);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
uint8_t x_130; 
lean_dec(x_31);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_130 = !lean_is_exclusive(x_33);
if (x_130 == 0)
{
return x_33;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_33, 0);
x_132 = lean_ctor_get(x_33, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_33);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
uint8_t x_134; 
lean_dec(x_29);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_134 = !lean_is_exclusive(x_30);
if (x_134 == 0)
{
return x_30;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_30, 0);
x_136 = lean_ctor_get(x_30, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_30);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_138 = l_Lean_Expr_appFn_x21(x_16);
x_139 = l_Lean_Expr_appFn_x21(x_138);
x_140 = l_Lean_Expr_appFn_x21(x_139);
x_141 = l_Lean_Expr_appArg_x21(x_140);
lean_dec(x_140);
x_142 = l_Lean_Expr_appArg_x21(x_139);
lean_dec(x_139);
x_143 = l_Lean_Expr_appArg_x21(x_138);
lean_dec(x_138);
x_144 = l_Lean_Expr_appArg_x21(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_143);
x_145 = l_Lean_Meta_isExprDefEq(x_141, x_143, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; uint8_t x_147; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_unbox(x_146);
lean_dec(x_146);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
lean_dec(x_142);
x_148 = lean_ctor_get(x_145, 1);
lean_inc(x_148);
lean_dec(x_145);
x_149 = l_Lean_Meta_injectionCore___lambda__1___closed__4;
x_150 = lean_unsigned_to_nat(3u);
x_151 = l_Lean_Expr_isAppOfArity(x_16, x_149, x_150);
lean_dec(x_16);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; 
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_18);
lean_dec(x_3);
x_152 = l_Lean_Meta_injectionCore___lambda__1___closed__7;
x_153 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_152, x_4, x_5, x_6, x_7, x_148);
lean_dec(x_7);
lean_dec(x_5);
return x_153;
}
else
{
lean_object* x_154; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_154 = lean_whnf(x_143, x_4, x_5, x_6, x_7, x_148);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_157 = lean_whnf(x_144, x_4, x_5, x_6, x_7, x_156);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
lean_inc(x_1);
x_160 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_st_ref_get(x_7, x_162);
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_164, 0);
lean_inc(x_166);
lean_dec(x_164);
lean_inc(x_166);
x_167 = l_Lean_Expr_isConstructorApp_x3f(x_166, x_155);
lean_dec(x_155);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_166);
lean_dec(x_161);
lean_dec(x_158);
lean_dec(x_18);
lean_dec(x_3);
x_168 = l_Lean_Meta_injectionCore___lambda__1___closed__10;
x_169 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_168, x_4, x_5, x_6, x_7, x_165);
lean_dec(x_7);
lean_dec(x_5);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_167, 0);
lean_inc(x_170);
lean_dec(x_167);
x_171 = l_Lean_Expr_isConstructorApp_x3f(x_166, x_158);
lean_dec(x_158);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; 
lean_dec(x_170);
lean_dec(x_161);
lean_dec(x_18);
lean_dec(x_3);
x_172 = l_Lean_Meta_injectionCore___lambda__1___closed__10;
x_173 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_172, x_4, x_5, x_6, x_7, x_165);
lean_dec(x_7);
lean_dec(x_5);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_171, 0);
lean_inc(x_174);
lean_dec(x_171);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_175 = l_Lean_Meta_mkNoConfusion(x_161, x_18, x_4, x_5, x_6, x_7, x_165);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_ctor_get(x_170, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
lean_dec(x_178);
x_180 = lean_ctor_get(x_174, 0);
lean_inc(x_180);
lean_dec(x_174);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
lean_dec(x_180);
x_182 = lean_name_eq(x_179, x_181);
lean_dec(x_181);
lean_dec(x_179);
if (x_182 == 0)
{
lean_object* x_183; uint8_t x_184; 
lean_dec(x_170);
lean_dec(x_3);
lean_dec(x_2);
x_183 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_176, x_4, x_5, x_6, x_7, x_177);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_184 = !lean_is_exclusive(x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_183, 0);
lean_dec(x_185);
x_186 = lean_box(0);
lean_ctor_set(x_183, 0, x_186);
return x_183;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_183, 1);
lean_inc(x_187);
lean_dec(x_183);
x_188 = lean_box(0);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
else
{
lean_object* x_190; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_176);
x_190 = lean_infer_type(x_176, x_4, x_5, x_6, x_7, x_177);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_193 = lean_whnf(x_191, x_4, x_5, x_6, x_7, x_192);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
if (lean_obj_tag(x_194) == 7)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_2);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec(x_194);
x_197 = l_Lean_Expr_headBeta(x_196);
lean_inc(x_1);
x_198 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_195);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
lean_inc(x_4);
x_201 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_197, x_199, x_4, x_5, x_6, x_7, x_200);
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
lean_inc(x_202);
x_204 = l_Lean_Expr_app___override(x_176, x_202);
x_205 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_204, x_4, x_5, x_6, x_7, x_203);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec(x_205);
x_207 = l_Lean_Expr_mvarId_x21(x_202);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_208 = l_Lean_MVarId_tryClear(x_207, x_3, x_4, x_5, x_6, x_7, x_206);
if (lean_obj_tag(x_208) == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_208, 1);
lean_inc(x_210);
lean_dec(x_208);
lean_inc(x_170);
x_211 = l_Lean_Meta_getCtorNumPropFields(x_170, x_4, x_5, x_6, x_7, x_210);
if (lean_obj_tag(x_211) == 0)
{
uint8_t x_212; 
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_213 = lean_ctor_get(x_211, 0);
x_214 = lean_ctor_get(x_170, 4);
lean_inc(x_214);
lean_dec(x_170);
x_215 = lean_nat_sub(x_214, x_213);
lean_dec(x_213);
lean_dec(x_214);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_209);
lean_ctor_set(x_216, 1, x_215);
lean_ctor_set(x_211, 0, x_216);
return x_211;
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_217 = lean_ctor_get(x_211, 0);
x_218 = lean_ctor_get(x_211, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_211);
x_219 = lean_ctor_get(x_170, 4);
lean_inc(x_219);
lean_dec(x_170);
x_220 = lean_nat_sub(x_219, x_217);
lean_dec(x_217);
lean_dec(x_219);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_209);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_218);
return x_222;
}
}
else
{
uint8_t x_223; 
lean_dec(x_209);
lean_dec(x_170);
x_223 = !lean_is_exclusive(x_211);
if (x_223 == 0)
{
return x_211;
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_211, 0);
x_225 = lean_ctor_get(x_211, 1);
lean_inc(x_225);
lean_inc(x_224);
lean_dec(x_211);
x_226 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
return x_226;
}
}
}
else
{
uint8_t x_227; 
lean_dec(x_170);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_227 = !lean_is_exclusive(x_208);
if (x_227 == 0)
{
return x_208;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_208, 0);
x_229 = lean_ctor_get(x_208, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_208);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
}
else
{
uint8_t x_231; 
lean_dec(x_197);
lean_dec(x_176);
lean_dec(x_170);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_231 = !lean_is_exclusive(x_198);
if (x_231 == 0)
{
return x_198;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_198, 0);
x_233 = lean_ctor_get(x_198, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_198);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_194);
lean_dec(x_176);
lean_dec(x_170);
lean_dec(x_3);
x_235 = lean_ctor_get(x_193, 1);
lean_inc(x_235);
lean_dec(x_193);
x_236 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_237 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_236, x_4, x_5, x_6, x_7, x_235);
lean_dec(x_7);
lean_dec(x_5);
return x_237;
}
}
else
{
uint8_t x_238; 
lean_dec(x_176);
lean_dec(x_170);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_238 = !lean_is_exclusive(x_193);
if (x_238 == 0)
{
return x_193;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_193, 0);
x_240 = lean_ctor_get(x_193, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_193);
x_241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
else
{
uint8_t x_242; 
lean_dec(x_176);
lean_dec(x_170);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_242 = !lean_is_exclusive(x_190);
if (x_242 == 0)
{
return x_190;
}
else
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_190, 0);
x_244 = lean_ctor_get(x_190, 1);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_190);
x_245 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
}
}
else
{
uint8_t x_246; 
lean_dec(x_174);
lean_dec(x_170);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_246 = !lean_is_exclusive(x_175);
if (x_246 == 0)
{
return x_175;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_175, 0);
x_248 = lean_ctor_get(x_175, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_175);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_158);
lean_dec(x_155);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_250 = !lean_is_exclusive(x_160);
if (x_250 == 0)
{
return x_160;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_160, 0);
x_252 = lean_ctor_get(x_160, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_160);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
else
{
uint8_t x_254; 
lean_dec(x_155);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_254 = !lean_is_exclusive(x_157);
if (x_254 == 0)
{
return x_157;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_157, 0);
x_256 = lean_ctor_get(x_157, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_157);
x_257 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
return x_257;
}
}
}
else
{
uint8_t x_258; 
lean_dec(x_144);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_258 = !lean_is_exclusive(x_154);
if (x_258 == 0)
{
return x_154;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_259 = lean_ctor_get(x_154, 0);
x_260 = lean_ctor_get(x_154, 1);
lean_inc(x_260);
lean_inc(x_259);
lean_dec(x_154);
x_261 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_261, 0, x_259);
lean_ctor_set(x_261, 1, x_260);
return x_261;
}
}
}
}
else
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_143);
lean_dec(x_16);
x_262 = lean_ctor_get(x_145, 1);
lean_inc(x_262);
lean_dec(x_145);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_263 = l_Lean_Meta_mkEq(x_142, x_144, x_4, x_5, x_6, x_7, x_262);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_266 = l_Lean_Meta_mkEqOfHEq(x_18, x_4, x_5, x_6, x_7, x_265);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; uint8_t x_271; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = l_Lean_Meta_injectionCore___lambda__1___closed__4;
x_270 = lean_unsigned_to_nat(3u);
x_271 = l_Lean_Expr_isAppOfArity(x_264, x_269, x_270);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; 
lean_dec(x_267);
lean_dec(x_264);
lean_dec(x_3);
x_272 = l_Lean_Meta_injectionCore___lambda__1___closed__7;
x_273 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_272, x_4, x_5, x_6, x_7, x_268);
lean_dec(x_7);
lean_dec(x_5);
return x_273;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_274 = l_Lean_Expr_appFn_x21(x_264);
x_275 = l_Lean_Expr_appArg_x21(x_274);
lean_dec(x_274);
x_276 = l_Lean_Expr_appArg_x21(x_264);
lean_dec(x_264);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_277 = lean_whnf(x_275, x_4, x_5, x_6, x_7, x_268);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_280 = lean_whnf(x_276, x_4, x_5, x_6, x_7, x_279);
if (lean_obj_tag(x_280) == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_280, 1);
lean_inc(x_282);
lean_dec(x_280);
lean_inc(x_1);
x_283 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_282);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
x_286 = lean_st_ref_get(x_7, x_285);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = lean_ctor_get(x_287, 0);
lean_inc(x_289);
lean_dec(x_287);
lean_inc(x_289);
x_290 = l_Lean_Expr_isConstructorApp_x3f(x_289, x_278);
lean_dec(x_278);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; 
lean_dec(x_289);
lean_dec(x_284);
lean_dec(x_281);
lean_dec(x_267);
lean_dec(x_3);
x_291 = l_Lean_Meta_injectionCore___lambda__1___closed__10;
x_292 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_291, x_4, x_5, x_6, x_7, x_288);
lean_dec(x_7);
lean_dec(x_5);
return x_292;
}
else
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_290, 0);
lean_inc(x_293);
lean_dec(x_290);
x_294 = l_Lean_Expr_isConstructorApp_x3f(x_289, x_281);
lean_dec(x_281);
if (lean_obj_tag(x_294) == 0)
{
lean_object* x_295; lean_object* x_296; 
lean_dec(x_293);
lean_dec(x_284);
lean_dec(x_267);
lean_dec(x_3);
x_295 = l_Lean_Meta_injectionCore___lambda__1___closed__10;
x_296 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_295, x_4, x_5, x_6, x_7, x_288);
lean_dec(x_7);
lean_dec(x_5);
return x_296;
}
else
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_294, 0);
lean_inc(x_297);
lean_dec(x_294);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_298 = l_Lean_Meta_mkNoConfusion(x_284, x_267, x_4, x_5, x_6, x_7, x_288);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; uint8_t x_305; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
lean_dec(x_298);
x_301 = lean_ctor_get(x_293, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
lean_dec(x_301);
x_303 = lean_ctor_get(x_297, 0);
lean_inc(x_303);
lean_dec(x_297);
x_304 = lean_ctor_get(x_303, 0);
lean_inc(x_304);
lean_dec(x_303);
x_305 = lean_name_eq(x_302, x_304);
lean_dec(x_304);
lean_dec(x_302);
if (x_305 == 0)
{
lean_object* x_306; uint8_t x_307; 
lean_dec(x_293);
lean_dec(x_3);
lean_dec(x_2);
x_306 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_299, x_4, x_5, x_6, x_7, x_300);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_307 = !lean_is_exclusive(x_306);
if (x_307 == 0)
{
lean_object* x_308; lean_object* x_309; 
x_308 = lean_ctor_get(x_306, 0);
lean_dec(x_308);
x_309 = lean_box(0);
lean_ctor_set(x_306, 0, x_309);
return x_306;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_306, 1);
lean_inc(x_310);
lean_dec(x_306);
x_311 = lean_box(0);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_311);
lean_ctor_set(x_312, 1, x_310);
return x_312;
}
}
else
{
lean_object* x_313; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_299);
x_313 = lean_infer_type(x_299, x_4, x_5, x_6, x_7, x_300);
if (lean_obj_tag(x_313) == 0)
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_313, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_313, 1);
lean_inc(x_315);
lean_dec(x_313);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_316 = lean_whnf(x_314, x_4, x_5, x_6, x_7, x_315);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
if (lean_obj_tag(x_317) == 7)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_2);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_319 = lean_ctor_get(x_317, 1);
lean_inc(x_319);
lean_dec(x_317);
x_320 = l_Lean_Expr_headBeta(x_319);
lean_inc(x_1);
x_321 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_318);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
lean_dec(x_321);
lean_inc(x_4);
x_324 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_320, x_322, x_4, x_5, x_6, x_7, x_323);
x_325 = lean_ctor_get(x_324, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_324, 1);
lean_inc(x_326);
lean_dec(x_324);
lean_inc(x_325);
x_327 = l_Lean_Expr_app___override(x_299, x_325);
x_328 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_327, x_4, x_5, x_6, x_7, x_326);
x_329 = lean_ctor_get(x_328, 1);
lean_inc(x_329);
lean_dec(x_328);
x_330 = l_Lean_Expr_mvarId_x21(x_325);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_331 = l_Lean_MVarId_tryClear(x_330, x_3, x_4, x_5, x_6, x_7, x_329);
if (lean_obj_tag(x_331) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
lean_dec(x_331);
lean_inc(x_293);
x_334 = l_Lean_Meta_getCtorNumPropFields(x_293, x_4, x_5, x_6, x_7, x_333);
if (lean_obj_tag(x_334) == 0)
{
uint8_t x_335; 
x_335 = !lean_is_exclusive(x_334);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_336 = lean_ctor_get(x_334, 0);
x_337 = lean_ctor_get(x_293, 4);
lean_inc(x_337);
lean_dec(x_293);
x_338 = lean_nat_sub(x_337, x_336);
lean_dec(x_336);
lean_dec(x_337);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_332);
lean_ctor_set(x_339, 1, x_338);
lean_ctor_set(x_334, 0, x_339);
return x_334;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_340 = lean_ctor_get(x_334, 0);
x_341 = lean_ctor_get(x_334, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_334);
x_342 = lean_ctor_get(x_293, 4);
lean_inc(x_342);
lean_dec(x_293);
x_343 = lean_nat_sub(x_342, x_340);
lean_dec(x_340);
lean_dec(x_342);
x_344 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_344, 0, x_332);
lean_ctor_set(x_344, 1, x_343);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_341);
return x_345;
}
}
else
{
uint8_t x_346; 
lean_dec(x_332);
lean_dec(x_293);
x_346 = !lean_is_exclusive(x_334);
if (x_346 == 0)
{
return x_334;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_334, 0);
x_348 = lean_ctor_get(x_334, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_334);
x_349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
return x_349;
}
}
}
else
{
uint8_t x_350; 
lean_dec(x_293);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_350 = !lean_is_exclusive(x_331);
if (x_350 == 0)
{
return x_331;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_331, 0);
x_352 = lean_ctor_get(x_331, 1);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_331);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
return x_353;
}
}
}
else
{
uint8_t x_354; 
lean_dec(x_320);
lean_dec(x_299);
lean_dec(x_293);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_354 = !lean_is_exclusive(x_321);
if (x_354 == 0)
{
return x_321;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_321, 0);
x_356 = lean_ctor_get(x_321, 1);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_321);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
return x_357;
}
}
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_dec(x_317);
lean_dec(x_299);
lean_dec(x_293);
lean_dec(x_3);
x_358 = lean_ctor_get(x_316, 1);
lean_inc(x_358);
lean_dec(x_316);
x_359 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_360 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_359, x_4, x_5, x_6, x_7, x_358);
lean_dec(x_7);
lean_dec(x_5);
return x_360;
}
}
else
{
uint8_t x_361; 
lean_dec(x_299);
lean_dec(x_293);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_361 = !lean_is_exclusive(x_316);
if (x_361 == 0)
{
return x_316;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_316, 0);
x_363 = lean_ctor_get(x_316, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_316);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
return x_364;
}
}
}
else
{
uint8_t x_365; 
lean_dec(x_299);
lean_dec(x_293);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_365 = !lean_is_exclusive(x_313);
if (x_365 == 0)
{
return x_313;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_313, 0);
x_367 = lean_ctor_get(x_313, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_313);
x_368 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set(x_368, 1, x_367);
return x_368;
}
}
}
}
else
{
uint8_t x_369; 
lean_dec(x_297);
lean_dec(x_293);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_369 = !lean_is_exclusive(x_298);
if (x_369 == 0)
{
return x_298;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; 
x_370 = lean_ctor_get(x_298, 0);
x_371 = lean_ctor_get(x_298, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_298);
x_372 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
return x_372;
}
}
}
}
}
else
{
uint8_t x_373; 
lean_dec(x_281);
lean_dec(x_278);
lean_dec(x_267);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_373 = !lean_is_exclusive(x_283);
if (x_373 == 0)
{
return x_283;
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; 
x_374 = lean_ctor_get(x_283, 0);
x_375 = lean_ctor_get(x_283, 1);
lean_inc(x_375);
lean_inc(x_374);
lean_dec(x_283);
x_376 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_376, 0, x_374);
lean_ctor_set(x_376, 1, x_375);
return x_376;
}
}
}
else
{
uint8_t x_377; 
lean_dec(x_278);
lean_dec(x_267);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_377 = !lean_is_exclusive(x_280);
if (x_377 == 0)
{
return x_280;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_280, 0);
x_379 = lean_ctor_get(x_280, 1);
lean_inc(x_379);
lean_inc(x_378);
lean_dec(x_280);
x_380 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_380, 0, x_378);
lean_ctor_set(x_380, 1, x_379);
return x_380;
}
}
}
else
{
uint8_t x_381; 
lean_dec(x_276);
lean_dec(x_267);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_381 = !lean_is_exclusive(x_277);
if (x_381 == 0)
{
return x_277;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_277, 0);
x_383 = lean_ctor_get(x_277, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_277);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
}
else
{
uint8_t x_385; 
lean_dec(x_264);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_385 = !lean_is_exclusive(x_266);
if (x_385 == 0)
{
return x_266;
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_386 = lean_ctor_get(x_266, 0);
x_387 = lean_ctor_get(x_266, 1);
lean_inc(x_387);
lean_inc(x_386);
lean_dec(x_266);
x_388 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_388, 0, x_386);
lean_ctor_set(x_388, 1, x_387);
return x_388;
}
}
}
else
{
uint8_t x_389; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_389 = !lean_is_exclusive(x_263);
if (x_389 == 0)
{
return x_263;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_263, 0);
x_391 = lean_ctor_get(x_263, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_263);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
return x_392;
}
}
}
}
else
{
uint8_t x_393; 
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_393 = !lean_is_exclusive(x_145);
if (x_393 == 0)
{
return x_145;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_145, 0);
x_395 = lean_ctor_get(x_145, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_145);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
}
}
else
{
uint8_t x_397; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_397 = !lean_is_exclusive(x_15);
if (x_397 == 0)
{
return x_15;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_15, 0);
x_399 = lean_ctor_get(x_15, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_15);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
}
else
{
uint8_t x_401; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_401 = !lean_is_exclusive(x_11);
if (x_401 == 0)
{
return x_11;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_402 = lean_ctor_get(x_11, 0);
x_403 = lean_ctor_get(x_11, 1);
lean_inc(x_403);
lean_inc(x_402);
lean_dec(x_11);
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set(x_404, 1, x_403);
return x_404;
}
}
}
else
{
uint8_t x_405; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_405 = !lean_is_exclusive(x_9);
if (x_405 == 0)
{
return x_9;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_406 = lean_ctor_get(x_9, 0);
x_407 = lean_ctor_get(x_9, 1);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_9);
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
return x_408;
}
}
}
}
static lean_object* _init_l_Lean_Meta_injectionCore___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_from_bytes("injection", 9);
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
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
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
x_1 = lean_mk_string_from_bytes("injections", 10);
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
x_1 = lean_mk_string_from_bytes("recursion depth exceeded", 24);
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
x_2 = lean_alloc_ctor(0, 1, 0);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_89; 
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
x_89 = l_Lean_Expr_isNatLit(x_33);
lean_dec(x_33);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_36);
x_90 = lean_box(0);
x_39 = x_90;
goto block_88;
}
else
{
uint8_t x_91; 
x_91 = l_Lean_Expr_isNatLit(x_36);
lean_dec(x_36);
if (x_91 == 0)
{
lean_object* x_92; 
x_92 = lean_box(0);
x_39 = x_92;
goto block_88;
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
block_88:
{
lean_object* x_40; lean_object* x_41; lean_object* x_64; 
lean_dec(x_39);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_64 = l_Lean_Meta_injection(x_4, x_15, x_5, x_6, x_7, x_8, x_9, x_37);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
if (lean_obj_tag(x_65) == 0)
{
uint8_t x_66; 
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
x_66 = !lean_is_exclusive(x_64);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_64, 0);
lean_dec(x_67);
x_68 = lean_box(0);
lean_ctor_set(x_64, 0, x_68);
return x_64;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_64, 1);
lean_inc(x_69);
lean_dec(x_64);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_72 = lean_ctor_get(x_64, 1);
lean_inc(x_72);
lean_dec(x_64);
x_73 = lean_ctor_get(x_65, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_65, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_65, 2);
lean_inc(x_75);
lean_dec(x_65);
x_76 = lean_array_to_list(lean_box(0), x_74);
lean_inc(x_16);
x_77 = l_List_appendTR___rarg(x_76, x_16);
lean_inc(x_73);
lean_inc(x_1);
x_78 = lean_alloc_closure((void*)(l_Lean_Meta_injections_go), 10, 5);
lean_closure_set(x_78, 0, x_1);
lean_closure_set(x_78, 1, x_18);
lean_closure_set(x_78, 2, x_77);
lean_closure_set(x_78, 3, x_73);
lean_closure_set(x_78, 4, x_75);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_79 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_73, x_78, x_6, x_7, x_8, x_9, x_72);
if (lean_obj_tag(x_79) == 0)
{
uint8_t x_80; 
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
x_80 = !lean_is_exclusive(x_79);
if (x_80 == 0)
{
return x_79;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_79, 0);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_79);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_dec(x_79);
x_40 = x_84;
x_41 = x_85;
goto block_63;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_18);
x_86 = lean_ctor_get(x_64, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_64, 1);
lean_inc(x_87);
lean_dec(x_64);
x_40 = x_86;
x_41 = x_87;
goto block_63;
}
block_63:
{
uint8_t x_42; 
x_42 = l_Lean_Exception_isRuntime(x_40);
if (x_42 == 0)
{
lean_object* x_43; 
lean_dec(x_40);
lean_dec(x_38);
x_43 = l_Lean_Meta_injections_go(x_1, x_19, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
return x_43;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
return x_43;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_43, 0);
x_50 = lean_ctor_get(x_43, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_43);
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
x_52 = lean_ctor_get_uint8(x_8, sizeof(void*)*11);
if (x_52 == 0)
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
else
{
lean_object* x_54; 
lean_dec(x_40);
lean_dec(x_38);
x_54 = l_Lean_Meta_injections_go(x_1, x_19, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
return x_54;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_54);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_54);
if (x_59 == 0)
{
return x_54;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_54, 0);
x_61 = lean_ctor_get(x_54, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_54);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
}
}
}
else
{
uint8_t x_94; 
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
x_94 = !lean_is_exclusive(x_35);
if (x_94 == 0)
{
return x_35;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_35, 0);
x_96 = lean_ctor_get(x_35, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_35);
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
x_98 = !lean_is_exclusive(x_32);
if (x_98 == 0)
{
return x_32;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_32, 0);
x_100 = lean_ctor_get(x_32, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_32);
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
uint8_t x_102; 
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
x_102 = !lean_is_exclusive(x_23);
if (x_102 == 0)
{
return x_23;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_23, 0);
x_104 = lean_ctor_get(x_23, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_23);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
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
x_106 = !lean_is_exclusive(x_20);
if (x_106 == 0)
{
return x_20;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_20, 0);
x_108 = lean_ctor_get(x_20, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_20);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_110 = l_Lean_Meta_injections_go___closed__2;
x_111 = l_Lean_Meta_injections_go___closed__5;
x_112 = l_Lean_Meta_throwTacticEx___rarg(x_110, x_1, x_111, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
return x_112;
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
x_11 = lean_array_to_list(lean_box(0), x_10);
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
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
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
