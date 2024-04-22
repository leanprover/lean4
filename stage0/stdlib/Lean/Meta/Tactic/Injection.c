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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__2;
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEqHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__10;
lean_object* l___private_Init_GetElem_0__outOfBounds___rarg(lean_object*);
static lean_object* l_Lean_Meta_injectionCore___closed__2;
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_object* l_Lean_Meta_injectionCore___lambda__1___closed__12;
lean_object* lean_array_to_list(lean_object*, lean_object*);
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
x_29 = l___private_Init_GetElem_0__outOfBounds___rarg(x_28);
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
lean_inc(x_16);
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
x_38 = l_Lean_Meta_injectionCore___lambda__1___closed__10;
x_39 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_38, x_4, x_5, x_6, x_7, x_37);
lean_dec(x_7);
lean_dec(x_5);
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
x_42 = l_Lean_Meta_injectionCore___lambda__1___closed__10;
x_43 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_42, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_7);
lean_dec(x_5);
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
uint8_t x_54; lean_object* x_55; lean_object* x_56; 
x_54 = 1;
lean_ctor_set_uint8(x_44, 9, x_54);
x_55 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_55, 0, x_44);
lean_ctor_set(x_55, 1, x_48);
lean_ctor_set(x_55, 2, x_49);
lean_ctor_set(x_55, 3, x_50);
lean_ctor_set(x_55, 4, x_51);
lean_ctor_set(x_55, 5, x_52);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_56 = l_Lean_Meta_mkNoConfusion(x_31, x_18, x_55, x_5, x_6, x_7, x_45);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_46, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_ctor_get(x_47, 0);
lean_inc(x_61);
lean_dec(x_47);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec(x_61);
x_63 = lean_name_eq(x_60, x_62);
lean_dec(x_62);
lean_dec(x_60);
if (x_63 == 0)
{
lean_object* x_64; uint8_t x_65; 
lean_dec(x_46);
lean_dec(x_3);
lean_dec(x_2);
x_64 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_57, x_4, x_5, x_6, x_7, x_58);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_64, 0);
lean_dec(x_66);
x_67 = lean_box(0);
lean_ctor_set(x_64, 0, x_67);
return x_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
lean_object* x_71; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_57);
x_71 = lean_infer_type(x_57, x_4, x_5, x_6, x_7, x_58);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_74 = l_Lean_Meta_whnfD(x_72, x_4, x_5, x_6, x_7, x_73);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_obj_tag(x_75) == 7)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_2);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = l_Lean_Expr_headBeta(x_77);
lean_inc(x_1);
x_79 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_76);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_4);
x_82 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_78, x_80, x_4, x_5, x_6, x_7, x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_83);
x_85 = l_Lean_Expr_app___override(x_57, x_83);
x_86 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_85, x_4, x_5, x_6, x_7, x_84);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_Lean_Expr_mvarId_x21(x_83);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_89 = l_Lean_MVarId_tryClear(x_88, x_3, x_4, x_5, x_6, x_7, x_87);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
lean_inc(x_46);
x_92 = l_Lean_Meta_getCtorNumPropFields(x_46, x_4, x_5, x_6, x_7, x_91);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_ctor_get(x_46, 4);
lean_inc(x_95);
lean_dec(x_46);
x_96 = lean_nat_sub(x_95, x_94);
lean_dec(x_94);
lean_dec(x_95);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_90);
lean_ctor_set(x_97, 1, x_96);
lean_ctor_set(x_92, 0, x_97);
return x_92;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_ctor_get(x_92, 0);
x_99 = lean_ctor_get(x_92, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_92);
x_100 = lean_ctor_get(x_46, 4);
lean_inc(x_100);
lean_dec(x_46);
x_101 = lean_nat_sub(x_100, x_98);
lean_dec(x_98);
lean_dec(x_100);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_90);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_99);
return x_103;
}
}
else
{
uint8_t x_104; 
lean_dec(x_90);
lean_dec(x_46);
x_104 = !lean_is_exclusive(x_92);
if (x_104 == 0)
{
return x_92;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_92, 0);
x_106 = lean_ctor_get(x_92, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_92);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
else
{
uint8_t x_108; 
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_108 = !lean_is_exclusive(x_89);
if (x_108 == 0)
{
return x_89;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_89, 0);
x_110 = lean_ctor_get(x_89, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_89);
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
lean_dec(x_78);
lean_dec(x_57);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_79);
if (x_112 == 0)
{
return x_79;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_79, 0);
x_114 = lean_ctor_get(x_79, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_79);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_dec(x_75);
lean_dec(x_57);
lean_dec(x_46);
lean_dec(x_3);
x_116 = lean_ctor_get(x_74, 1);
lean_inc(x_116);
lean_dec(x_74);
x_117 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_118 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_117, x_4, x_5, x_6, x_7, x_116);
lean_dec(x_7);
lean_dec(x_5);
return x_118;
}
}
else
{
uint8_t x_119; 
lean_dec(x_57);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_74);
if (x_119 == 0)
{
return x_74;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_74, 0);
x_121 = lean_ctor_get(x_74, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_74);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_57);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_71);
if (x_123 == 0)
{
return x_71;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_71, 0);
x_125 = lean_ctor_get(x_71, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_71);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_127 = !lean_is_exclusive(x_56);
if (x_127 == 0)
{
return x_56;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_56, 0);
x_129 = lean_ctor_get(x_56, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_56);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
uint8_t x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; uint8_t x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_131 = lean_ctor_get_uint8(x_44, 0);
x_132 = lean_ctor_get_uint8(x_44, 1);
x_133 = lean_ctor_get_uint8(x_44, 2);
x_134 = lean_ctor_get_uint8(x_44, 3);
x_135 = lean_ctor_get_uint8(x_44, 4);
x_136 = lean_ctor_get_uint8(x_44, 5);
x_137 = lean_ctor_get_uint8(x_44, 6);
x_138 = lean_ctor_get_uint8(x_44, 7);
x_139 = lean_ctor_get_uint8(x_44, 8);
x_140 = lean_ctor_get_uint8(x_44, 10);
x_141 = lean_ctor_get_uint8(x_44, 11);
lean_dec(x_44);
x_142 = 1;
x_143 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_143, 0, x_131);
lean_ctor_set_uint8(x_143, 1, x_132);
lean_ctor_set_uint8(x_143, 2, x_133);
lean_ctor_set_uint8(x_143, 3, x_134);
lean_ctor_set_uint8(x_143, 4, x_135);
lean_ctor_set_uint8(x_143, 5, x_136);
lean_ctor_set_uint8(x_143, 6, x_137);
lean_ctor_set_uint8(x_143, 7, x_138);
lean_ctor_set_uint8(x_143, 8, x_139);
lean_ctor_set_uint8(x_143, 9, x_142);
lean_ctor_set_uint8(x_143, 10, x_140);
lean_ctor_set_uint8(x_143, 11, x_141);
x_144 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_144, 1, x_48);
lean_ctor_set(x_144, 2, x_49);
lean_ctor_set(x_144, 3, x_50);
lean_ctor_set(x_144, 4, x_51);
lean_ctor_set(x_144, 5, x_52);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_145 = l_Lean_Meta_mkNoConfusion(x_31, x_18, x_144, x_5, x_6, x_7, x_45);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
lean_dec(x_145);
x_148 = lean_ctor_get(x_46, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
lean_dec(x_148);
x_150 = lean_ctor_get(x_47, 0);
lean_inc(x_150);
lean_dec(x_47);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
lean_dec(x_150);
x_152 = lean_name_eq(x_149, x_151);
lean_dec(x_151);
lean_dec(x_149);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_46);
lean_dec(x_3);
lean_dec(x_2);
x_153 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_146, x_4, x_5, x_6, x_7, x_147);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
x_156 = lean_box(0);
if (lean_is_scalar(x_155)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_155;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_154);
return x_157;
}
else
{
lean_object* x_158; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_146);
x_158 = lean_infer_type(x_146, x_4, x_5, x_6, x_7, x_147);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_161 = l_Lean_Meta_whnfD(x_159, x_4, x_5, x_6, x_7, x_160);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
if (lean_obj_tag(x_162) == 7)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_2);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = l_Lean_Expr_headBeta(x_164);
lean_inc(x_1);
x_166 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_163);
if (lean_obj_tag(x_166) == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec(x_166);
lean_inc(x_4);
x_169 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_165, x_167, x_4, x_5, x_6, x_7, x_168);
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
lean_inc(x_170);
x_172 = l_Lean_Expr_app___override(x_146, x_170);
x_173 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_172, x_4, x_5, x_6, x_7, x_171);
x_174 = lean_ctor_get(x_173, 1);
lean_inc(x_174);
lean_dec(x_173);
x_175 = l_Lean_Expr_mvarId_x21(x_170);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_176 = l_Lean_MVarId_tryClear(x_175, x_3, x_4, x_5, x_6, x_7, x_174);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec(x_176);
lean_inc(x_46);
x_179 = l_Lean_Meta_getCtorNumPropFields(x_46, x_4, x_5, x_6, x_7, x_178);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_182 = x_179;
} else {
 lean_dec_ref(x_179);
 x_182 = lean_box(0);
}
x_183 = lean_ctor_get(x_46, 4);
lean_inc(x_183);
lean_dec(x_46);
x_184 = lean_nat_sub(x_183, x_180);
lean_dec(x_180);
lean_dec(x_183);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_177);
lean_ctor_set(x_185, 1, x_184);
if (lean_is_scalar(x_182)) {
 x_186 = lean_alloc_ctor(0, 2, 0);
} else {
 x_186 = x_182;
}
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_181);
return x_186;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_177);
lean_dec(x_46);
x_187 = lean_ctor_get(x_179, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_179, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_189 = x_179;
} else {
 lean_dec_ref(x_179);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_191 = lean_ctor_get(x_176, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_176, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_193 = x_176;
} else {
 lean_dec_ref(x_176);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_dec(x_165);
lean_dec(x_146);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_195 = lean_ctor_get(x_166, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_166, 1);
lean_inc(x_196);
if (lean_is_exclusive(x_166)) {
 lean_ctor_release(x_166, 0);
 lean_ctor_release(x_166, 1);
 x_197 = x_166;
} else {
 lean_dec_ref(x_166);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(1, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_162);
lean_dec(x_146);
lean_dec(x_46);
lean_dec(x_3);
x_199 = lean_ctor_get(x_161, 1);
lean_inc(x_199);
lean_dec(x_161);
x_200 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_201 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_200, x_4, x_5, x_6, x_7, x_199);
lean_dec(x_7);
lean_dec(x_5);
return x_201;
}
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_146);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_202 = lean_ctor_get(x_161, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_161, 1);
lean_inc(x_203);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_204 = x_161;
} else {
 lean_dec_ref(x_161);
 x_204 = lean_box(0);
}
if (lean_is_scalar(x_204)) {
 x_205 = lean_alloc_ctor(1, 2, 0);
} else {
 x_205 = x_204;
}
lean_ctor_set(x_205, 0, x_202);
lean_ctor_set(x_205, 1, x_203);
return x_205;
}
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_146);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_206 = lean_ctor_get(x_158, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_158, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_158)) {
 lean_ctor_release(x_158, 0);
 lean_ctor_release(x_158, 1);
 x_208 = x_158;
} else {
 lean_dec_ref(x_158);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_210 = lean_ctor_get(x_145, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_145, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_212 = x_145;
} else {
 lean_dec_ref(x_145);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
}
}
}
else
{
uint8_t x_214; 
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
x_214 = !lean_is_exclusive(x_36);
if (x_214 == 0)
{
return x_36;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_36, 0);
x_216 = lean_ctor_get(x_36, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_36);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
else
{
uint8_t x_218; 
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
x_218 = !lean_is_exclusive(x_33);
if (x_218 == 0)
{
return x_33;
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_33, 0);
x_220 = lean_ctor_get(x_33, 1);
lean_inc(x_220);
lean_inc(x_219);
lean_dec(x_33);
x_221 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
}
}
else
{
uint8_t x_222; 
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
x_222 = !lean_is_exclusive(x_30);
if (x_222 == 0)
{
return x_30;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_30, 0);
x_224 = lean_ctor_get(x_30, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_30);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_inc(x_16);
x_226 = l_Lean_Expr_appFn_x21(x_16);
lean_inc(x_226);
x_227 = l_Lean_Expr_appFn_x21(x_226);
lean_inc(x_227);
x_228 = l_Lean_Expr_appFn_x21(x_227);
x_229 = l_Lean_Expr_appArg_x21(x_228);
lean_dec(x_228);
x_230 = l_Lean_Expr_appArg_x21(x_227);
lean_dec(x_227);
x_231 = l_Lean_Expr_appArg_x21(x_226);
lean_dec(x_226);
x_232 = l_Lean_Expr_appArg_x21(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_231);
x_233 = l_Lean_Meta_isExprDefEq(x_229, x_231, x_4, x_5, x_6, x_7, x_17);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; uint8_t x_235; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_unbox(x_234);
lean_dec(x_234);
if (x_235 == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; 
lean_dec(x_230);
x_236 = lean_ctor_get(x_233, 1);
lean_inc(x_236);
lean_dec(x_233);
x_237 = l_Lean_Meta_injectionCore___lambda__1___closed__4;
x_238 = lean_unsigned_to_nat(3u);
x_239 = l_Lean_Expr_isAppOfArity(x_16, x_237, x_238);
lean_dec(x_16);
if (x_239 == 0)
{
lean_object* x_240; lean_object* x_241; 
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_18);
lean_dec(x_3);
x_240 = l_Lean_Meta_injectionCore___lambda__1___closed__7;
x_241 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_240, x_4, x_5, x_6, x_7, x_236);
lean_dec(x_7);
lean_dec(x_5);
return x_241;
}
else
{
lean_object* x_242; 
lean_inc(x_1);
x_242 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_236);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
lean_dec(x_242);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_245 = l_Lean_Meta_isConstructorApp_x27_x3f(x_231, x_4, x_5, x_6, x_7, x_244);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_248 = l_Lean_Meta_isConstructorApp_x27_x3f(x_232, x_4, x_5, x_6, x_7, x_247);
if (lean_obj_tag(x_248) == 0)
{
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_243);
lean_dec(x_18);
lean_dec(x_3);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
x_250 = l_Lean_Meta_injectionCore___lambda__1___closed__10;
x_251 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_250, x_4, x_5, x_6, x_7, x_249);
lean_dec(x_7);
lean_dec(x_5);
return x_251;
}
else
{
lean_object* x_252; 
x_252 = lean_ctor_get(x_248, 0);
lean_inc(x_252);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_246);
lean_dec(x_243);
lean_dec(x_18);
lean_dec(x_3);
x_253 = lean_ctor_get(x_248, 1);
lean_inc(x_253);
lean_dec(x_248);
x_254 = l_Lean_Meta_injectionCore___lambda__1___closed__10;
x_255 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_254, x_4, x_5, x_6, x_7, x_253);
lean_dec(x_7);
lean_dec(x_5);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_256 = lean_ctor_get(x_4, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_248, 1);
lean_inc(x_257);
lean_dec(x_248);
x_258 = lean_ctor_get(x_246, 0);
lean_inc(x_258);
lean_dec(x_246);
x_259 = lean_ctor_get(x_252, 0);
lean_inc(x_259);
lean_dec(x_252);
x_260 = lean_ctor_get(x_4, 1);
lean_inc(x_260);
x_261 = lean_ctor_get(x_4, 2);
lean_inc(x_261);
x_262 = lean_ctor_get(x_4, 3);
lean_inc(x_262);
x_263 = lean_ctor_get(x_4, 4);
lean_inc(x_263);
x_264 = lean_ctor_get(x_4, 5);
lean_inc(x_264);
x_265 = !lean_is_exclusive(x_256);
if (x_265 == 0)
{
uint8_t x_266; lean_object* x_267; lean_object* x_268; 
x_266 = 1;
lean_ctor_set_uint8(x_256, 9, x_266);
x_267 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_267, 0, x_256);
lean_ctor_set(x_267, 1, x_260);
lean_ctor_set(x_267, 2, x_261);
lean_ctor_set(x_267, 3, x_262);
lean_ctor_set(x_267, 4, x_263);
lean_ctor_set(x_267, 5, x_264);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_268 = l_Lean_Meta_mkNoConfusion(x_243, x_18, x_267, x_5, x_6, x_7, x_257);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = lean_ctor_get(x_258, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
lean_dec(x_271);
x_273 = lean_ctor_get(x_259, 0);
lean_inc(x_273);
lean_dec(x_259);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
lean_dec(x_273);
x_275 = lean_name_eq(x_272, x_274);
lean_dec(x_274);
lean_dec(x_272);
if (x_275 == 0)
{
lean_object* x_276; uint8_t x_277; 
lean_dec(x_258);
lean_dec(x_3);
lean_dec(x_2);
x_276 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_269, x_4, x_5, x_6, x_7, x_270);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_277 = !lean_is_exclusive(x_276);
if (x_277 == 0)
{
lean_object* x_278; lean_object* x_279; 
x_278 = lean_ctor_get(x_276, 0);
lean_dec(x_278);
x_279 = lean_box(0);
lean_ctor_set(x_276, 0, x_279);
return x_276;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_276, 1);
lean_inc(x_280);
lean_dec(x_276);
x_281 = lean_box(0);
x_282 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_282, 0, x_281);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
else
{
lean_object* x_283; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_269);
x_283 = lean_infer_type(x_269, x_4, x_5, x_6, x_7, x_270);
if (lean_obj_tag(x_283) == 0)
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_286 = l_Lean_Meta_whnfD(x_284, x_4, x_5, x_6, x_7, x_285);
if (lean_obj_tag(x_286) == 0)
{
lean_object* x_287; 
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
if (lean_obj_tag(x_287) == 7)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; 
lean_dec(x_2);
x_288 = lean_ctor_get(x_286, 1);
lean_inc(x_288);
lean_dec(x_286);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
lean_dec(x_287);
x_290 = l_Lean_Expr_headBeta(x_289);
lean_inc(x_1);
x_291 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_288);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
lean_inc(x_4);
x_294 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_290, x_292, x_4, x_5, x_6, x_7, x_293);
x_295 = lean_ctor_get(x_294, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_294, 1);
lean_inc(x_296);
lean_dec(x_294);
lean_inc(x_295);
x_297 = l_Lean_Expr_app___override(x_269, x_295);
x_298 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_297, x_4, x_5, x_6, x_7, x_296);
x_299 = lean_ctor_get(x_298, 1);
lean_inc(x_299);
lean_dec(x_298);
x_300 = l_Lean_Expr_mvarId_x21(x_295);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_301 = l_Lean_MVarId_tryClear(x_300, x_3, x_4, x_5, x_6, x_7, x_299);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_301, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_301, 1);
lean_inc(x_303);
lean_dec(x_301);
lean_inc(x_258);
x_304 = l_Lean_Meta_getCtorNumPropFields(x_258, x_4, x_5, x_6, x_7, x_303);
if (lean_obj_tag(x_304) == 0)
{
uint8_t x_305; 
x_305 = !lean_is_exclusive(x_304);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_306 = lean_ctor_get(x_304, 0);
x_307 = lean_ctor_get(x_258, 4);
lean_inc(x_307);
lean_dec(x_258);
x_308 = lean_nat_sub(x_307, x_306);
lean_dec(x_306);
lean_dec(x_307);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_302);
lean_ctor_set(x_309, 1, x_308);
lean_ctor_set(x_304, 0, x_309);
return x_304;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_310 = lean_ctor_get(x_304, 0);
x_311 = lean_ctor_get(x_304, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_304);
x_312 = lean_ctor_get(x_258, 4);
lean_inc(x_312);
lean_dec(x_258);
x_313 = lean_nat_sub(x_312, x_310);
lean_dec(x_310);
lean_dec(x_312);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_302);
lean_ctor_set(x_314, 1, x_313);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_311);
return x_315;
}
}
else
{
uint8_t x_316; 
lean_dec(x_302);
lean_dec(x_258);
x_316 = !lean_is_exclusive(x_304);
if (x_316 == 0)
{
return x_304;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_304, 0);
x_318 = lean_ctor_get(x_304, 1);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_304);
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
return x_319;
}
}
}
else
{
uint8_t x_320; 
lean_dec(x_258);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_320 = !lean_is_exclusive(x_301);
if (x_320 == 0)
{
return x_301;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_301, 0);
x_322 = lean_ctor_get(x_301, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_301);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
return x_323;
}
}
}
else
{
uint8_t x_324; 
lean_dec(x_290);
lean_dec(x_269);
lean_dec(x_258);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_324 = !lean_is_exclusive(x_291);
if (x_324 == 0)
{
return x_291;
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
x_325 = lean_ctor_get(x_291, 0);
x_326 = lean_ctor_get(x_291, 1);
lean_inc(x_326);
lean_inc(x_325);
lean_dec(x_291);
x_327 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_327, 0, x_325);
lean_ctor_set(x_327, 1, x_326);
return x_327;
}
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_287);
lean_dec(x_269);
lean_dec(x_258);
lean_dec(x_3);
x_328 = lean_ctor_get(x_286, 1);
lean_inc(x_328);
lean_dec(x_286);
x_329 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_330 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_329, x_4, x_5, x_6, x_7, x_328);
lean_dec(x_7);
lean_dec(x_5);
return x_330;
}
}
else
{
uint8_t x_331; 
lean_dec(x_269);
lean_dec(x_258);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_331 = !lean_is_exclusive(x_286);
if (x_331 == 0)
{
return x_286;
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_286, 0);
x_333 = lean_ctor_get(x_286, 1);
lean_inc(x_333);
lean_inc(x_332);
lean_dec(x_286);
x_334 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_334, 0, x_332);
lean_ctor_set(x_334, 1, x_333);
return x_334;
}
}
}
else
{
uint8_t x_335; 
lean_dec(x_269);
lean_dec(x_258);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_335 = !lean_is_exclusive(x_283);
if (x_335 == 0)
{
return x_283;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_283, 0);
x_337 = lean_ctor_get(x_283, 1);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_283);
x_338 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_338, 0, x_336);
lean_ctor_set(x_338, 1, x_337);
return x_338;
}
}
}
}
else
{
uint8_t x_339; 
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_339 = !lean_is_exclusive(x_268);
if (x_339 == 0)
{
return x_268;
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_340 = lean_ctor_get(x_268, 0);
x_341 = lean_ctor_get(x_268, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_268);
x_342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_342, 0, x_340);
lean_ctor_set(x_342, 1, x_341);
return x_342;
}
}
}
else
{
uint8_t x_343; uint8_t x_344; uint8_t x_345; uint8_t x_346; uint8_t x_347; uint8_t x_348; uint8_t x_349; uint8_t x_350; uint8_t x_351; uint8_t x_352; uint8_t x_353; uint8_t x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_343 = lean_ctor_get_uint8(x_256, 0);
x_344 = lean_ctor_get_uint8(x_256, 1);
x_345 = lean_ctor_get_uint8(x_256, 2);
x_346 = lean_ctor_get_uint8(x_256, 3);
x_347 = lean_ctor_get_uint8(x_256, 4);
x_348 = lean_ctor_get_uint8(x_256, 5);
x_349 = lean_ctor_get_uint8(x_256, 6);
x_350 = lean_ctor_get_uint8(x_256, 7);
x_351 = lean_ctor_get_uint8(x_256, 8);
x_352 = lean_ctor_get_uint8(x_256, 10);
x_353 = lean_ctor_get_uint8(x_256, 11);
lean_dec(x_256);
x_354 = 1;
x_355 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_355, 0, x_343);
lean_ctor_set_uint8(x_355, 1, x_344);
lean_ctor_set_uint8(x_355, 2, x_345);
lean_ctor_set_uint8(x_355, 3, x_346);
lean_ctor_set_uint8(x_355, 4, x_347);
lean_ctor_set_uint8(x_355, 5, x_348);
lean_ctor_set_uint8(x_355, 6, x_349);
lean_ctor_set_uint8(x_355, 7, x_350);
lean_ctor_set_uint8(x_355, 8, x_351);
lean_ctor_set_uint8(x_355, 9, x_354);
lean_ctor_set_uint8(x_355, 10, x_352);
lean_ctor_set_uint8(x_355, 11, x_353);
x_356 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_260);
lean_ctor_set(x_356, 2, x_261);
lean_ctor_set(x_356, 3, x_262);
lean_ctor_set(x_356, 4, x_263);
lean_ctor_set(x_356, 5, x_264);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_357 = l_Lean_Meta_mkNoConfusion(x_243, x_18, x_356, x_5, x_6, x_7, x_257);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
x_360 = lean_ctor_get(x_258, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
lean_dec(x_360);
x_362 = lean_ctor_get(x_259, 0);
lean_inc(x_362);
lean_dec(x_259);
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
lean_dec(x_362);
x_364 = lean_name_eq(x_361, x_363);
lean_dec(x_363);
lean_dec(x_361);
if (x_364 == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_258);
lean_dec(x_3);
lean_dec(x_2);
x_365 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_358, x_4, x_5, x_6, x_7, x_359);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_366 = lean_ctor_get(x_365, 1);
lean_inc(x_366);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_367 = x_365;
} else {
 lean_dec_ref(x_365);
 x_367 = lean_box(0);
}
x_368 = lean_box(0);
if (lean_is_scalar(x_367)) {
 x_369 = lean_alloc_ctor(0, 2, 0);
} else {
 x_369 = x_367;
}
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_366);
return x_369;
}
else
{
lean_object* x_370; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_358);
x_370 = lean_infer_type(x_358, x_4, x_5, x_6, x_7, x_359);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_373 = l_Lean_Meta_whnfD(x_371, x_4, x_5, x_6, x_7, x_372);
if (lean_obj_tag(x_373) == 0)
{
lean_object* x_374; 
x_374 = lean_ctor_get(x_373, 0);
lean_inc(x_374);
if (lean_obj_tag(x_374) == 7)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_2);
x_375 = lean_ctor_get(x_373, 1);
lean_inc(x_375);
lean_dec(x_373);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec(x_374);
x_377 = l_Lean_Expr_headBeta(x_376);
lean_inc(x_1);
x_378 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_375);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
lean_inc(x_4);
x_381 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_377, x_379, x_4, x_5, x_6, x_7, x_380);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
lean_inc(x_382);
x_384 = l_Lean_Expr_app___override(x_358, x_382);
x_385 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_384, x_4, x_5, x_6, x_7, x_383);
x_386 = lean_ctor_get(x_385, 1);
lean_inc(x_386);
lean_dec(x_385);
x_387 = l_Lean_Expr_mvarId_x21(x_382);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_388 = l_Lean_MVarId_tryClear(x_387, x_3, x_4, x_5, x_6, x_7, x_386);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_389 = lean_ctor_get(x_388, 0);
lean_inc(x_389);
x_390 = lean_ctor_get(x_388, 1);
lean_inc(x_390);
lean_dec(x_388);
lean_inc(x_258);
x_391 = l_Lean_Meta_getCtorNumPropFields(x_258, x_4, x_5, x_6, x_7, x_390);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_394 = x_391;
} else {
 lean_dec_ref(x_391);
 x_394 = lean_box(0);
}
x_395 = lean_ctor_get(x_258, 4);
lean_inc(x_395);
lean_dec(x_258);
x_396 = lean_nat_sub(x_395, x_392);
lean_dec(x_392);
lean_dec(x_395);
x_397 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_397, 0, x_389);
lean_ctor_set(x_397, 1, x_396);
if (lean_is_scalar(x_394)) {
 x_398 = lean_alloc_ctor(0, 2, 0);
} else {
 x_398 = x_394;
}
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_393);
return x_398;
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_389);
lean_dec(x_258);
x_399 = lean_ctor_get(x_391, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_391, 1);
lean_inc(x_400);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_401 = x_391;
} else {
 lean_dec_ref(x_391);
 x_401 = lean_box(0);
}
if (lean_is_scalar(x_401)) {
 x_402 = lean_alloc_ctor(1, 2, 0);
} else {
 x_402 = x_401;
}
lean_ctor_set(x_402, 0, x_399);
lean_ctor_set(x_402, 1, x_400);
return x_402;
}
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_258);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_403 = lean_ctor_get(x_388, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_388, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_388)) {
 lean_ctor_release(x_388, 0);
 lean_ctor_release(x_388, 1);
 x_405 = x_388;
} else {
 lean_dec_ref(x_388);
 x_405 = lean_box(0);
}
if (lean_is_scalar(x_405)) {
 x_406 = lean_alloc_ctor(1, 2, 0);
} else {
 x_406 = x_405;
}
lean_ctor_set(x_406, 0, x_403);
lean_ctor_set(x_406, 1, x_404);
return x_406;
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_377);
lean_dec(x_358);
lean_dec(x_258);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_407 = lean_ctor_get(x_378, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_378, 1);
lean_inc(x_408);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_409 = x_378;
} else {
 lean_dec_ref(x_378);
 x_409 = lean_box(0);
}
if (lean_is_scalar(x_409)) {
 x_410 = lean_alloc_ctor(1, 2, 0);
} else {
 x_410 = x_409;
}
lean_ctor_set(x_410, 0, x_407);
lean_ctor_set(x_410, 1, x_408);
return x_410;
}
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_dec(x_374);
lean_dec(x_358);
lean_dec(x_258);
lean_dec(x_3);
x_411 = lean_ctor_get(x_373, 1);
lean_inc(x_411);
lean_dec(x_373);
x_412 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_413 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_412, x_4, x_5, x_6, x_7, x_411);
lean_dec(x_7);
lean_dec(x_5);
return x_413;
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_358);
lean_dec(x_258);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_414 = lean_ctor_get(x_373, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_373, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_416 = x_373;
} else {
 lean_dec_ref(x_373);
 x_416 = lean_box(0);
}
if (lean_is_scalar(x_416)) {
 x_417 = lean_alloc_ctor(1, 2, 0);
} else {
 x_417 = x_416;
}
lean_ctor_set(x_417, 0, x_414);
lean_ctor_set(x_417, 1, x_415);
return x_417;
}
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_358);
lean_dec(x_258);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_418 = lean_ctor_get(x_370, 0);
lean_inc(x_418);
x_419 = lean_ctor_get(x_370, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_420 = x_370;
} else {
 lean_dec_ref(x_370);
 x_420 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_421 = lean_alloc_ctor(1, 2, 0);
} else {
 x_421 = x_420;
}
lean_ctor_set(x_421, 0, x_418);
lean_ctor_set(x_421, 1, x_419);
return x_421;
}
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_259);
lean_dec(x_258);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_422 = lean_ctor_get(x_357, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_357, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 lean_ctor_release(x_357, 1);
 x_424 = x_357;
} else {
 lean_dec_ref(x_357);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 2, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_422);
lean_ctor_set(x_425, 1, x_423);
return x_425;
}
}
}
}
}
else
{
uint8_t x_426; 
lean_dec(x_246);
lean_dec(x_243);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_426 = !lean_is_exclusive(x_248);
if (x_426 == 0)
{
return x_248;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_248, 0);
x_428 = lean_ctor_get(x_248, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_248);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
}
else
{
uint8_t x_430; 
lean_dec(x_243);
lean_dec(x_232);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_430 = !lean_is_exclusive(x_245);
if (x_430 == 0)
{
return x_245;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_245, 0);
x_432 = lean_ctor_get(x_245, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_245);
x_433 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_433, 0, x_431);
lean_ctor_set(x_433, 1, x_432);
return x_433;
}
}
}
else
{
uint8_t x_434; 
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_434 = !lean_is_exclusive(x_242);
if (x_434 == 0)
{
return x_242;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_242, 0);
x_436 = lean_ctor_get(x_242, 1);
lean_inc(x_436);
lean_inc(x_435);
lean_dec(x_242);
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
}
}
}
else
{
lean_object* x_438; lean_object* x_439; 
lean_dec(x_231);
lean_dec(x_16);
x_438 = lean_ctor_get(x_233, 1);
lean_inc(x_438);
lean_dec(x_233);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_439 = l_Lean_Meta_mkEq(x_230, x_232, x_4, x_5, x_6, x_7, x_438);
if (lean_obj_tag(x_439) == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_439, 0);
lean_inc(x_440);
x_441 = lean_ctor_get(x_439, 1);
lean_inc(x_441);
lean_dec(x_439);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_442 = l_Lean_Meta_mkEqOfHEq(x_18, x_4, x_5, x_6, x_7, x_441);
if (lean_obj_tag(x_442) == 0)
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; 
x_443 = lean_ctor_get(x_442, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_442, 1);
lean_inc(x_444);
lean_dec(x_442);
x_445 = l_Lean_Meta_injectionCore___lambda__1___closed__4;
x_446 = lean_unsigned_to_nat(3u);
x_447 = l_Lean_Expr_isAppOfArity(x_440, x_445, x_446);
if (x_447 == 0)
{
lean_object* x_448; lean_object* x_449; 
lean_dec(x_443);
lean_dec(x_440);
lean_dec(x_3);
x_448 = l_Lean_Meta_injectionCore___lambda__1___closed__7;
x_449 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_448, x_4, x_5, x_6, x_7, x_444);
lean_dec(x_7);
lean_dec(x_5);
return x_449;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
lean_inc(x_440);
x_450 = l_Lean_Expr_appFn_x21(x_440);
x_451 = l_Lean_Expr_appArg_x21(x_450);
lean_dec(x_450);
x_452 = l_Lean_Expr_appArg_x21(x_440);
lean_dec(x_440);
lean_inc(x_1);
x_453 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_444);
if (lean_obj_tag(x_453) == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
lean_dec(x_453);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_456 = l_Lean_Meta_isConstructorApp_x27_x3f(x_451, x_4, x_5, x_6, x_7, x_455);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
lean_dec(x_456);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_459 = l_Lean_Meta_isConstructorApp_x27_x3f(x_452, x_4, x_5, x_6, x_7, x_458);
if (lean_obj_tag(x_459) == 0)
{
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
lean_dec(x_454);
lean_dec(x_443);
lean_dec(x_3);
x_460 = lean_ctor_get(x_459, 1);
lean_inc(x_460);
lean_dec(x_459);
x_461 = l_Lean_Meta_injectionCore___lambda__1___closed__10;
x_462 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_461, x_4, x_5, x_6, x_7, x_460);
lean_dec(x_7);
lean_dec(x_5);
return x_462;
}
else
{
lean_object* x_463; 
x_463 = lean_ctor_get(x_459, 0);
lean_inc(x_463);
if (lean_obj_tag(x_463) == 0)
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
lean_dec(x_457);
lean_dec(x_454);
lean_dec(x_443);
lean_dec(x_3);
x_464 = lean_ctor_get(x_459, 1);
lean_inc(x_464);
lean_dec(x_459);
x_465 = l_Lean_Meta_injectionCore___lambda__1___closed__10;
x_466 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_465, x_4, x_5, x_6, x_7, x_464);
lean_dec(x_7);
lean_dec(x_5);
return x_466;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; uint8_t x_476; 
x_467 = lean_ctor_get(x_4, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_459, 1);
lean_inc(x_468);
lean_dec(x_459);
x_469 = lean_ctor_get(x_457, 0);
lean_inc(x_469);
lean_dec(x_457);
x_470 = lean_ctor_get(x_463, 0);
lean_inc(x_470);
lean_dec(x_463);
x_471 = lean_ctor_get(x_4, 1);
lean_inc(x_471);
x_472 = lean_ctor_get(x_4, 2);
lean_inc(x_472);
x_473 = lean_ctor_get(x_4, 3);
lean_inc(x_473);
x_474 = lean_ctor_get(x_4, 4);
lean_inc(x_474);
x_475 = lean_ctor_get(x_4, 5);
lean_inc(x_475);
x_476 = !lean_is_exclusive(x_467);
if (x_476 == 0)
{
uint8_t x_477; lean_object* x_478; lean_object* x_479; 
x_477 = 1;
lean_ctor_set_uint8(x_467, 9, x_477);
x_478 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_478, 0, x_467);
lean_ctor_set(x_478, 1, x_471);
lean_ctor_set(x_478, 2, x_472);
lean_ctor_set(x_478, 3, x_473);
lean_ctor_set(x_478, 4, x_474);
lean_ctor_set(x_478, 5, x_475);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_479 = l_Lean_Meta_mkNoConfusion(x_454, x_443, x_478, x_5, x_6, x_7, x_468);
if (lean_obj_tag(x_479) == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; 
x_480 = lean_ctor_get(x_479, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_479, 1);
lean_inc(x_481);
lean_dec(x_479);
x_482 = lean_ctor_get(x_469, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_482, 0);
lean_inc(x_483);
lean_dec(x_482);
x_484 = lean_ctor_get(x_470, 0);
lean_inc(x_484);
lean_dec(x_470);
x_485 = lean_ctor_get(x_484, 0);
lean_inc(x_485);
lean_dec(x_484);
x_486 = lean_name_eq(x_483, x_485);
lean_dec(x_485);
lean_dec(x_483);
if (x_486 == 0)
{
lean_object* x_487; uint8_t x_488; 
lean_dec(x_469);
lean_dec(x_3);
lean_dec(x_2);
x_487 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_480, x_4, x_5, x_6, x_7, x_481);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_488 = !lean_is_exclusive(x_487);
if (x_488 == 0)
{
lean_object* x_489; lean_object* x_490; 
x_489 = lean_ctor_get(x_487, 0);
lean_dec(x_489);
x_490 = lean_box(0);
lean_ctor_set(x_487, 0, x_490);
return x_487;
}
else
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; 
x_491 = lean_ctor_get(x_487, 1);
lean_inc(x_491);
lean_dec(x_487);
x_492 = lean_box(0);
x_493 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_493, 0, x_492);
lean_ctor_set(x_493, 1, x_491);
return x_493;
}
}
else
{
lean_object* x_494; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_480);
x_494 = lean_infer_type(x_480, x_4, x_5, x_6, x_7, x_481);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_497 = l_Lean_Meta_whnfD(x_495, x_4, x_5, x_6, x_7, x_496);
if (lean_obj_tag(x_497) == 0)
{
lean_object* x_498; 
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
if (lean_obj_tag(x_498) == 7)
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
lean_dec(x_2);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
lean_dec(x_497);
x_500 = lean_ctor_get(x_498, 1);
lean_inc(x_500);
lean_dec(x_498);
x_501 = l_Lean_Expr_headBeta(x_500);
lean_inc(x_1);
x_502 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_499);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_503 = lean_ctor_get(x_502, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_502, 1);
lean_inc(x_504);
lean_dec(x_502);
lean_inc(x_4);
x_505 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_501, x_503, x_4, x_5, x_6, x_7, x_504);
x_506 = lean_ctor_get(x_505, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_505, 1);
lean_inc(x_507);
lean_dec(x_505);
lean_inc(x_506);
x_508 = l_Lean_Expr_app___override(x_480, x_506);
x_509 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_508, x_4, x_5, x_6, x_7, x_507);
x_510 = lean_ctor_get(x_509, 1);
lean_inc(x_510);
lean_dec(x_509);
x_511 = l_Lean_Expr_mvarId_x21(x_506);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_512 = l_Lean_MVarId_tryClear(x_511, x_3, x_4, x_5, x_6, x_7, x_510);
if (lean_obj_tag(x_512) == 0)
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_513 = lean_ctor_get(x_512, 0);
lean_inc(x_513);
x_514 = lean_ctor_get(x_512, 1);
lean_inc(x_514);
lean_dec(x_512);
lean_inc(x_469);
x_515 = l_Lean_Meta_getCtorNumPropFields(x_469, x_4, x_5, x_6, x_7, x_514);
if (lean_obj_tag(x_515) == 0)
{
uint8_t x_516; 
x_516 = !lean_is_exclusive(x_515);
if (x_516 == 0)
{
lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_517 = lean_ctor_get(x_515, 0);
x_518 = lean_ctor_get(x_469, 4);
lean_inc(x_518);
lean_dec(x_469);
x_519 = lean_nat_sub(x_518, x_517);
lean_dec(x_517);
lean_dec(x_518);
x_520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_520, 0, x_513);
lean_ctor_set(x_520, 1, x_519);
lean_ctor_set(x_515, 0, x_520);
return x_515;
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; 
x_521 = lean_ctor_get(x_515, 0);
x_522 = lean_ctor_get(x_515, 1);
lean_inc(x_522);
lean_inc(x_521);
lean_dec(x_515);
x_523 = lean_ctor_get(x_469, 4);
lean_inc(x_523);
lean_dec(x_469);
x_524 = lean_nat_sub(x_523, x_521);
lean_dec(x_521);
lean_dec(x_523);
x_525 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_525, 0, x_513);
lean_ctor_set(x_525, 1, x_524);
x_526 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_526, 0, x_525);
lean_ctor_set(x_526, 1, x_522);
return x_526;
}
}
else
{
uint8_t x_527; 
lean_dec(x_513);
lean_dec(x_469);
x_527 = !lean_is_exclusive(x_515);
if (x_527 == 0)
{
return x_515;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_528 = lean_ctor_get(x_515, 0);
x_529 = lean_ctor_get(x_515, 1);
lean_inc(x_529);
lean_inc(x_528);
lean_dec(x_515);
x_530 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_530, 0, x_528);
lean_ctor_set(x_530, 1, x_529);
return x_530;
}
}
}
else
{
uint8_t x_531; 
lean_dec(x_469);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_531 = !lean_is_exclusive(x_512);
if (x_531 == 0)
{
return x_512;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_532 = lean_ctor_get(x_512, 0);
x_533 = lean_ctor_get(x_512, 1);
lean_inc(x_533);
lean_inc(x_532);
lean_dec(x_512);
x_534 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_534, 0, x_532);
lean_ctor_set(x_534, 1, x_533);
return x_534;
}
}
}
else
{
uint8_t x_535; 
lean_dec(x_501);
lean_dec(x_480);
lean_dec(x_469);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_535 = !lean_is_exclusive(x_502);
if (x_535 == 0)
{
return x_502;
}
else
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; 
x_536 = lean_ctor_get(x_502, 0);
x_537 = lean_ctor_get(x_502, 1);
lean_inc(x_537);
lean_inc(x_536);
lean_dec(x_502);
x_538 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_538, 0, x_536);
lean_ctor_set(x_538, 1, x_537);
return x_538;
}
}
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; 
lean_dec(x_498);
lean_dec(x_480);
lean_dec(x_469);
lean_dec(x_3);
x_539 = lean_ctor_get(x_497, 1);
lean_inc(x_539);
lean_dec(x_497);
x_540 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_541 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_540, x_4, x_5, x_6, x_7, x_539);
lean_dec(x_7);
lean_dec(x_5);
return x_541;
}
}
else
{
uint8_t x_542; 
lean_dec(x_480);
lean_dec(x_469);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_542 = !lean_is_exclusive(x_497);
if (x_542 == 0)
{
return x_497;
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_543 = lean_ctor_get(x_497, 0);
x_544 = lean_ctor_get(x_497, 1);
lean_inc(x_544);
lean_inc(x_543);
lean_dec(x_497);
x_545 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_545, 0, x_543);
lean_ctor_set(x_545, 1, x_544);
return x_545;
}
}
}
else
{
uint8_t x_546; 
lean_dec(x_480);
lean_dec(x_469);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_546 = !lean_is_exclusive(x_494);
if (x_546 == 0)
{
return x_494;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; 
x_547 = lean_ctor_get(x_494, 0);
x_548 = lean_ctor_get(x_494, 1);
lean_inc(x_548);
lean_inc(x_547);
lean_dec(x_494);
x_549 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_549, 0, x_547);
lean_ctor_set(x_549, 1, x_548);
return x_549;
}
}
}
}
else
{
uint8_t x_550; 
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_550 = !lean_is_exclusive(x_479);
if (x_550 == 0)
{
return x_479;
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_551 = lean_ctor_get(x_479, 0);
x_552 = lean_ctor_get(x_479, 1);
lean_inc(x_552);
lean_inc(x_551);
lean_dec(x_479);
x_553 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_553, 0, x_551);
lean_ctor_set(x_553, 1, x_552);
return x_553;
}
}
}
else
{
uint8_t x_554; uint8_t x_555; uint8_t x_556; uint8_t x_557; uint8_t x_558; uint8_t x_559; uint8_t x_560; uint8_t x_561; uint8_t x_562; uint8_t x_563; uint8_t x_564; uint8_t x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
x_554 = lean_ctor_get_uint8(x_467, 0);
x_555 = lean_ctor_get_uint8(x_467, 1);
x_556 = lean_ctor_get_uint8(x_467, 2);
x_557 = lean_ctor_get_uint8(x_467, 3);
x_558 = lean_ctor_get_uint8(x_467, 4);
x_559 = lean_ctor_get_uint8(x_467, 5);
x_560 = lean_ctor_get_uint8(x_467, 6);
x_561 = lean_ctor_get_uint8(x_467, 7);
x_562 = lean_ctor_get_uint8(x_467, 8);
x_563 = lean_ctor_get_uint8(x_467, 10);
x_564 = lean_ctor_get_uint8(x_467, 11);
lean_dec(x_467);
x_565 = 1;
x_566 = lean_alloc_ctor(0, 0, 12);
lean_ctor_set_uint8(x_566, 0, x_554);
lean_ctor_set_uint8(x_566, 1, x_555);
lean_ctor_set_uint8(x_566, 2, x_556);
lean_ctor_set_uint8(x_566, 3, x_557);
lean_ctor_set_uint8(x_566, 4, x_558);
lean_ctor_set_uint8(x_566, 5, x_559);
lean_ctor_set_uint8(x_566, 6, x_560);
lean_ctor_set_uint8(x_566, 7, x_561);
lean_ctor_set_uint8(x_566, 8, x_562);
lean_ctor_set_uint8(x_566, 9, x_565);
lean_ctor_set_uint8(x_566, 10, x_563);
lean_ctor_set_uint8(x_566, 11, x_564);
x_567 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_567, 0, x_566);
lean_ctor_set(x_567, 1, x_471);
lean_ctor_set(x_567, 2, x_472);
lean_ctor_set(x_567, 3, x_473);
lean_ctor_set(x_567, 4, x_474);
lean_ctor_set(x_567, 5, x_475);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_568 = l_Lean_Meta_mkNoConfusion(x_454, x_443, x_567, x_5, x_6, x_7, x_468);
if (lean_obj_tag(x_568) == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; uint8_t x_575; 
x_569 = lean_ctor_get(x_568, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_568, 1);
lean_inc(x_570);
lean_dec(x_568);
x_571 = lean_ctor_get(x_469, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_571, 0);
lean_inc(x_572);
lean_dec(x_571);
x_573 = lean_ctor_get(x_470, 0);
lean_inc(x_573);
lean_dec(x_470);
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
lean_dec(x_573);
x_575 = lean_name_eq(x_572, x_574);
lean_dec(x_574);
lean_dec(x_572);
if (x_575 == 0)
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
lean_dec(x_469);
lean_dec(x_3);
lean_dec(x_2);
x_576 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_569, x_4, x_5, x_6, x_7, x_570);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_577 = lean_ctor_get(x_576, 1);
lean_inc(x_577);
if (lean_is_exclusive(x_576)) {
 lean_ctor_release(x_576, 0);
 lean_ctor_release(x_576, 1);
 x_578 = x_576;
} else {
 lean_dec_ref(x_576);
 x_578 = lean_box(0);
}
x_579 = lean_box(0);
if (lean_is_scalar(x_578)) {
 x_580 = lean_alloc_ctor(0, 2, 0);
} else {
 x_580 = x_578;
}
lean_ctor_set(x_580, 0, x_579);
lean_ctor_set(x_580, 1, x_577);
return x_580;
}
else
{
lean_object* x_581; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_569);
x_581 = lean_infer_type(x_569, x_4, x_5, x_6, x_7, x_570);
if (lean_obj_tag(x_581) == 0)
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_582 = lean_ctor_get(x_581, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_581, 1);
lean_inc(x_583);
lean_dec(x_581);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_584 = l_Lean_Meta_whnfD(x_582, x_4, x_5, x_6, x_7, x_583);
if (lean_obj_tag(x_584) == 0)
{
lean_object* x_585; 
x_585 = lean_ctor_get(x_584, 0);
lean_inc(x_585);
if (lean_obj_tag(x_585) == 7)
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; 
lean_dec(x_2);
x_586 = lean_ctor_get(x_584, 1);
lean_inc(x_586);
lean_dec(x_584);
x_587 = lean_ctor_get(x_585, 1);
lean_inc(x_587);
lean_dec(x_585);
x_588 = l_Lean_Expr_headBeta(x_587);
lean_inc(x_1);
x_589 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_586);
if (lean_obj_tag(x_589) == 0)
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_590 = lean_ctor_get(x_589, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_589, 1);
lean_inc(x_591);
lean_dec(x_589);
lean_inc(x_4);
x_592 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_588, x_590, x_4, x_5, x_6, x_7, x_591);
x_593 = lean_ctor_get(x_592, 0);
lean_inc(x_593);
x_594 = lean_ctor_get(x_592, 1);
lean_inc(x_594);
lean_dec(x_592);
lean_inc(x_593);
x_595 = l_Lean_Expr_app___override(x_569, x_593);
x_596 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_595, x_4, x_5, x_6, x_7, x_594);
x_597 = lean_ctor_get(x_596, 1);
lean_inc(x_597);
lean_dec(x_596);
x_598 = l_Lean_Expr_mvarId_x21(x_593);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_599 = l_Lean_MVarId_tryClear(x_598, x_3, x_4, x_5, x_6, x_7, x_597);
if (lean_obj_tag(x_599) == 0)
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_600 = lean_ctor_get(x_599, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_599, 1);
lean_inc(x_601);
lean_dec(x_599);
lean_inc(x_469);
x_602 = l_Lean_Meta_getCtorNumPropFields(x_469, x_4, x_5, x_6, x_7, x_601);
if (lean_obj_tag(x_602) == 0)
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; 
x_603 = lean_ctor_get(x_602, 0);
lean_inc(x_603);
x_604 = lean_ctor_get(x_602, 1);
lean_inc(x_604);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 lean_ctor_release(x_602, 1);
 x_605 = x_602;
} else {
 lean_dec_ref(x_602);
 x_605 = lean_box(0);
}
x_606 = lean_ctor_get(x_469, 4);
lean_inc(x_606);
lean_dec(x_469);
x_607 = lean_nat_sub(x_606, x_603);
lean_dec(x_603);
lean_dec(x_606);
x_608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_608, 0, x_600);
lean_ctor_set(x_608, 1, x_607);
if (lean_is_scalar(x_605)) {
 x_609 = lean_alloc_ctor(0, 2, 0);
} else {
 x_609 = x_605;
}
lean_ctor_set(x_609, 0, x_608);
lean_ctor_set(x_609, 1, x_604);
return x_609;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_600);
lean_dec(x_469);
x_610 = lean_ctor_get(x_602, 0);
lean_inc(x_610);
x_611 = lean_ctor_get(x_602, 1);
lean_inc(x_611);
if (lean_is_exclusive(x_602)) {
 lean_ctor_release(x_602, 0);
 lean_ctor_release(x_602, 1);
 x_612 = x_602;
} else {
 lean_dec_ref(x_602);
 x_612 = lean_box(0);
}
if (lean_is_scalar(x_612)) {
 x_613 = lean_alloc_ctor(1, 2, 0);
} else {
 x_613 = x_612;
}
lean_ctor_set(x_613, 0, x_610);
lean_ctor_set(x_613, 1, x_611);
return x_613;
}
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
lean_dec(x_469);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_614 = lean_ctor_get(x_599, 0);
lean_inc(x_614);
x_615 = lean_ctor_get(x_599, 1);
lean_inc(x_615);
if (lean_is_exclusive(x_599)) {
 lean_ctor_release(x_599, 0);
 lean_ctor_release(x_599, 1);
 x_616 = x_599;
} else {
 lean_dec_ref(x_599);
 x_616 = lean_box(0);
}
if (lean_is_scalar(x_616)) {
 x_617 = lean_alloc_ctor(1, 2, 0);
} else {
 x_617 = x_616;
}
lean_ctor_set(x_617, 0, x_614);
lean_ctor_set(x_617, 1, x_615);
return x_617;
}
}
else
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
lean_dec(x_588);
lean_dec(x_569);
lean_dec(x_469);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_618 = lean_ctor_get(x_589, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_589, 1);
lean_inc(x_619);
if (lean_is_exclusive(x_589)) {
 lean_ctor_release(x_589, 0);
 lean_ctor_release(x_589, 1);
 x_620 = x_589;
} else {
 lean_dec_ref(x_589);
 x_620 = lean_box(0);
}
if (lean_is_scalar(x_620)) {
 x_621 = lean_alloc_ctor(1, 2, 0);
} else {
 x_621 = x_620;
}
lean_ctor_set(x_621, 0, x_618);
lean_ctor_set(x_621, 1, x_619);
return x_621;
}
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; 
lean_dec(x_585);
lean_dec(x_569);
lean_dec(x_469);
lean_dec(x_3);
x_622 = lean_ctor_get(x_584, 1);
lean_inc(x_622);
lean_dec(x_584);
x_623 = l_Lean_Meta_injectionCore___lambda__1___closed__13;
x_624 = l_Lean_Meta_throwTacticEx___rarg(x_2, x_1, x_623, x_4, x_5, x_6, x_7, x_622);
lean_dec(x_7);
lean_dec(x_5);
return x_624;
}
}
else
{
lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
lean_dec(x_569);
lean_dec(x_469);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_625 = lean_ctor_get(x_584, 0);
lean_inc(x_625);
x_626 = lean_ctor_get(x_584, 1);
lean_inc(x_626);
if (lean_is_exclusive(x_584)) {
 lean_ctor_release(x_584, 0);
 lean_ctor_release(x_584, 1);
 x_627 = x_584;
} else {
 lean_dec_ref(x_584);
 x_627 = lean_box(0);
}
if (lean_is_scalar(x_627)) {
 x_628 = lean_alloc_ctor(1, 2, 0);
} else {
 x_628 = x_627;
}
lean_ctor_set(x_628, 0, x_625);
lean_ctor_set(x_628, 1, x_626);
return x_628;
}
}
else
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
lean_dec(x_569);
lean_dec(x_469);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_629 = lean_ctor_get(x_581, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_581, 1);
lean_inc(x_630);
if (lean_is_exclusive(x_581)) {
 lean_ctor_release(x_581, 0);
 lean_ctor_release(x_581, 1);
 x_631 = x_581;
} else {
 lean_dec_ref(x_581);
 x_631 = lean_box(0);
}
if (lean_is_scalar(x_631)) {
 x_632 = lean_alloc_ctor(1, 2, 0);
} else {
 x_632 = x_631;
}
lean_ctor_set(x_632, 0, x_629);
lean_ctor_set(x_632, 1, x_630);
return x_632;
}
}
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
lean_dec(x_470);
lean_dec(x_469);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_633 = lean_ctor_get(x_568, 0);
lean_inc(x_633);
x_634 = lean_ctor_get(x_568, 1);
lean_inc(x_634);
if (lean_is_exclusive(x_568)) {
 lean_ctor_release(x_568, 0);
 lean_ctor_release(x_568, 1);
 x_635 = x_568;
} else {
 lean_dec_ref(x_568);
 x_635 = lean_box(0);
}
if (lean_is_scalar(x_635)) {
 x_636 = lean_alloc_ctor(1, 2, 0);
} else {
 x_636 = x_635;
}
lean_ctor_set(x_636, 0, x_633);
lean_ctor_set(x_636, 1, x_634);
return x_636;
}
}
}
}
}
else
{
uint8_t x_637; 
lean_dec(x_457);
lean_dec(x_454);
lean_dec(x_443);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_637 = !lean_is_exclusive(x_459);
if (x_637 == 0)
{
return x_459;
}
else
{
lean_object* x_638; lean_object* x_639; lean_object* x_640; 
x_638 = lean_ctor_get(x_459, 0);
x_639 = lean_ctor_get(x_459, 1);
lean_inc(x_639);
lean_inc(x_638);
lean_dec(x_459);
x_640 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_640, 0, x_638);
lean_ctor_set(x_640, 1, x_639);
return x_640;
}
}
}
else
{
uint8_t x_641; 
lean_dec(x_454);
lean_dec(x_452);
lean_dec(x_443);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_641 = !lean_is_exclusive(x_456);
if (x_641 == 0)
{
return x_456;
}
else
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_642 = lean_ctor_get(x_456, 0);
x_643 = lean_ctor_get(x_456, 1);
lean_inc(x_643);
lean_inc(x_642);
lean_dec(x_456);
x_644 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_644, 0, x_642);
lean_ctor_set(x_644, 1, x_643);
return x_644;
}
}
}
else
{
uint8_t x_645; 
lean_dec(x_452);
lean_dec(x_451);
lean_dec(x_443);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_645 = !lean_is_exclusive(x_453);
if (x_645 == 0)
{
return x_453;
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_646 = lean_ctor_get(x_453, 0);
x_647 = lean_ctor_get(x_453, 1);
lean_inc(x_647);
lean_inc(x_646);
lean_dec(x_453);
x_648 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_648, 0, x_646);
lean_ctor_set(x_648, 1, x_647);
return x_648;
}
}
}
}
else
{
uint8_t x_649; 
lean_dec(x_440);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_649 = !lean_is_exclusive(x_442);
if (x_649 == 0)
{
return x_442;
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_650 = lean_ctor_get(x_442, 0);
x_651 = lean_ctor_get(x_442, 1);
lean_inc(x_651);
lean_inc(x_650);
lean_dec(x_442);
x_652 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_652, 0, x_650);
lean_ctor_set(x_652, 1, x_651);
return x_652;
}
}
}
else
{
uint8_t x_653; 
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_653 = !lean_is_exclusive(x_439);
if (x_653 == 0)
{
return x_439;
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_654 = lean_ctor_get(x_439, 0);
x_655 = lean_ctor_get(x_439, 1);
lean_inc(x_655);
lean_inc(x_654);
lean_dec(x_439);
x_656 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_656, 0, x_654);
lean_ctor_set(x_656, 1, x_655);
return x_656;
}
}
}
}
else
{
uint8_t x_657; 
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_657 = !lean_is_exclusive(x_233);
if (x_657 == 0)
{
return x_233;
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_658 = lean_ctor_get(x_233, 0);
x_659 = lean_ctor_get(x_233, 1);
lean_inc(x_659);
lean_inc(x_658);
lean_dec(x_233);
x_660 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_660, 0, x_658);
lean_ctor_set(x_660, 1, x_659);
return x_660;
}
}
}
}
else
{
uint8_t x_661; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_661 = !lean_is_exclusive(x_15);
if (x_661 == 0)
{
return x_15;
}
else
{
lean_object* x_662; lean_object* x_663; lean_object* x_664; 
x_662 = lean_ctor_get(x_15, 0);
x_663 = lean_ctor_get(x_15, 1);
lean_inc(x_663);
lean_inc(x_662);
lean_dec(x_15);
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
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_665 = !lean_is_exclusive(x_11);
if (x_665 == 0)
{
return x_11;
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_666 = lean_ctor_get(x_11, 0);
x_667 = lean_ctor_get(x_11, 1);
lean_inc(x_667);
lean_inc(x_666);
lean_dec(x_11);
x_668 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_668, 0, x_666);
lean_ctor_set(x_668, 1, x_667);
return x_668;
}
}
}
else
{
uint8_t x_669; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_669 = !lean_is_exclusive(x_9);
if (x_669 == 0)
{
return x_9;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_670 = lean_ctor_get(x_9, 0);
x_671 = lean_ctor_get(x_9, 1);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_9);
x_672 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_672, 0, x_670);
lean_ctor_set(x_672, 1, x_671);
return x_672;
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
x_89 = l_Lean_Expr_isRawNatLit(x_33);
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
x_91 = l_Lean_Expr_isRawNatLit(x_36);
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
