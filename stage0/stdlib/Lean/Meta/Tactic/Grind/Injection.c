// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Injection
// Imports: Lean.Meta.CtorRecognizer Lean.Meta.Tactic.Util Lean.Meta.Tactic.Clear
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lambda__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lambda__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lambda__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lambda__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lambda__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_injection_x3f___lambda__4___closed__1;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lambda__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorAppCore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
static lean_object* l_Lean_Meta_Grind_injection_x3f___lambda__4___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lambda__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
static lean_object* l_Lean_Meta_Grind_injection_x3f___lambda__4___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_MVarId_getType(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_2);
x_12 = l_Lean_Expr_fvar___override(x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_Meta_mkNoConfusion(x_10, x_12, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_16 = lean_infer_type(x_14, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_19 = l_Lean_Meta_whnfD(x_17, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 7)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_headBeta(x_22);
lean_inc(x_1);
x_24 = l_Lean_MVarId_getTag(x_1, x_4, x_5, x_6, x_7, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_4);
x_27 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_23, x_25, x_4, x_5, x_6, x_7, x_26);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_28);
x_30 = l_Lean_Expr_app___override(x_14, x_28);
x_31 = l_Lean_MVarId_assign___at_Lean_Meta_getLevel___spec__1(x_1, x_30, x_4, x_5, x_6, x_7, x_29);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = l_Lean_Expr_mvarId_x21(x_28);
lean_dec(x_28);
x_34 = l_Lean_MVarId_clear(x_33, x_2, x_4, x_5, x_6, x_7, x_32);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_34, 0, x_37);
return x_34;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_34, 0);
x_39 = lean_ctor_get(x_34, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_34);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_34);
if (x_42 == 0)
{
return x_34;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_34, 0);
x_44 = lean_ctor_get(x_34, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_34);
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
lean_dec(x_23);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_24);
if (x_46 == 0)
{
return x_24;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_24, 0);
x_48 = lean_ctor_get(x_24, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_24);
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
lean_dec(x_20);
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_19);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_19, 0);
lean_dec(x_51);
x_52 = lean_box(0);
lean_ctor_set(x_19, 0, x_52);
return x_19;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_19, 1);
lean_inc(x_53);
lean_dec(x_19);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_19);
if (x_56 == 0)
{
return x_19;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_19, 0);
x_58 = lean_ctor_get(x_19, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_19);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_60 = !lean_is_exclusive(x_16);
if (x_60 == 0)
{
return x_16;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_16, 0);
x_62 = lean_ctor_get(x_16, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_16);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_13);
if (x_64 == 0)
{
return x_13;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_13, 0);
x_66 = lean_ctor_get(x_13, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_13);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_68 = !lean_is_exclusive(x_9);
if (x_68 == 0)
{
return x_9;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_9, 0);
x_70 = lean_ctor_get(x_9, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_9);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lambda__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_Meta_isConstructorAppCore_x3f(x_3, x_5, x_6, x_7, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_isConstructorAppCore_x3f(x_4, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_13, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_13, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_13, 0, x_23);
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_dec(x_13);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_13);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = lean_ctor_get(x_13, 1);
x_29 = lean_ctor_get(x_13, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_11, 0);
lean_inc(x_30);
lean_dec(x_11);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_name_eq(x_33, x_35);
lean_dec(x_35);
lean_dec(x_33);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_box(0);
lean_ctor_set(x_13, 0, x_37);
return x_13;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_free_object(x_13);
x_38 = lean_box(0);
x_39 = l_Lean_Meta_Grind_injection_x3f___lambda__1(x_1, x_2, x_38, x_5, x_6, x_7, x_8, x_28);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_40 = lean_ctor_get(x_13, 1);
lean_inc(x_40);
lean_dec(x_13);
x_41 = lean_ctor_get(x_11, 0);
lean_inc(x_41);
lean_dec(x_11);
x_42 = lean_ctor_get(x_20, 0);
lean_inc(x_42);
lean_dec(x_20);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_name_eq(x_44, x_46);
lean_dec(x_46);
lean_dec(x_44);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_40);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_box(0);
x_51 = l_Lean_Meta_Grind_injection_x3f___lambda__1(x_1, x_2, x_50, x_5, x_6, x_7, x_8, x_40);
return x_51;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lambda__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Grind_injection_x3f___lambda__4___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_injection_x3f___lambda__3___boxed), 6, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_injection_x3f___lambda__4___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_injection_x3f___lambda__4___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_Grind_injection_x3f___lambda__4___closed__2;
x_3 = l_Lean_Name_str___override(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lambda__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_3);
lean_inc(x_1);
x_8 = l_Lean_FVarId_getDecl(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_LocalDecl_type(x_9);
lean_dec(x_9);
x_12 = l_Lean_Meta_Grind_injection_x3f___lambda__4___closed__1;
x_13 = l_Lean_Expr_cleanupAnnotations(x_11);
x_14 = l_Lean_Expr_isApp(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_apply_6(x_12, x_15, x_3, x_4, x_5, x_6, x_10);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l_Lean_Expr_appArg(x_13, lean_box(0));
x_18 = l_Lean_Expr_appFnCleanup(x_13, lean_box(0));
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_box(0);
x_21 = lean_apply_6(x_12, x_20, x_3, x_4, x_5, x_6, x_10);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = l_Lean_Expr_appArg(x_18, lean_box(0));
x_23 = l_Lean_Expr_appFnCleanup(x_18, lean_box(0));
x_24 = l_Lean_Expr_isApp(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_apply_6(x_12, x_25, x_3, x_4, x_5, x_6, x_10);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = l_Lean_Expr_appFnCleanup(x_23, lean_box(0));
x_28 = l_Lean_Meta_Grind_injection_x3f___lambda__4___closed__3;
x_29 = l_Lean_Expr_isConstOf(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_box(0);
x_31 = lean_apply_6(x_12, x_30, x_3, x_4, x_5, x_6, x_10);
return x_31;
}
else
{
lean_object* x_32; 
x_32 = l_Lean_Meta_Grind_injection_x3f___lambda__2(x_2, x_1, x_22, x_17, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_17);
lean_dec(x_22);
return x_32;
}
}
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_8);
if (x_33 == 0)
{
return x_8;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_8, 0);
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_8);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_injection_x3f___lambda__4), 7, 2);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at___private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp___spec__2___rarg(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_injection_x3f___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lambda__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_injection_x3f___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_injection_x3f___lambda__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_injection_x3f___lambda__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_CtorRecognizer(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_injection_x3f___lambda__4___closed__1 = _init_l_Lean_Meta_Grind_injection_x3f___lambda__4___closed__1();
lean_mark_persistent(l_Lean_Meta_Grind_injection_x3f___lambda__4___closed__1);
l_Lean_Meta_Grind_injection_x3f___lambda__4___closed__2 = _init_l_Lean_Meta_Grind_injection_x3f___lambda__4___closed__2();
lean_mark_persistent(l_Lean_Meta_Grind_injection_x3f___lambda__4___closed__2);
l_Lean_Meta_Grind_injection_x3f___lambda__4___closed__3 = _init_l_Lean_Meta_Grind_injection_x3f___lambda__4___closed__3();
lean_mark_persistent(l_Lean_Meta_Grind_injection_x3f___lambda__4___closed__3);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
