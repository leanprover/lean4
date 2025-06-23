// Lean compiler output
// Module: Lean.Meta.Tactic.Constructor
// Imports: Lean.Meta.Check Lean.Meta.Tactic.Util Lean.Meta.Tactic.Apply
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_existsIntro___lam__0___closed__10;
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_constructor___lam__0___closed__0;
static lean_object* l_Lean_MVarId_existsIntro___lam__0___closed__6;
static lean_object* l_Lean_MVarId_constructor___lam__0___closed__8;
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_MVarId_existsIntro___lam__0___closed__1;
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_existsIntro___lam__0___closed__7;
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lean_MVarId_existsIntro___lam__0___closed__3;
static lean_object* l_Lean_MVarId_constructor___lam__0___closed__6;
static lean_object* l_Lean_MVarId_constructor___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_MVarId_existsIntro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_constructor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_existsIntro___lam__0___closed__9;
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
static lean_object* l_Lean_MVarId_existsIntro___lam__0___closed__5;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
static lean_object* l_Lean_MVarId_existsIntro___lam__0___closed__4;
static lean_object* l_Lean_MVarId_existsIntro___lam__0___closed__11;
static lean_object* l_Lean_MVarId_constructor___closed__1;
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_constructor___lam__0___closed__1;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_constructor___lam__0___closed__3;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_constructor___lam__0___closed__4;
static lean_object* l_Lean_MVarId_existsIntro___lam__0___closed__8;
static lean_object* l_Lean_MVarId_existsIntro___lam__0___closed__0;
static lean_object* l_Lean_MVarId_existsIntro___closed__1;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_existsIntro___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_constructor___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_existsIntro___lam__0___closed__13;
static lean_object* l_Lean_MVarId_existsIntro___closed__0;
static lean_object* l_Lean_MVarId_constructor___lam__0___closed__5;
uint8_t l_Lean_Exception_isRuntime(lean_object*);
static lean_object* l_Lean_MVarId_existsIntro___lam__0___closed__12;
static lean_object* l_Lean_MVarId_constructor___lam__0___closed__7;
LEAN_EXPORT lean_object* l_Lean_MVarId_constructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_MVarId_existsIntro___lam__0___closed__2;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = !lean_is_exclusive(x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_6, 0);
x_16 = lean_ctor_get(x_6, 1);
lean_inc(x_1);
x_17 = l_Lean_Expr_const___override(x_15, x_1);
x_18 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
x_19 = l_Lean_MVarId_apply(x_2, x_17, x_3, x_18, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 0, x_22);
lean_ctor_set(x_19, 0, x_6);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set_tag(x_6, 0);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_34; 
lean_free_object(x_6);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_29 = x_19;
} else {
 lean_dec_ref(x_19);
 x_29 = lean_box(0);
}
x_34 = l_Lean_Exception_isInterrupt(x_27);
if (x_34 == 0)
{
uint8_t x_35; 
x_35 = l_Lean_Exception_isRuntime(x_27);
x_30 = x_35;
goto block_33;
}
else
{
x_30 = x_34;
goto block_33;
}
block_33:
{
if (x_30 == 0)
{
lean_dec(x_29);
lean_dec(x_27);
lean_inc(x_5);
{
lean_object* _tmp_5 = x_16;
lean_object* _tmp_6 = x_5;
lean_object* _tmp_11 = x_28;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_12 = _tmp_11;
}
goto _start;
}
else
{
lean_object* x_32; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_29;
}
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_6, 0);
x_37 = lean_ctor_get(x_6, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_6);
lean_inc(x_1);
x_38 = l_Lean_Expr_const___override(x_36, x_1);
x_39 = lean_box(0);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_2);
x_40 = l_Lean_MVarId_apply(x_2, x_38, x_3, x_39, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_37);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_43 = x_40;
} else {
 lean_dec_ref(x_40);
 x_43 = lean_box(0);
}
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_4);
if (lean_is_scalar(x_43)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_43;
}
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_54; 
x_47 = lean_ctor_get(x_40, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_49 = x_40;
} else {
 lean_dec_ref(x_40);
 x_49 = lean_box(0);
}
x_54 = l_Lean_Exception_isInterrupt(x_47);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = l_Lean_Exception_isRuntime(x_47);
x_50 = x_55;
goto block_53;
}
else
{
x_50 = x_54;
goto block_53;
}
block_53:
{
if (x_50 == 0)
{
lean_dec(x_49);
lean_dec(x_47);
lean_inc(x_5);
{
lean_object* _tmp_5 = x_37;
lean_object* _tmp_6 = x_5;
lean_object* _tmp_11 = x_48;
x_6 = _tmp_5;
x_7 = _tmp_6;
x_12 = _tmp_11;
}
goto _start;
}
else
{
lean_object* x_52; 
lean_dec(x_37);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_48);
return x_52;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
static lean_object* _init_l_Lean_MVarId_constructor___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("target is not an inductive datatype", 35, 35);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_constructor___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_constructor___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_constructor___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_constructor___lam__0___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_constructor___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_constructor___lam__0___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_constructor___lam__0___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_MVarId_constructor___lam__0___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("no applicable constructor found", 31, 31);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_constructor___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_constructor___lam__0___closed__5;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_constructor___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_constructor___lam__0___closed__6;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_constructor___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_constructor___lam__0___closed__7;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_constructor___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; 
lean_inc(x_2);
lean_inc(x_1);
x_17 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_19 = l_Lean_MVarId_getType_x27(x_1, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Lean_Expr_getAppFn(x_20);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 4)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_st_ref_get(x_7, x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = lean_unbox(x_29);
x_31 = l_Lean_Environment_find_x3f(x_28, x_23, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_dec(x_24);
lean_dec(x_3);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_27;
goto block_16;
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 5)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_33, 4);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_box(0);
x_36 = l_Lean_MVarId_constructor___lam__0___closed__4;
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_37 = l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0___redArg(x_24, x_1, x_3, x_35, x_36, x_34, x_36, x_4, x_5, x_6, x_7, x_27);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec(x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = l_Lean_MVarId_constructor___lam__0___closed__8;
x_42 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_41, x_4, x_5, x_6, x_7, x_40);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_37);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_37, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_39, 0);
lean_inc(x_45);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_45);
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_37, 1);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_ctor_get(x_39, 0);
lean_inc(x_47);
lean_dec(x_39);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_37);
if (x_49 == 0)
{
return x_37;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_37, 0);
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_37);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_dec(x_32);
lean_dec(x_24);
lean_dec(x_3);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_27;
goto block_16;
}
}
}
else
{
lean_dec(x_22);
lean_dec(x_3);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_21;
goto block_16;
}
}
else
{
uint8_t x_53; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_19);
if (x_53 == 0)
{
return x_19;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_19, 0);
x_55 = lean_ctor_get(x_19, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_19);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_17);
if (x_57 == 0)
{
return x_17;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_17, 0);
x_59 = lean_ctor_get(x_17, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_17);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_MVarId_constructor___lam__0___closed__3;
x_15 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_14, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_15;
}
}
}
static lean_object* _init_l_Lean_MVarId_constructor___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("constructor", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_constructor___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_constructor___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_constructor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_MVarId_constructor___closed__1;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_constructor___lam__0), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_2);
x_10 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
return x_15;
}
}
static lean_object* _init_l_Lean_MVarId_existsIntro___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected number of subgoals", 29, 29);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_existsIntro___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_existsIntro___lam__0___closed__0;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_existsIntro___lam__0___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_existsIntro___lam__0___closed__1;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_existsIntro___lam__0___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_existsIntro___lam__0___closed__2;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_existsIntro___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("target is not an inductive datatype with one constructor", 56, 56);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_existsIntro___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_existsIntro___lam__0___closed__4;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_existsIntro___lam__0___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_existsIntro___lam__0___closed__5;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_existsIntro___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_existsIntro___lam__0___closed__6;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_existsIntro___lam__0___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_existsIntro___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; uint8_t x_8; 
x_1 = lean_box(0);
x_2 = lean_box(1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 0, 4);
x_5 = lean_unbox(x_3);
lean_ctor_set_uint8(x_4, 0, x_5);
x_6 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, 1, x_6);
x_7 = lean_unbox(x_1);
lean_ctor_set_uint8(x_4, 2, x_7);
x_8 = lean_unbox(x_2);
lean_ctor_set_uint8(x_4, 3, x_8);
return x_4;
}
}
static lean_object* _init_l_Lean_MVarId_existsIntro___lam__0___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("constructor must have at least two fields", 41, 41);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_existsIntro___lam__0___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_existsIntro___lam__0___closed__10;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_existsIntro___lam__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_existsIntro___lam__0___closed__11;
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_MVarId_existsIntro___lam__0___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_existsIntro___lam__0___closed__12;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_existsIntro___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_25; 
lean_inc(x_2);
lean_inc(x_1);
x_25 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_27 = l_Lean_MVarId_getType_x27(x_1, x_4, x_5, x_6, x_7, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_getAppFn(x_28);
if (lean_obj_tag(x_30) == 4)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_st_ref_get(x_7, x_29);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_box(0);
x_38 = lean_unbox(x_37);
x_39 = l_Lean_Environment_find_x3f(x_36, x_31, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_3);
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_35;
goto block_24;
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_39, 0);
if (lean_obj_tag(x_41) == 5)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_42, 4);
lean_inc(x_43);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_free_object(x_39);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_3);
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_35;
goto block_24;
}
else
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_45, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 6)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
lean_dec(x_46);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_48, 4);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_nat_dec_lt(x_52, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_55 = lean_ctor_get(x_50, 0);
lean_inc(x_55);
lean_dec(x_50);
x_56 = l_Lean_Expr_const___override(x_55, x_32);
x_57 = l_Lean_MVarId_existsIntro___lam__0___closed__8;
x_58 = l_Lean_Expr_getAppNumArgs(x_28);
lean_inc(x_58);
x_59 = lean_mk_array(x_58, x_57);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_sub(x_58, x_60);
lean_dec(x_58);
x_62 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_28, x_59, x_61);
x_63 = lean_unsigned_to_nat(0u);
x_64 = l_Array_toSubarray___redArg(x_62, x_63, x_51);
x_65 = l_Array_ofSubarray___redArg(x_64);
lean_dec(x_64);
x_66 = l_Lean_mkAppN(x_56, x_65);
lean_dec(x_65);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_66);
x_67 = lean_infer_type(x_66, x_4, x_5, x_6, x_7, x_49);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_nat_sub(x_52, x_53);
lean_dec(x_52);
lean_ctor_set(x_39, 0, x_70);
x_71 = lean_box(0);
x_72 = lean_unbox(x_71);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_73 = l_Lean_Meta_forallMetaTelescopeReducing(x_68, x_39, x_72, x_4, x_5, x_6, x_7, x_69);
lean_dec(x_39);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_mkAppN(x_66, x_76);
lean_dec(x_76);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_77);
x_78 = l_Lean_Meta_checkApp(x_77, x_3, x_4, x_5, x_6, x_7, x_75);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
lean_dec(x_78);
x_80 = l_Lean_Expr_app___override(x_77, x_3);
x_81 = l_Lean_MVarId_existsIntro___lam__0___closed__9;
x_82 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_83 = l_Lean_MVarId_apply(x_1, x_80, x_81, x_82, x_4, x_5, x_6, x_7, x_79);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_85;
goto block_16;
}
else
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
uint8_t x_87; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_83, 0);
lean_dec(x_88);
x_89 = lean_ctor_get(x_84, 0);
lean_inc(x_89);
lean_dec(x_84);
lean_ctor_set(x_83, 0, x_89);
return x_83;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_83, 1);
lean_inc(x_90);
lean_dec(x_83);
x_91 = lean_ctor_get(x_84, 0);
lean_inc(x_91);
lean_dec(x_84);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_90);
return x_92;
}
}
else
{
lean_object* x_93; 
lean_dec(x_86);
lean_dec(x_84);
x_93 = lean_ctor_get(x_83, 1);
lean_inc(x_93);
lean_dec(x_83);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_93;
goto block_16;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_83);
if (x_94 == 0)
{
return x_83;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_83, 0);
x_96 = lean_ctor_get(x_83, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_83);
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
lean_dec(x_77);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = !lean_is_exclusive(x_78);
if (x_98 == 0)
{
return x_78;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_78, 0);
x_100 = lean_ctor_get(x_78, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_78);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_66);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_73);
if (x_102 == 0)
{
return x_73;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_73, 0);
x_104 = lean_ctor_get(x_73, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_73);
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
lean_dec(x_66);
lean_dec(x_52);
lean_free_object(x_39);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_67);
if (x_106 == 0)
{
return x_67;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_67, 0);
x_108 = lean_ctor_get(x_67, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_67);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_free_object(x_39);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_3);
x_110 = l_Lean_MVarId_existsIntro___lam__0___closed__13;
x_111 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_110, x_4, x_5, x_6, x_7, x_49);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
return x_111;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_111, 0);
x_114 = lean_ctor_get(x_111, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_111);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
lean_object* x_116; 
lean_dec(x_47);
lean_free_object(x_39);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_3);
x_116 = lean_ctor_get(x_46, 1);
lean_inc(x_116);
lean_dec(x_46);
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_116;
goto block_24;
}
}
else
{
uint8_t x_117; 
lean_free_object(x_39);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_46);
if (x_117 == 0)
{
return x_46;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_46, 0);
x_119 = lean_ctor_get(x_46, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_46);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_dec(x_44);
lean_dec(x_43);
lean_free_object(x_39);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_3);
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_35;
goto block_24;
}
}
}
else
{
lean_free_object(x_39);
lean_dec(x_41);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_3);
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_35;
goto block_24;
}
}
else
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_39, 0);
lean_inc(x_121);
lean_dec(x_39);
if (lean_obj_tag(x_121) == 5)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec(x_121);
x_123 = lean_ctor_get(x_122, 4);
lean_inc(x_123);
lean_dec(x_122);
if (lean_obj_tag(x_123) == 0)
{
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_3);
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_35;
goto block_24;
}
else
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
lean_dec(x_123);
x_126 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_125, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 6)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
lean_dec(x_127);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 3);
lean_inc(x_131);
x_132 = lean_ctor_get(x_128, 4);
lean_inc(x_132);
lean_dec(x_128);
x_133 = lean_unsigned_to_nat(2u);
x_134 = lean_nat_dec_lt(x_132, x_133);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_135 = lean_ctor_get(x_130, 0);
lean_inc(x_135);
lean_dec(x_130);
x_136 = l_Lean_Expr_const___override(x_135, x_32);
x_137 = l_Lean_MVarId_existsIntro___lam__0___closed__8;
x_138 = l_Lean_Expr_getAppNumArgs(x_28);
lean_inc(x_138);
x_139 = lean_mk_array(x_138, x_137);
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_nat_sub(x_138, x_140);
lean_dec(x_138);
x_142 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_28, x_139, x_141);
x_143 = lean_unsigned_to_nat(0u);
x_144 = l_Array_toSubarray___redArg(x_142, x_143, x_131);
x_145 = l_Array_ofSubarray___redArg(x_144);
lean_dec(x_144);
x_146 = l_Lean_mkAppN(x_136, x_145);
lean_dec(x_145);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_146);
x_147 = lean_infer_type(x_146, x_4, x_5, x_6, x_7, x_129);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_150 = lean_nat_sub(x_132, x_133);
lean_dec(x_132);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
x_152 = lean_box(0);
x_153 = lean_unbox(x_152);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_154 = l_Lean_Meta_forallMetaTelescopeReducing(x_148, x_151, x_153, x_4, x_5, x_6, x_7, x_149);
lean_dec(x_151);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
lean_dec(x_154);
x_157 = lean_ctor_get(x_155, 0);
lean_inc(x_157);
lean_dec(x_155);
x_158 = l_Lean_mkAppN(x_146, x_157);
lean_dec(x_157);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_158);
x_159 = l_Lean_Meta_checkApp(x_158, x_3, x_4, x_5, x_6, x_7, x_156);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
x_161 = l_Lean_Expr_app___override(x_158, x_3);
x_162 = l_Lean_MVarId_existsIntro___lam__0___closed__9;
x_163 = lean_box(0);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_164 = l_Lean_MVarId_apply(x_1, x_161, x_162, x_163, x_4, x_5, x_6, x_7, x_160);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; 
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_166;
goto block_16;
}
else
{
lean_object* x_167; 
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
if (lean_obj_tag(x_167) == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_168 = lean_ctor_get(x_164, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_169 = x_164;
} else {
 lean_dec_ref(x_164);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_165, 0);
lean_inc(x_170);
lean_dec(x_165);
if (lean_is_scalar(x_169)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_169;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_168);
return x_171;
}
else
{
lean_object* x_172; 
lean_dec(x_167);
lean_dec(x_165);
x_172 = lean_ctor_get(x_164, 1);
lean_inc(x_172);
lean_dec(x_164);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_172;
goto block_16;
}
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_173 = lean_ctor_get(x_164, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_164, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_175 = x_164;
} else {
 lean_dec_ref(x_164);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_158);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_177 = lean_ctor_get(x_159, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_159, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_179 = x_159;
} else {
 lean_dec_ref(x_159);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_dec(x_146);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_181 = lean_ctor_get(x_154, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_154, 1);
lean_inc(x_182);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_183 = x_154;
} else {
 lean_dec_ref(x_154);
 x_183 = lean_box(0);
}
if (lean_is_scalar(x_183)) {
 x_184 = lean_alloc_ctor(1, 2, 0);
} else {
 x_184 = x_183;
}
lean_ctor_set(x_184, 0, x_181);
lean_ctor_set(x_184, 1, x_182);
return x_184;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_146);
lean_dec(x_132);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_185 = lean_ctor_get(x_147, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_147, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_187 = x_147;
} else {
 lean_dec_ref(x_147);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_3);
x_189 = l_Lean_MVarId_existsIntro___lam__0___closed__13;
x_190 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_189, x_4, x_5, x_6, x_7, x_129);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_193 = x_190;
} else {
 lean_dec_ref(x_190);
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
lean_object* x_195; 
lean_dec(x_127);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_3);
x_195 = lean_ctor_get(x_126, 1);
lean_inc(x_195);
lean_dec(x_126);
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_195;
goto block_24;
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_196 = lean_ctor_get(x_126, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_126, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_198 = x_126;
} else {
 lean_dec_ref(x_126);
 x_198 = lean_box(0);
}
if (lean_is_scalar(x_198)) {
 x_199 = lean_alloc_ctor(1, 2, 0);
} else {
 x_199 = x_198;
}
lean_ctor_set(x_199, 0, x_196);
lean_ctor_set(x_199, 1, x_197);
return x_199;
}
}
else
{
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_3);
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_35;
goto block_24;
}
}
}
else
{
lean_dec(x_121);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_3);
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_35;
goto block_24;
}
}
}
}
else
{
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_3);
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_29;
goto block_24;
}
}
else
{
uint8_t x_200; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_200 = !lean_is_exclusive(x_27);
if (x_200 == 0)
{
return x_27;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_27, 0);
x_202 = lean_ctor_get(x_27, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_27);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_204 = !lean_is_exclusive(x_25);
if (x_204 == 0)
{
return x_25;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_25, 0);
x_206 = lean_ctor_get(x_25, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_25);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_MVarId_existsIntro___lam__0___closed__3;
x_15 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_14, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_15;
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_MVarId_existsIntro___lam__0___closed__7;
x_23 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_22, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
return x_23;
}
}
}
static lean_object* _init_l_Lean_MVarId_existsIntro___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("exists", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lean_MVarId_existsIntro___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_MVarId_existsIntro___closed__0;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_existsIntro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = l_Lean_MVarId_existsIntro___closed__1;
lean_inc(x_1);
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_existsIntro___lam__0), 8, 3);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_8);
lean_closure_set(x_9, 2, x_2);
x_10 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Constructor(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_MVarId_constructor___lam__0___closed__0 = _init_l_Lean_MVarId_constructor___lam__0___closed__0();
lean_mark_persistent(l_Lean_MVarId_constructor___lam__0___closed__0);
l_Lean_MVarId_constructor___lam__0___closed__1 = _init_l_Lean_MVarId_constructor___lam__0___closed__1();
lean_mark_persistent(l_Lean_MVarId_constructor___lam__0___closed__1);
l_Lean_MVarId_constructor___lam__0___closed__2 = _init_l_Lean_MVarId_constructor___lam__0___closed__2();
lean_mark_persistent(l_Lean_MVarId_constructor___lam__0___closed__2);
l_Lean_MVarId_constructor___lam__0___closed__3 = _init_l_Lean_MVarId_constructor___lam__0___closed__3();
lean_mark_persistent(l_Lean_MVarId_constructor___lam__0___closed__3);
l_Lean_MVarId_constructor___lam__0___closed__4 = _init_l_Lean_MVarId_constructor___lam__0___closed__4();
lean_mark_persistent(l_Lean_MVarId_constructor___lam__0___closed__4);
l_Lean_MVarId_constructor___lam__0___closed__5 = _init_l_Lean_MVarId_constructor___lam__0___closed__5();
lean_mark_persistent(l_Lean_MVarId_constructor___lam__0___closed__5);
l_Lean_MVarId_constructor___lam__0___closed__6 = _init_l_Lean_MVarId_constructor___lam__0___closed__6();
lean_mark_persistent(l_Lean_MVarId_constructor___lam__0___closed__6);
l_Lean_MVarId_constructor___lam__0___closed__7 = _init_l_Lean_MVarId_constructor___lam__0___closed__7();
lean_mark_persistent(l_Lean_MVarId_constructor___lam__0___closed__7);
l_Lean_MVarId_constructor___lam__0___closed__8 = _init_l_Lean_MVarId_constructor___lam__0___closed__8();
lean_mark_persistent(l_Lean_MVarId_constructor___lam__0___closed__8);
l_Lean_MVarId_constructor___closed__0 = _init_l_Lean_MVarId_constructor___closed__0();
lean_mark_persistent(l_Lean_MVarId_constructor___closed__0);
l_Lean_MVarId_constructor___closed__1 = _init_l_Lean_MVarId_constructor___closed__1();
lean_mark_persistent(l_Lean_MVarId_constructor___closed__1);
l_Lean_MVarId_existsIntro___lam__0___closed__0 = _init_l_Lean_MVarId_existsIntro___lam__0___closed__0();
lean_mark_persistent(l_Lean_MVarId_existsIntro___lam__0___closed__0);
l_Lean_MVarId_existsIntro___lam__0___closed__1 = _init_l_Lean_MVarId_existsIntro___lam__0___closed__1();
lean_mark_persistent(l_Lean_MVarId_existsIntro___lam__0___closed__1);
l_Lean_MVarId_existsIntro___lam__0___closed__2 = _init_l_Lean_MVarId_existsIntro___lam__0___closed__2();
lean_mark_persistent(l_Lean_MVarId_existsIntro___lam__0___closed__2);
l_Lean_MVarId_existsIntro___lam__0___closed__3 = _init_l_Lean_MVarId_existsIntro___lam__0___closed__3();
lean_mark_persistent(l_Lean_MVarId_existsIntro___lam__0___closed__3);
l_Lean_MVarId_existsIntro___lam__0___closed__4 = _init_l_Lean_MVarId_existsIntro___lam__0___closed__4();
lean_mark_persistent(l_Lean_MVarId_existsIntro___lam__0___closed__4);
l_Lean_MVarId_existsIntro___lam__0___closed__5 = _init_l_Lean_MVarId_existsIntro___lam__0___closed__5();
lean_mark_persistent(l_Lean_MVarId_existsIntro___lam__0___closed__5);
l_Lean_MVarId_existsIntro___lam__0___closed__6 = _init_l_Lean_MVarId_existsIntro___lam__0___closed__6();
lean_mark_persistent(l_Lean_MVarId_existsIntro___lam__0___closed__6);
l_Lean_MVarId_existsIntro___lam__0___closed__7 = _init_l_Lean_MVarId_existsIntro___lam__0___closed__7();
lean_mark_persistent(l_Lean_MVarId_existsIntro___lam__0___closed__7);
l_Lean_MVarId_existsIntro___lam__0___closed__8 = _init_l_Lean_MVarId_existsIntro___lam__0___closed__8();
lean_mark_persistent(l_Lean_MVarId_existsIntro___lam__0___closed__8);
l_Lean_MVarId_existsIntro___lam__0___closed__9 = _init_l_Lean_MVarId_existsIntro___lam__0___closed__9();
lean_mark_persistent(l_Lean_MVarId_existsIntro___lam__0___closed__9);
l_Lean_MVarId_existsIntro___lam__0___closed__10 = _init_l_Lean_MVarId_existsIntro___lam__0___closed__10();
lean_mark_persistent(l_Lean_MVarId_existsIntro___lam__0___closed__10);
l_Lean_MVarId_existsIntro___lam__0___closed__11 = _init_l_Lean_MVarId_existsIntro___lam__0___closed__11();
lean_mark_persistent(l_Lean_MVarId_existsIntro___lam__0___closed__11);
l_Lean_MVarId_existsIntro___lam__0___closed__12 = _init_l_Lean_MVarId_existsIntro___lam__0___closed__12();
lean_mark_persistent(l_Lean_MVarId_existsIntro___lam__0___closed__12);
l_Lean_MVarId_existsIntro___lam__0___closed__13 = _init_l_Lean_MVarId_existsIntro___lam__0___closed__13();
lean_mark_persistent(l_Lean_MVarId_existsIntro___lam__0___closed__13);
l_Lean_MVarId_existsIntro___closed__0 = _init_l_Lean_MVarId_existsIntro___closed__0();
lean_mark_persistent(l_Lean_MVarId_existsIntro___closed__0);
l_Lean_MVarId_existsIntro___closed__1 = _init_l_Lean_MVarId_existsIntro___closed__1();
lean_mark_persistent(l_Lean_MVarId_existsIntro___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
