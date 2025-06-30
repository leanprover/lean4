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
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
x_1 = lean_mk_string_unchecked("target is not an inductive datatype with one constructor", 56, 56);
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
x_1 = lean_mk_string_unchecked("unexpected number of subgoals", 29, 29);
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
static lean_object* _init_l_Lean_MVarId_existsIntro___lam__0___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_97; lean_object* x_98; 
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
x_97 = lean_unbox(x_37);
x_98 = l_Lean_Environment_find_x3f(x_36, x_31, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_3);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_35;
goto block_16;
}
else
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec(x_98);
if (lean_obj_tag(x_99) == 5)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
lean_dec(x_99);
x_101 = lean_ctor_get(x_100, 4);
lean_inc(x_101);
lean_dec(x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_3);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_35;
goto block_16;
}
else
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_103, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 6)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
lean_dec(x_105);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec(x_104);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 3);
lean_inc(x_109);
x_110 = lean_ctor_get(x_106, 4);
lean_inc(x_110);
lean_dec(x_106);
x_111 = lean_unsigned_to_nat(2u);
x_112 = lean_nat_dec_lt(x_110, x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_113 = lean_ctor_get(x_108, 0);
lean_inc(x_113);
lean_dec(x_108);
x_114 = l_Lean_Expr_const___override(x_113, x_32);
x_115 = l_Lean_MVarId_existsIntro___lam__0___closed__9;
x_116 = l_Lean_Expr_getAppNumArgs(x_28);
lean_inc(x_116);
x_117 = lean_mk_array(x_116, x_115);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_sub(x_116, x_118);
lean_dec(x_116);
x_120 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_28, x_117, x_119);
x_121 = lean_unsigned_to_nat(0u);
x_122 = lean_array_get_size(x_120);
x_123 = lean_nat_dec_le(x_109, x_122);
if (x_123 == 0)
{
lean_dec(x_109);
x_38 = x_7;
x_39 = x_5;
x_40 = x_114;
x_41 = x_107;
x_42 = x_120;
x_43 = x_6;
x_44 = x_4;
x_45 = x_110;
x_46 = x_121;
x_47 = x_122;
goto block_96;
}
else
{
lean_dec(x_122);
x_38 = x_7;
x_39 = x_5;
x_40 = x_114;
x_41 = x_107;
x_42 = x_120;
x_43 = x_6;
x_44 = x_4;
x_45 = x_110;
x_46 = x_121;
x_47 = x_109;
goto block_96;
}
}
else
{
lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_3);
x_124 = l_Lean_MVarId_existsIntro___lam__0___closed__13;
x_125 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_124, x_4, x_5, x_6, x_7, x_107);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
return x_125;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_125, 0);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_125);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
lean_object* x_130; 
lean_dec(x_105);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_3);
x_130 = lean_ctor_get(x_104, 1);
lean_inc(x_130);
lean_dec(x_104);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_130;
goto block_16;
}
}
else
{
uint8_t x_131; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_104);
if (x_131 == 0)
{
return x_104;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_104, 0);
x_133 = lean_ctor_get(x_104, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_104);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
else
{
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_3);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_35;
goto block_16;
}
}
}
else
{
lean_dec(x_99);
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_3);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_35;
goto block_16;
}
}
block_96:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = l_Array_toSubarray___redArg(x_42, x_46, x_47);
x_49 = l_Array_ofSubarray___redArg(x_48);
lean_dec(x_48);
x_50 = l_Lean_mkAppN(x_40, x_49);
lean_dec(x_49);
lean_inc(x_38);
lean_inc(x_43);
lean_inc(x_39);
lean_inc(x_44);
lean_inc(x_50);
x_51 = lean_infer_type(x_50, x_44, x_39, x_43, x_38, x_41);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_unsigned_to_nat(2u);
x_55 = lean_nat_sub(x_45, x_54);
lean_dec(x_45);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_box(0);
x_58 = lean_unbox(x_57);
lean_inc(x_38);
lean_inc(x_43);
lean_inc(x_39);
lean_inc(x_44);
x_59 = l_Lean_Meta_forallMetaTelescopeReducing(x_52, x_56, x_58, x_44, x_39, x_43, x_38, x_53);
lean_dec(x_56);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_mkAppN(x_50, x_62);
lean_dec(x_62);
lean_inc(x_38);
lean_inc(x_43);
lean_inc(x_39);
lean_inc(x_44);
lean_inc(x_3);
lean_inc(x_63);
x_64 = l_Lean_Meta_checkApp(x_63, x_3, x_44, x_39, x_43, x_38, x_61);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_66 = l_Lean_Expr_app___override(x_63, x_3);
x_67 = l_Lean_MVarId_existsIntro___lam__0___closed__8;
x_68 = lean_box(0);
lean_inc(x_38);
lean_inc(x_43);
lean_inc(x_39);
lean_inc(x_44);
lean_inc(x_1);
x_69 = l_Lean_MVarId_apply(x_1, x_66, x_67, x_68, x_44, x_39, x_43, x_38, x_65);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
x_17 = x_44;
x_18 = x_39;
x_19 = x_43;
x_20 = x_38;
x_21 = x_71;
goto block_24;
}
else
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_2);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_69);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_ctor_get(x_69, 0);
lean_dec(x_74);
x_75 = lean_ctor_get(x_70, 0);
lean_inc(x_75);
lean_dec(x_70);
lean_ctor_set(x_69, 0, x_75);
return x_69;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_69, 1);
lean_inc(x_76);
lean_dec(x_69);
x_77 = lean_ctor_get(x_70, 0);
lean_inc(x_77);
lean_dec(x_70);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec(x_72);
lean_dec(x_70);
x_79 = lean_ctor_get(x_69, 1);
lean_inc(x_79);
lean_dec(x_69);
x_17 = x_44;
x_18 = x_39;
x_19 = x_43;
x_20 = x_38;
x_21 = x_79;
goto block_24;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_69);
if (x_80 == 0)
{
return x_69;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_69, 0);
x_82 = lean_ctor_get(x_69, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_69);
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
lean_dec(x_63);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_64);
if (x_84 == 0)
{
return x_64;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_64, 0);
x_86 = lean_ctor_get(x_64, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_64);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_50);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_59);
if (x_88 == 0)
{
return x_59;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_59, 0);
x_90 = lean_ctor_get(x_59, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_59);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_dec(x_50);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_51);
if (x_92 == 0)
{
return x_51;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_51, 0);
x_94 = lean_ctor_get(x_51, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_51);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_3);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_29;
goto block_16;
}
}
else
{
uint8_t x_135; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_27);
if (x_135 == 0)
{
return x_27;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_27, 0);
x_137 = lean_ctor_get(x_27, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_27);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_25);
if (x_139 == 0)
{
return x_25;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_25, 0);
x_141 = lean_ctor_get(x_25, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_25);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
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
