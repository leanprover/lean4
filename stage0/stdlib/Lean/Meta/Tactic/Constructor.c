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
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
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
lean_dec_ref(x_7);
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
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_3);
lean_inc(x_2);
x_19 = l_Lean_MVarId_apply(x_2, x_17, x_3, x_18, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
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
lean_inc_ref(x_5);
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
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
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
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_3);
lean_inc(x_2);
x_40 = l_Lean_MVarId_apply(x_2, x_38, x_3, x_39, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_37);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
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
lean_inc_ref(x_5);
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
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
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
lean_dec_ref(x_17);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_1);
x_19 = l_Lean_MVarId_getType_x27(x_1, x_4, x_5, x_6, x_7, x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec_ref(x_19);
x_22 = l_Lean_Expr_getAppFn(x_20);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 4)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec_ref(x_22);
x_25 = lean_st_ref_get(x_7, x_21);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec_ref(x_25);
x_28 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_28);
lean_dec(x_26);
x_29 = 0;
x_30 = l_Lean_Environment_find_x3f(x_28, x_23, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_dec(x_24);
lean_dec_ref(x_3);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_27;
goto block_16;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec_ref(x_30);
if (lean_obj_tag(x_31) == 5)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_32);
lean_dec_ref(x_31);
x_33 = lean_ctor_get(x_32, 4);
lean_inc(x_33);
lean_dec_ref(x_32);
x_34 = lean_box(0);
x_35 = l_Lean_MVarId_constructor___lam__0___closed__4;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_1);
x_36 = l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0___redArg(x_24, x_1, x_3, x_34, x_35, x_33, x_35, x_4, x_5, x_6, x_7, x_27);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec_ref(x_36);
x_40 = l_Lean_MVarId_constructor___lam__0___closed__8;
x_41 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_40, x_4, x_5, x_6, x_7, x_39);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_41;
}
else
{
uint8_t x_42; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_36);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_36, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
lean_dec_ref(x_38);
lean_ctor_set(x_36, 0, x_44);
return x_36;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_ctor_get(x_38, 0);
lean_inc(x_46);
lean_dec_ref(x_38);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_36);
if (x_48 == 0)
{
return x_36;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_36, 0);
x_50 = lean_ctor_get(x_36, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_36);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_dec(x_31);
lean_dec(x_24);
lean_dec_ref(x_3);
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
lean_dec_ref(x_22);
lean_dec_ref(x_3);
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
uint8_t x_52; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_19);
if (x_52 == 0)
{
return x_19;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_19, 0);
x_54 = lean_ctor_get(x_19, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_19);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_17);
if (x_56 == 0)
{
return x_17;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_17, 0);
x_58 = lean_ctor_get(x_17, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_17);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_MVarId_constructor___lam__0___closed__3;
x_15 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_14, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
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
uint8_t x_1; uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_1 = 0;
x_2 = 1;
x_3 = 0;
x_4 = lean_alloc_ctor(0, 0, 4);
lean_ctor_set_uint8(x_4, 0, x_3);
lean_ctor_set_uint8(x_4, 1, x_2);
lean_ctor_set_uint8(x_4, 2, x_1);
lean_ctor_set_uint8(x_4, 3, x_2);
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
lean_dec_ref(x_25);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_1);
x_27 = l_Lean_MVarId_getType_x27(x_1, x_4, x_5, x_6, x_7, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec_ref(x_27);
x_30 = l_Lean_Expr_getAppFn(x_28);
if (lean_obj_tag(x_30) == 4)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_96; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_st_ref_get(x_7, x_29);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec_ref(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_36);
lean_dec(x_34);
x_37 = 0;
x_96 = l_Lean_Environment_find_x3f(x_36, x_31, x_37);
if (lean_obj_tag(x_96) == 0)
{
lean_dec(x_32);
lean_dec(x_28);
lean_dec_ref(x_3);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_35;
goto block_16;
}
else
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec_ref(x_96);
if (lean_obj_tag(x_97) == 5)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc_ref(x_98);
lean_dec_ref(x_97);
x_99 = lean_ctor_get(x_98, 4);
lean_inc(x_99);
lean_dec_ref(x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_dec(x_32);
lean_dec(x_28);
lean_dec_ref(x_3);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_35;
goto block_16;
}
else
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
lean_dec_ref(x_99);
x_102 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_101, x_4, x_5, x_6, x_7, x_35);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 6)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc_ref(x_104);
lean_dec_ref(x_103);
x_105 = lean_ctor_get(x_102, 1);
lean_inc(x_105);
lean_dec_ref(x_102);
x_106 = lean_ctor_get(x_104, 0);
lean_inc_ref(x_106);
x_107 = lean_ctor_get(x_104, 3);
lean_inc(x_107);
x_108 = lean_ctor_get(x_104, 4);
lean_inc(x_108);
lean_dec_ref(x_104);
x_109 = lean_unsigned_to_nat(2u);
x_110 = lean_nat_dec_lt(x_108, x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_111 = lean_ctor_get(x_106, 0);
lean_inc(x_111);
lean_dec_ref(x_106);
x_112 = l_Lean_Expr_const___override(x_111, x_32);
x_113 = l_Lean_MVarId_existsIntro___lam__0___closed__9;
x_114 = l_Lean_Expr_getAppNumArgs(x_28);
lean_inc(x_114);
x_115 = lean_mk_array(x_114, x_113);
x_116 = lean_unsigned_to_nat(1u);
x_117 = lean_nat_sub(x_114, x_116);
lean_dec(x_114);
x_118 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_28, x_115, x_117);
x_119 = lean_unsigned_to_nat(0u);
x_120 = lean_array_get_size(x_118);
x_121 = lean_nat_dec_le(x_107, x_120);
if (x_121 == 0)
{
lean_dec(x_107);
x_38 = x_5;
x_39 = x_7;
x_40 = x_4;
x_41 = x_118;
x_42 = x_108;
x_43 = x_105;
x_44 = x_6;
x_45 = x_112;
x_46 = x_119;
x_47 = x_120;
goto block_95;
}
else
{
lean_dec(x_120);
x_38 = x_5;
x_39 = x_7;
x_40 = x_4;
x_41 = x_118;
x_42 = x_108;
x_43 = x_105;
x_44 = x_6;
x_45 = x_112;
x_46 = x_119;
x_47 = x_107;
goto block_95;
}
}
else
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; 
lean_dec(x_108);
lean_dec(x_107);
lean_dec_ref(x_106);
lean_dec(x_32);
lean_dec(x_28);
lean_dec_ref(x_3);
x_122 = l_Lean_MVarId_existsIntro___lam__0___closed__13;
x_123 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_122, x_4, x_5, x_6, x_7, x_105);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
return x_123;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_123, 0);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_123);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
else
{
lean_object* x_128; 
lean_dec(x_103);
lean_dec(x_32);
lean_dec(x_28);
lean_dec_ref(x_3);
x_128 = lean_ctor_get(x_102, 1);
lean_inc(x_128);
lean_dec_ref(x_102);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_128;
goto block_16;
}
}
else
{
uint8_t x_129; 
lean_dec(x_32);
lean_dec(x_28);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_102);
if (x_129 == 0)
{
return x_102;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_102, 0);
x_131 = lean_ctor_get(x_102, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_102);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
else
{
lean_dec_ref(x_100);
lean_dec_ref(x_99);
lean_dec(x_32);
lean_dec(x_28);
lean_dec_ref(x_3);
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
lean_dec(x_97);
lean_dec(x_32);
lean_dec(x_28);
lean_dec_ref(x_3);
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_35;
goto block_16;
}
}
block_95:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = l_Array_toSubarray___redArg(x_41, x_46, x_47);
x_49 = l_Array_ofSubarray___redArg(x_48);
lean_dec_ref(x_48);
x_50 = l_Lean_mkAppN(x_45, x_49);
lean_dec_ref(x_49);
lean_inc(x_39);
lean_inc_ref(x_44);
lean_inc(x_38);
lean_inc_ref(x_40);
lean_inc_ref(x_50);
x_51 = lean_infer_type(x_50, x_40, x_38, x_44, x_39, x_43);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec_ref(x_51);
x_54 = lean_unsigned_to_nat(2u);
x_55 = lean_nat_sub(x_42, x_54);
lean_dec(x_42);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = 0;
lean_inc(x_39);
lean_inc_ref(x_44);
lean_inc(x_38);
lean_inc_ref(x_40);
x_58 = l_Lean_Meta_forallMetaTelescopeReducing(x_52, x_56, x_57, x_40, x_38, x_44, x_39, x_53);
lean_dec_ref(x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec_ref(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Lean_mkAppN(x_50, x_61);
lean_dec(x_61);
lean_inc(x_39);
lean_inc_ref(x_44);
lean_inc(x_38);
lean_inc_ref(x_40);
lean_inc_ref(x_3);
lean_inc_ref(x_62);
x_63 = l_Lean_Meta_checkApp(x_62, x_3, x_40, x_38, x_44, x_39, x_60);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec_ref(x_63);
x_65 = l_Lean_Expr_app___override(x_62, x_3);
x_66 = l_Lean_MVarId_existsIntro___lam__0___closed__8;
x_67 = lean_box(0);
lean_inc(x_39);
lean_inc_ref(x_44);
lean_inc(x_38);
lean_inc_ref(x_40);
lean_inc(x_1);
x_68 = l_Lean_MVarId_apply(x_1, x_65, x_66, x_67, x_40, x_38, x_44, x_39, x_64);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec_ref(x_68);
x_17 = x_40;
x_18 = x_38;
x_19 = x_44;
x_20 = x_39;
x_21 = x_70;
goto block_24;
}
else
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
lean_dec_ref(x_44);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_2);
lean_dec(x_1);
x_72 = !lean_is_exclusive(x_68);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_68, 0);
lean_dec(x_73);
x_74 = lean_ctor_get(x_69, 0);
lean_inc(x_74);
lean_dec_ref(x_69);
lean_ctor_set(x_68, 0, x_74);
return x_68;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_68, 1);
lean_inc(x_75);
lean_dec(x_68);
x_76 = lean_ctor_get(x_69, 0);
lean_inc(x_76);
lean_dec_ref(x_69);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; 
lean_dec_ref(x_71);
lean_dec_ref(x_69);
x_78 = lean_ctor_get(x_68, 1);
lean_inc(x_78);
lean_dec_ref(x_68);
x_17 = x_40;
x_18 = x_38;
x_19 = x_44;
x_20 = x_39;
x_21 = x_78;
goto block_24;
}
}
}
else
{
uint8_t x_79; 
lean_dec_ref(x_44);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_2);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_68);
if (x_79 == 0)
{
return x_68;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_68, 0);
x_81 = lean_ctor_get(x_68, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_68);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec_ref(x_62);
lean_dec_ref(x_44);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_63);
if (x_83 == 0)
{
return x_63;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_63, 0);
x_85 = lean_ctor_get(x_63, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_63);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
uint8_t x_87; 
lean_dec_ref(x_50);
lean_dec_ref(x_44);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_58);
if (x_87 == 0)
{
return x_58;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_58, 0);
x_89 = lean_ctor_get(x_58, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_58);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_dec_ref(x_50);
lean_dec_ref(x_44);
lean_dec(x_42);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_51);
if (x_91 == 0)
{
return x_51;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_51, 0);
x_93 = lean_ctor_get(x_51, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_51);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
else
{
lean_dec_ref(x_30);
lean_dec(x_28);
lean_dec_ref(x_3);
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
uint8_t x_133; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_133 = !lean_is_exclusive(x_27);
if (x_133 == 0)
{
return x_27;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_27, 0);
x_135 = lean_ctor_get(x_27, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_27);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_25);
if (x_137 == 0)
{
return x_25;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_25, 0);
x_139 = lean_ctor_get(x_25, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_25);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_MVarId_existsIntro___lam__0___closed__3;
x_15 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_14, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
return x_15;
}
block_24:
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_MVarId_existsIntro___lam__0___closed__7;
x_23 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_22, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_20);
lean_dec_ref(x_19);
lean_dec(x_18);
lean_dec_ref(x_17);
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
