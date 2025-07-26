// Lean compiler output
// Module: Lean.Meta.CheckTactic
// Imports: Lean.Meta.Basic
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0;
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3;
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__4;
static lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4;
static lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2;
static lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1;
static lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1;
static lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__5;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__6;
static lean_object* _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Meta", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("CheckTactic", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("CheckGoalType", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3;
x_2 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2;
x_3 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1;
x_4 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0;
x_5 = l_Lean_Name_mkStr4(x_4, x_3, x_2, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4;
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Expr_const___override(x_11, x_13);
x_15 = l_Lean_mkAppB(x_14, x_2, x_1);
lean_ctor_set(x_8, 0, x_15);
return x_8;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_8, 0);
x_17 = lean_ctor_get(x_8, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_8);
x_18 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4;
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_Expr_const___override(x_18, x_20);
x_22 = l_Lean_mkAppB(x_21, x_2, x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_mkCheckGoalType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_CheckTactic_mkCheckGoalType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Goal", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\nis expected to match ", 22, 22);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__5;
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_12 = l_Lean_Expr_sort___override(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = 0;
x_15 = lean_box(0);
lean_inc_ref(x_3);
x_16 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_13, x_14, x_15, x_3, x_4, x_5, x_6, x_11);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_18);
lean_inc_ref(x_3);
x_21 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_20, x_14, x_15, x_3, x_4, x_5, x_6, x_19);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4;
x_26 = lean_box(0);
lean_inc(x_10);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_26);
lean_ctor_set(x_21, 0, x_10);
x_27 = l_Lean_Expr_const___override(x_25, x_21);
x_28 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0;
lean_inc(x_18);
x_29 = lean_array_push(x_28, x_18);
lean_inc(x_23);
x_30 = lean_array_push(x_29, x_23);
x_31 = l_Lean_mkAppN(x_27, x_30);
lean_dec_ref(x_30);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_31);
lean_inc_ref(x_2);
x_32 = l_Lean_Meta_isExprDefEq(x_2, x_31, x_3, x_4, x_5, x_6, x_24);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_10);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec_ref(x_32);
x_36 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2;
x_37 = l_Lean_indentExpr(x_2);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_37);
lean_ctor_set(x_16, 0, x_36);
x_38 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__4;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_38);
lean_ctor_set(x_8, 0, x_16);
x_39 = l_Lean_indentExpr(x_31);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_8);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__6;
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_42, x_3, x_4, x_5, x_6, x_35);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
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
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec_ref(x_31);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_48 = !lean_is_exclusive(x_32);
if (x_48 == 0)
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_32, 0);
lean_dec(x_49);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_8, 1, x_16);
lean_ctor_set(x_8, 0, x_23);
lean_ctor_set(x_32, 0, x_8);
return x_32;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_32, 1);
lean_inc(x_50);
lean_dec(x_32);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_8, 1, x_16);
lean_ctor_set(x_8, 0, x_23);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_8);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
uint8_t x_52; 
lean_dec_ref(x_31);
lean_dec(x_23);
lean_free_object(x_16);
lean_dec(x_18);
lean_free_object(x_8);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_52 = !lean_is_exclusive(x_32);
if (x_52 == 0)
{
return x_32;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_32, 0);
x_54 = lean_ctor_get(x_32, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_32);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_56 = lean_ctor_get(x_21, 0);
x_57 = lean_ctor_get(x_21, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_21);
x_58 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4;
x_59 = lean_box(0);
lean_inc(x_10);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_10);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_Expr_const___override(x_58, x_60);
x_62 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0;
lean_inc(x_18);
x_63 = lean_array_push(x_62, x_18);
lean_inc(x_56);
x_64 = lean_array_push(x_63, x_56);
x_65 = l_Lean_mkAppN(x_61, x_64);
lean_dec_ref(x_64);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_65);
lean_inc_ref(x_2);
x_66 = l_Lean_Meta_isExprDefEq(x_2, x_65, x_3, x_4, x_5, x_6, x_57);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; uint8_t x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_unbox(x_67);
lean_dec(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_56);
lean_dec(x_18);
lean_dec(x_10);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
lean_dec_ref(x_66);
x_70 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2;
x_71 = l_Lean_indentExpr(x_2);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_71);
lean_ctor_set(x_16, 0, x_70);
x_72 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__4;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_72);
lean_ctor_set(x_8, 0, x_16);
x_73 = l_Lean_indentExpr(x_65);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_8);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__6;
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_76, x_3, x_4, x_5, x_6, x_69);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(1, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec_ref(x_65);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_82 = lean_ctor_get(x_66, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_83 = x_66;
} else {
 lean_dec_ref(x_66);
 x_83 = lean_box(0);
}
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_8, 1, x_16);
lean_ctor_set(x_8, 0, x_56);
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_8);
lean_ctor_set(x_84, 1, x_82);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec_ref(x_65);
lean_dec(x_56);
lean_free_object(x_16);
lean_dec(x_18);
lean_free_object(x_8);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_85 = lean_ctor_get(x_66, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_66, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_87 = x_66;
} else {
 lean_dec_ref(x_66);
 x_87 = lean_box(0);
}
if (lean_is_scalar(x_87)) {
 x_88 = lean_alloc_ctor(1, 2, 0);
} else {
 x_88 = x_87;
}
lean_ctor_set(x_88, 0, x_85);
lean_ctor_set(x_88, 1, x_86);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_89 = lean_ctor_get(x_16, 0);
x_90 = lean_ctor_get(x_16, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_16);
lean_inc(x_89);
x_91 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_91, 0, x_89);
lean_inc_ref(x_3);
x_92 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_91, x_14, x_15, x_3, x_4, x_5, x_6, x_90);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
x_96 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4;
x_97 = lean_box(0);
lean_inc(x_10);
if (lean_is_scalar(x_95)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_95;
 lean_ctor_set_tag(x_98, 1);
}
lean_ctor_set(x_98, 0, x_10);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Lean_Expr_const___override(x_96, x_98);
x_100 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0;
lean_inc(x_89);
x_101 = lean_array_push(x_100, x_89);
lean_inc(x_93);
x_102 = lean_array_push(x_101, x_93);
x_103 = l_Lean_mkAppN(x_99, x_102);
lean_dec_ref(x_102);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_103);
lean_inc_ref(x_2);
x_104 = l_Lean_Meta_isExprDefEq(x_2, x_103, x_3, x_4, x_5, x_6, x_94);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_unbox(x_105);
lean_dec(x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_93);
lean_dec(x_89);
lean_dec(x_10);
x_107 = lean_ctor_get(x_104, 1);
lean_inc(x_107);
lean_dec_ref(x_104);
x_108 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2;
x_109 = l_Lean_indentExpr(x_2);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__4;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_111);
lean_ctor_set(x_8, 0, x_110);
x_112 = l_Lean_indentExpr(x_103);
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_8);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__6;
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_115, x_3, x_4, x_5, x_6, x_107);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec_ref(x_103);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_121 = lean_ctor_get(x_104, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_122 = x_104;
} else {
 lean_dec_ref(x_104);
 x_122 = lean_box(0);
}
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_89);
lean_ctor_set(x_123, 1, x_10);
lean_ctor_set(x_8, 1, x_123);
lean_ctor_set(x_8, 0, x_93);
if (lean_is_scalar(x_122)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_122;
}
lean_ctor_set(x_124, 0, x_8);
lean_ctor_set(x_124, 1, x_121);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec_ref(x_103);
lean_dec(x_93);
lean_dec(x_89);
lean_free_object(x_8);
lean_dec(x_10);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_125 = lean_ctor_get(x_104, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_104, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_127 = x_104;
} else {
 lean_dec_ref(x_104);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_129 = lean_ctor_get(x_8, 0);
x_130 = lean_ctor_get(x_8, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_8);
lean_inc(x_129);
x_131 = l_Lean_Expr_sort___override(x_129);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
x_133 = 0;
x_134 = lean_box(0);
lean_inc_ref(x_3);
x_135 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_132, x_133, x_134, x_3, x_4, x_5, x_6, x_130);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_138 = x_135;
} else {
 lean_dec_ref(x_135);
 x_138 = lean_box(0);
}
lean_inc(x_136);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_136);
lean_inc_ref(x_3);
x_140 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_139, x_133, x_134, x_3, x_4, x_5, x_6, x_137);
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 lean_ctor_release(x_140, 1);
 x_143 = x_140;
} else {
 lean_dec_ref(x_140);
 x_143 = lean_box(0);
}
x_144 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4;
x_145 = lean_box(0);
lean_inc(x_129);
if (lean_is_scalar(x_143)) {
 x_146 = lean_alloc_ctor(1, 2, 0);
} else {
 x_146 = x_143;
 lean_ctor_set_tag(x_146, 1);
}
lean_ctor_set(x_146, 0, x_129);
lean_ctor_set(x_146, 1, x_145);
x_147 = l_Lean_Expr_const___override(x_144, x_146);
x_148 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0;
lean_inc(x_136);
x_149 = lean_array_push(x_148, x_136);
lean_inc(x_141);
x_150 = lean_array_push(x_149, x_141);
x_151 = l_Lean_mkAppN(x_147, x_150);
lean_dec_ref(x_150);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc_ref(x_151);
lean_inc_ref(x_2);
x_152 = l_Lean_Meta_isExprDefEq(x_2, x_151, x_3, x_4, x_5, x_6, x_142);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; uint8_t x_154; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_unbox(x_153);
lean_dec(x_153);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_141);
lean_dec(x_136);
lean_dec(x_129);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_dec_ref(x_152);
x_156 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2;
x_157 = l_Lean_indentExpr(x_2);
if (lean_is_scalar(x_138)) {
 x_158 = lean_alloc_ctor(7, 2, 0);
} else {
 x_158 = x_138;
 lean_ctor_set_tag(x_158, 7);
}
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__4;
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = l_Lean_indentExpr(x_151);
x_162 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
x_163 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__6;
x_164 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
x_165 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_164, x_3, x_4, x_5, x_6, x_155);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_168 = x_165;
} else {
 lean_dec_ref(x_165);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec_ref(x_151);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_170 = lean_ctor_get(x_152, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_171 = x_152;
} else {
 lean_dec_ref(x_152);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_138;
}
lean_ctor_set(x_172, 0, x_136);
lean_ctor_set(x_172, 1, x_129);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_141);
lean_ctor_set(x_173, 1, x_172);
if (lean_is_scalar(x_171)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_171;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_170);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec_ref(x_151);
lean_dec(x_141);
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_129);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_175 = lean_ctor_get(x_152, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_152, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 lean_ctor_release(x_152, 1);
 x_177 = x_152;
} else {
 lean_dec_ref(x_152);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_CheckTactic_matchCheckGoalType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_CheckTactic_matchCheckGoalType(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_CheckTactic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0 = _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0();
lean_mark_persistent(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0);
l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1 = _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1();
lean_mark_persistent(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1);
l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2 = _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2();
lean_mark_persistent(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2);
l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3 = _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3();
lean_mark_persistent(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3);
l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4 = _init_l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4();
lean_mark_persistent(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4);
l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0 = _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0();
lean_mark_persistent(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0);
l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1 = _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1();
lean_mark_persistent(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1);
l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2 = _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2();
lean_mark_persistent(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2);
l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3 = _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3();
lean_mark_persistent(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3);
l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__4 = _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__4();
lean_mark_persistent(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__4);
l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__5 = _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__5();
lean_mark_persistent(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__5);
l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__6 = _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__6();
lean_mark_persistent(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__6);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
