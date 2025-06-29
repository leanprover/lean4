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
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_12 = l_Lean_Expr_sort___override(x_10);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_box(0);
x_15 = lean_box(0);
x_16 = lean_unbox(x_14);
lean_inc(x_3);
x_17 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_13, x_16, x_15, x_3, x_4, x_5, x_6, x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_19);
x_22 = lean_unbox(x_14);
lean_inc(x_3);
x_23 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_21, x_22, x_15, x_3, x_4, x_5, x_6, x_20);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4;
x_28 = lean_box(0);
lean_inc(x_10);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_28);
lean_ctor_set(x_23, 0, x_10);
x_29 = l_Lean_Expr_const___override(x_27, x_23);
x_30 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0;
lean_inc(x_19);
x_31 = lean_array_push(x_30, x_19);
lean_inc(x_25);
x_32 = lean_array_push(x_31, x_25);
x_33 = l_Lean_mkAppN(x_29, x_32);
lean_dec(x_32);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_33);
lean_inc(x_2);
x_34 = l_Lean_Meta_isExprDefEq(x_2, x_33, x_3, x_4, x_5, x_6, x_26);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_dec(x_25);
lean_dec(x_19);
lean_dec(x_10);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2;
x_39 = l_Lean_indentExpr(x_2);
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_39);
lean_ctor_set(x_17, 0, x_38);
x_40 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__4;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_40);
lean_ctor_set(x_8, 0, x_17);
x_41 = l_Lean_indentExpr(x_33);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_8);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__6;
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_44, x_3, x_4, x_5, x_6, x_37);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
return x_45;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_45);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_33);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_50 = !lean_is_exclusive(x_34);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_34, 0);
lean_dec(x_51);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_8, 1, x_17);
lean_ctor_set(x_8, 0, x_25);
lean_ctor_set(x_34, 0, x_8);
return x_34;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_34, 1);
lean_inc(x_52);
lean_dec(x_34);
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_8, 1, x_17);
lean_ctor_set(x_8, 0, x_25);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_8);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_33);
lean_dec(x_25);
lean_free_object(x_17);
lean_dec(x_19);
lean_free_object(x_8);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_34);
if (x_54 == 0)
{
return x_34;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_34, 0);
x_56 = lean_ctor_get(x_34, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_34);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_58 = lean_ctor_get(x_23, 0);
x_59 = lean_ctor_get(x_23, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_23);
x_60 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4;
x_61 = lean_box(0);
lean_inc(x_10);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_10);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Expr_const___override(x_60, x_62);
x_64 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0;
lean_inc(x_19);
x_65 = lean_array_push(x_64, x_19);
lean_inc(x_58);
x_66 = lean_array_push(x_65, x_58);
x_67 = l_Lean_mkAppN(x_63, x_66);
lean_dec(x_66);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_67);
lean_inc(x_2);
x_68 = l_Lean_Meta_isExprDefEq(x_2, x_67, x_3, x_4, x_5, x_6, x_59);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; uint8_t x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_unbox(x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_58);
lean_dec(x_19);
lean_dec(x_10);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_dec(x_68);
x_72 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2;
x_73 = l_Lean_indentExpr(x_2);
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_73);
lean_ctor_set(x_17, 0, x_72);
x_74 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__4;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_74);
lean_ctor_set(x_8, 0, x_17);
x_75 = l_Lean_indentExpr(x_67);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_8);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__6;
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_78, x_3, x_4, x_5, x_6, x_71);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_67);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = lean_ctor_get(x_68, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_85 = x_68;
} else {
 lean_dec_ref(x_68);
 x_85 = lean_box(0);
}
lean_ctor_set(x_17, 1, x_10);
lean_ctor_set(x_8, 1, x_17);
lean_ctor_set(x_8, 0, x_58);
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_8);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_67);
lean_dec(x_58);
lean_free_object(x_17);
lean_dec(x_19);
lean_free_object(x_8);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_87 = lean_ctor_get(x_68, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_68, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_89 = x_68;
} else {
 lean_dec_ref(x_68);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_91 = lean_ctor_get(x_17, 0);
x_92 = lean_ctor_get(x_17, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_17);
lean_inc(x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_91);
x_94 = lean_unbox(x_14);
lean_inc(x_3);
x_95 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_93, x_94, x_15, x_3, x_4, x_5, x_6, x_92);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
x_99 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4;
x_100 = lean_box(0);
lean_inc(x_10);
if (lean_is_scalar(x_98)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_98;
 lean_ctor_set_tag(x_101, 1);
}
lean_ctor_set(x_101, 0, x_10);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_Expr_const___override(x_99, x_101);
x_103 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0;
lean_inc(x_91);
x_104 = lean_array_push(x_103, x_91);
lean_inc(x_96);
x_105 = lean_array_push(x_104, x_96);
x_106 = l_Lean_mkAppN(x_102, x_105);
lean_dec(x_105);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_106);
lean_inc(x_2);
x_107 = l_Lean_Meta_isExprDefEq(x_2, x_106, x_3, x_4, x_5, x_6, x_97);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_unbox(x_108);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_96);
lean_dec(x_91);
lean_dec(x_10);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_dec(x_107);
x_111 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2;
x_112 = l_Lean_indentExpr(x_2);
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__4;
lean_ctor_set_tag(x_8, 7);
lean_ctor_set(x_8, 1, x_114);
lean_ctor_set(x_8, 0, x_113);
x_115 = l_Lean_indentExpr(x_106);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_8);
lean_ctor_set(x_116, 1, x_115);
x_117 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__6;
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_118, x_3, x_4, x_5, x_6, x_110);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
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
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_106);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_124 = lean_ctor_get(x_107, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_125 = x_107;
} else {
 lean_dec_ref(x_107);
 x_125 = lean_box(0);
}
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_91);
lean_ctor_set(x_126, 1, x_10);
lean_ctor_set(x_8, 1, x_126);
lean_ctor_set(x_8, 0, x_96);
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_8);
lean_ctor_set(x_127, 1, x_124);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_106);
lean_dec(x_96);
lean_dec(x_91);
lean_free_object(x_8);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_128 = lean_ctor_get(x_107, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_107, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_130 = x_107;
} else {
 lean_dec_ref(x_107);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_132 = lean_ctor_get(x_8, 0);
x_133 = lean_ctor_get(x_8, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_8);
lean_inc(x_132);
x_134 = l_Lean_Expr_sort___override(x_132);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
x_136 = lean_box(0);
x_137 = lean_box(0);
x_138 = lean_unbox(x_136);
lean_inc(x_3);
x_139 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_135, x_138, x_137, x_3, x_4, x_5, x_6, x_133);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_142 = x_139;
} else {
 lean_dec_ref(x_139);
 x_142 = lean_box(0);
}
lean_inc(x_140);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_140);
x_144 = lean_unbox(x_136);
lean_inc(x_3);
x_145 = l___private_Lean_Meta_Basic_0__Lean_Meta_mkFreshExprMVarImpl(x_143, x_144, x_137, x_3, x_4, x_5, x_6, x_141);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
x_149 = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4;
x_150 = lean_box(0);
lean_inc(x_132);
if (lean_is_scalar(x_148)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_148;
 lean_ctor_set_tag(x_151, 1);
}
lean_ctor_set(x_151, 0, x_132);
lean_ctor_set(x_151, 1, x_150);
x_152 = l_Lean_Expr_const___override(x_149, x_151);
x_153 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0;
lean_inc(x_140);
x_154 = lean_array_push(x_153, x_140);
lean_inc(x_146);
x_155 = lean_array_push(x_154, x_146);
x_156 = l_Lean_mkAppN(x_152, x_155);
lean_dec(x_155);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_156);
lean_inc(x_2);
x_157 = l_Lean_Meta_isExprDefEq(x_2, x_156, x_3, x_4, x_5, x_6, x_147);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_unbox(x_158);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_146);
lean_dec(x_140);
lean_dec(x_132);
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
lean_dec(x_157);
x_161 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2;
x_162 = l_Lean_indentExpr(x_2);
if (lean_is_scalar(x_142)) {
 x_163 = lean_alloc_ctor(7, 2, 0);
} else {
 x_163 = x_142;
 lean_ctor_set_tag(x_163, 7);
}
lean_ctor_set(x_163, 0, x_161);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__4;
x_165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Lean_indentExpr(x_156);
x_167 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
x_168 = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__6;
x_169 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
x_170 = l_Lean_throwErrorAt___at___Lean_throwUnknownIdentifierAt___at___Lean_throwUnknownConstantAt___at_____private_Lean_Meta_Basic_0__Lean_Meta_getConstTemp_x3f_spec__0_spec__0_spec__0___redArg(x_1, x_169, x_3, x_4, x_5, x_6, x_160);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_156);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_175 = lean_ctor_get(x_157, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_176 = x_157;
} else {
 lean_dec_ref(x_157);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_142;
}
lean_ctor_set(x_177, 0, x_140);
lean_ctor_set(x_177, 1, x_132);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_146);
lean_ctor_set(x_178, 1, x_177);
if (lean_is_scalar(x_176)) {
 x_179 = lean_alloc_ctor(0, 2, 0);
} else {
 x_179 = x_176;
}
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_175);
return x_179;
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_156);
lean_dec(x_146);
lean_dec(x_142);
lean_dec(x_140);
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_180 = lean_ctor_get(x_157, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_157, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_182 = x_157;
} else {
 lean_dec_ref(x_157);
 x_182 = lean_box(0);
}
if (lean_is_scalar(x_182)) {
 x_183 = lean_alloc_ctor(1, 2, 0);
} else {
 x_183 = x_182;
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_181);
return x_183;
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
