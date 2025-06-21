// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Actions
// Imports: Std.Tactic.BVDecide.LRAT.Actions Std.Tactic.BVDecide.LRAT.Internal.Clause
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_natLiteralToPosFinLiteral(lean_object*, lean_object*);
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0;
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_natLiteralToPosFinLiteral___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_natLiteralToPosFinLiteral(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_nat_dec_lt(x_4, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
lean_free_object(x_2);
lean_dec(x_5);
lean_dec(x_4);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_4, x_8);
x_10 = l_instDecidableNot___redArg(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_free_object(x_2);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_15 = lean_nat_dec_lt(x_13, x_1);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_13);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_13, x_17);
x_19 = l_instDecidableNot___redArg(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_13);
x_20 = lean_box(0);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_21, 1, x_14);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_natLiteralToPosFinLiteral___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_natLiteralToPosFinLiteral(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_nat_abs(x_2);
x_4 = lean_nat_dec_lt(x_3, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
lean_dec(x_3);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_6 = l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0;
x_7 = lean_int_dec_eq(x_2, x_6);
x_8 = l_instDecidableNot___redArg(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_int_dec_lt(x_6, x_2);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_3);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_array_uget(x_4, x_3);
x_8 = lean_nat_abs(x_7);
x_9 = lean_nat_dec_lt(x_8, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_11 = l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0;
x_12 = lean_int_dec_eq(x_7, x_11);
x_13 = l_instDecidableNot___redArg(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_15 = lean_box(0);
x_16 = lean_array_uset(x_4, x_3, x_15);
x_17 = lean_int_dec_lt(x_11, x_7);
lean_dec(x_7);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_18);
x_20 = 1;
x_21 = lean_usize_add(x_3, x_20);
x_22 = lean_array_uset(x_16, x_3, x_19);
x_3 = x_21;
x_4 = x_22;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
case 1:
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_array_size(x_11);
x_14 = 0;
x_15 = l_Array_mapMUnsafe_map___at___Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(x_1, x_13, x_14, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_free_object(x_2);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_1);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(x_1, x_17);
lean_dec(x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_free_object(x_2);
lean_dec(x_12);
lean_dec(x_10);
x_19 = lean_box(0);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_2, 1, x_21);
lean_ctor_set(x_18, 0, x_2);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_inc(x_22);
lean_dec(x_18);
lean_ctor_set(x_2, 1, x_22);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_2);
return x_23;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
x_26 = lean_ctor_get(x_2, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_27 = lean_array_size(x_25);
x_28 = 0;
x_29 = l_Array_mapMUnsafe_map___at___Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(x_1, x_27, x_28, x_25);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_1);
x_30 = lean_box(0);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(x_1, x_31);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_dec(x_26);
lean_dec(x_24);
x_33 = lean_box(0);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_34);
lean_ctor_set(x_36, 2, x_26);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(1, 1, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
case 2:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_2);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_ctor_get(x_2, 2);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_41 = lean_ctor_get(x_2, 0);
x_42 = lean_ctor_get(x_2, 1);
x_43 = lean_ctor_get(x_2, 3);
x_44 = lean_ctor_get(x_2, 4);
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
x_47 = lean_nat_dec_lt(x_45, x_1);
if (x_47 == 0)
{
lean_object* x_48; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_2);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_1);
x_48 = lean_box(0);
return x_48;
}
else
{
lean_object* x_49; uint8_t x_50; uint8_t x_51; 
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_nat_dec_eq(x_45, x_49);
x_51 = l_instDecidableNot___redArg(x_50);
if (x_51 == 0)
{
lean_object* x_52; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_2);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_1);
x_52 = lean_box(0);
return x_52;
}
else
{
size_t x_53; size_t x_54; lean_object* x_55; 
x_53 = lean_array_size(x_42);
x_54 = 0;
x_55 = l_Array_mapMUnsafe_map___at___Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(x_1, x_53, x_54, x_42);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_2);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_1);
x_56 = lean_box(0);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(x_1, x_57);
lean_dec(x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
lean_free_object(x_39);
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_2);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_41);
x_59 = lean_box(0);
return x_59;
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_58);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_58, 0);
lean_ctor_set(x_2, 1, x_61);
lean_ctor_set(x_58, 0, x_2);
return x_58;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_58, 0);
lean_inc(x_62);
lean_dec(x_58);
lean_ctor_set(x_2, 1, x_62);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_2);
return x_63;
}
}
}
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_64 = lean_ctor_get(x_2, 0);
x_65 = lean_ctor_get(x_2, 1);
x_66 = lean_ctor_get(x_2, 3);
x_67 = lean_ctor_get(x_2, 4);
x_68 = lean_ctor_get(x_39, 0);
x_69 = lean_ctor_get(x_39, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_39);
x_70 = lean_nat_dec_lt(x_68, x_1);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_2);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_1);
x_71 = lean_box(0);
return x_71;
}
else
{
lean_object* x_72; uint8_t x_73; uint8_t x_74; 
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_nat_dec_eq(x_68, x_72);
x_74 = l_instDecidableNot___redArg(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_2);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_1);
x_75 = lean_box(0);
return x_75;
}
else
{
size_t x_76; size_t x_77; lean_object* x_78; 
x_76 = lean_array_size(x_65);
x_77 = 0;
x_78 = l_Array_mapMUnsafe_map___at___Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(x_1, x_76, x_77, x_65);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; 
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_2);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_1);
x_79 = lean_box(0);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(x_1, x_80);
lean_dec(x_80);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; 
lean_dec(x_69);
lean_dec(x_68);
lean_free_object(x_2);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_64);
x_82 = lean_box(0);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_68);
lean_ctor_set(x_85, 1, x_69);
lean_ctor_set(x_2, 2, x_85);
lean_ctor_set(x_2, 1, x_83);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(1, 1, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_2);
return x_86;
}
}
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_87 = lean_ctor_get(x_2, 2);
x_88 = lean_ctor_get(x_2, 0);
x_89 = lean_ctor_get(x_2, 1);
x_90 = lean_ctor_get(x_2, 3);
x_91 = lean_ctor_get(x_2, 4);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_87);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_2);
x_92 = lean_ctor_get(x_87, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_94 = x_87;
} else {
 lean_dec_ref(x_87);
 x_94 = lean_box(0);
}
x_95 = lean_nat_dec_lt(x_92, x_1);
if (x_95 == 0)
{
lean_object* x_96; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_1);
x_96 = lean_box(0);
return x_96;
}
else
{
lean_object* x_97; uint8_t x_98; uint8_t x_99; 
x_97 = lean_unsigned_to_nat(0u);
x_98 = lean_nat_dec_eq(x_92, x_97);
x_99 = l_instDecidableNot___redArg(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_1);
x_100 = lean_box(0);
return x_100;
}
else
{
size_t x_101; size_t x_102; lean_object* x_103; 
x_101 = lean_array_size(x_89);
x_102 = 0;
x_103 = l_Array_mapMUnsafe_map___at___Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(x_1, x_101, x_102, x_89);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_88);
lean_dec(x_1);
x_104 = lean_box(0);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_ctor_get(x_103, 0);
lean_inc(x_105);
lean_dec(x_103);
x_106 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(x_1, x_105);
lean_dec(x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_88);
x_107 = lean_box(0);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_94;
}
lean_ctor_set(x_110, 0, x_92);
lean_ctor_set(x_110, 1, x_93);
x_111 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_111, 0, x_88);
lean_ctor_set(x_111, 1, x_108);
lean_ctor_set(x_111, 2, x_110);
lean_ctor_set(x_111, 3, x_90);
lean_ctor_set(x_111, 4, x_91);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(1, 1, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_111);
return x_112;
}
}
}
}
}
}
default: 
{
uint8_t x_113; 
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_2);
if (x_113 == 0)
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_2);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_2, 0);
lean_inc(x_115);
lean_dec(x_2);
x_116 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
return x_117;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0 = _init_l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0();
lean_mark_persistent(l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
