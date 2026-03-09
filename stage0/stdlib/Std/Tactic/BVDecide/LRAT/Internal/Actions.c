// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Actions
// Imports: public import Std.Tactic.BVDecide.LRAT.Actions public import Std.Tactic.BVDecide.LRAT.Internal.Clause
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_natLiteralToPosFinLiteral(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_natLiteralToPosFinLiteral___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0;
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___boxed(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_natLiteralToPosFinLiteral(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_18; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
x_5 = x_2;
x_6 = x_18;
goto block_17;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_7; 
x_7 = lean_nat_dec_lt(x_3, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_del_object(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_nat_dec_eq(x_3, x_9);
if (x_10 == 0)
{
if (x_7 == 0)
{
lean_object* x_11; 
lean_del_object(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; 
if (x_6 == 0)
{
x_12 = x_5;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_3);
lean_ctor_set(x_15, 1, x_4);
x_12 = x_15;
goto block_14;
}
block_14:
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
else
{
lean_object* x_16; 
lean_del_object(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_box(0);
return x_16;
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
static lean_object* _init_l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0(void) {
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
lean_object* x_6; uint8_t x_7; 
x_6 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0, &l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0);
x_7 = lean_int_dec_eq(x_2, x_6);
if (x_7 == 0)
{
if (x_4 == 0)
{
lean_object* x_8; 
lean_dec(x_3);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_int_dec_lt(x_6, x_2);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = lean_box(0);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
lean_dec_ref(x_4);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_obj_once(&l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0, &l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0_once, _init_l_Std_Tactic_BVDecide_LRAT_Internal_intToLiteral___closed__0);
x_13 = lean_int_dec_eq(x_7, x_12);
if (x_13 == 0)
{
if (x_9 == 0)
{
lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_15 = lean_array_uset(x_4, x_3, x_11);
x_16 = lean_int_dec_lt(x_12, x_7);
lean_dec(x_7);
x_17 = lean_box(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = 1;
x_20 = lean_usize_add(x_3, x_19);
x_21 = lean_array_uset(x_15, x_3, x_18);
x_3 = x_20;
x_4 = x_21;
goto _start;
}
}
else
{
lean_object* x_23; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_4);
x_23 = lean_box(0);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_12; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
x_5 = x_2;
x_6 = x_12;
goto block_11;
}
else
{
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_7; 
if (x_6 == 0)
{
x_7 = x_5;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
x_7 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_37; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_2, 2);
x_37 = !lean_is_exclusive(x_2);
if (x_37 == 0)
{
x_16 = x_2;
x_17 = x_37;
goto block_36;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_2);
x_16 = lean_box(0);
x_17 = x_37;
goto block_36;
}
block_36:
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_array_size(x_14);
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(x_1, x_18, x_19, x_14);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
lean_del_object(x_16);
lean_dec_ref(x_15);
lean_dec(x_13);
x_21 = lean_box(0);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec_ref(x_20);
x_23 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(x_1, x_22);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
lean_del_object(x_16);
lean_dec_ref(x_15);
lean_dec(x_13);
x_24 = lean_box(0);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_35; 
x_25 = lean_ctor_get(x_23, 0);
x_35 = !lean_is_exclusive(x_23);
if (x_35 == 0)
{
x_26 = x_23;
x_27 = x_35;
goto block_34;
}
else
{
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_28; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 1, x_25);
x_28 = x_16;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_25);
lean_ctor_set(x_33, 2, x_15);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 0, x_28);
x_29 = x_26;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
}
}
}
case 2:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_79; 
x_38 = lean_ctor_get(x_2, 2);
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
x_41 = lean_ctor_get(x_2, 3);
x_42 = lean_ctor_get(x_2, 4);
x_79 = !lean_is_exclusive(x_2);
if (x_79 == 0)
{
x_43 = x_2;
x_44 = x_79;
goto block_78;
}
else
{
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_38);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
x_43 = lean_box(0);
x_44 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_77; 
x_45 = lean_ctor_get(x_38, 0);
x_46 = lean_ctor_get(x_38, 1);
x_77 = !lean_is_exclusive(x_38);
if (x_77 == 0)
{
x_47 = x_38;
x_48 = x_77;
goto block_76;
}
else
{
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_38);
x_47 = lean_box(0);
x_48 = x_77;
goto block_76;
}
block_76:
{
uint8_t x_49; 
x_49 = lean_nat_dec_lt(x_45, x_1);
if (x_49 == 0)
{
lean_object* x_50; 
lean_del_object(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_del_object(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_39);
x_50 = lean_box(0);
return x_50;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_dec_eq(x_45, x_51);
if (x_52 == 0)
{
if (x_49 == 0)
{
lean_object* x_53; 
lean_del_object(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_del_object(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_39);
x_53 = lean_box(0);
return x_53;
}
else
{
size_t x_54; size_t x_55; lean_object* x_56; 
x_54 = lean_array_size(x_40);
x_55 = 0;
x_56 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction_spec__0(x_1, x_54, x_55, x_40);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; 
lean_del_object(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_del_object(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec(x_39);
x_57 = lean_box(0);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec_ref(x_56);
x_59 = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_ofArray(x_1, x_58);
lean_dec(x_58);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
lean_del_object(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_del_object(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec(x_39);
x_60 = lean_box(0);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_74; 
x_61 = lean_ctor_get(x_59, 0);
x_74 = !lean_is_exclusive(x_59);
if (x_74 == 0)
{
x_62 = x_59;
x_63 = x_74;
goto block_73;
}
else
{
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_box(0);
x_63 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_64; 
if (x_48 == 0)
{
x_64 = x_47;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_45);
lean_ctor_set(x_72, 1, x_46);
x_64 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_65; 
if (x_44 == 0)
{
lean_ctor_set(x_43, 2, x_64);
lean_ctor_set(x_43, 1, x_61);
x_65 = x_43;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_70, 0, x_39);
lean_ctor_set(x_70, 1, x_61);
lean_ctor_set(x_70, 2, x_64);
lean_ctor_set(x_70, 3, x_41);
lean_ctor_set(x_70, 4, x_42);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_63 == 0)
{
lean_ctor_set(x_62, 0, x_65);
x_66 = x_62;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_65);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
}
}
}
}
else
{
lean_object* x_75; 
lean_del_object(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_del_object(x_43);
lean_dec_ref(x_42);
lean_dec_ref(x_41);
lean_dec(x_40);
lean_dec(x_39);
x_75 = lean_box(0);
return x_75;
}
}
}
}
}
default: 
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_88; 
x_80 = lean_ctor_get(x_2, 0);
x_88 = !lean_is_exclusive(x_2);
if (x_88 == 0)
{
x_81 = x_2;
x_82 = x_88;
goto block_87;
}
else
{
lean_inc(x_80);
lean_dec(x_2);
x_81 = lean_box(0);
x_82 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_83; 
if (x_82 == 0)
{
x_83 = x_81;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_86, 0, x_80);
x_83 = x_86;
goto block_85;
}
block_85:
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
return x_84;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Internal_intActionToDefaultClauseAction(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin);
lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Clause(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Tactic_BVDecide_LRAT_Internal_Actions(builtin);
}
#ifdef __cplusplus
}
#endif
