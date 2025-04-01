// Lean compiler output
// Module: Std.Sat.CNF.Dimacs
// Imports: Std.Sat.CNF.Basic Std.Sat.CNF.RelabelFin
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
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_handleLit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_incrementClauses(lean_object*);
static lean_object* l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__1;
static lean_object* l_Std_Sat_CNF_dimacs___closed__1;
static lean_object* l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__2;
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Std_Sat_CNF_dimacs___closed__2;
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs_go___boxed(lean_object*, lean_object*);
static lean_object* l_Std_Sat_CNF_dimacs___closed__4;
static lean_object* l_Std_Sat_CNF_dimacs___closed__3;
LEAN_EXPORT lean_object* l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_handleLit(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_handleLit(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_nat_dec_le(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_inc(x_5);
lean_ctor_set(x_2, 1, x_5);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_nat_dec_le(x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_inc(x_13);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_13);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_handleLit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_handleLit(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Sat_CNF_Dimacs_0__Std_Sat_CNF_DimacsM_incrementClauses(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_3, x_4);
lean_dec(x_3);
lean_ctor_set(x_1, 0, x_5);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_8, x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
}
static lean_object* _init_l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("-", 1, 1);
return x_1;
}
}
static lean_object* _init_l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_nat_dec_le(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_6, 1);
x_12 = 32;
x_13 = lean_unbox(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_9, x_14);
x_16 = l___private_Init_Data_Repr_0__Nat_reprFast(x_15);
x_17 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__1;
x_18 = lean_string_append(x_17, x_16);
lean_dec(x_16);
x_19 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = lean_string_append(x_1, x_20);
lean_dec(x_20);
x_22 = lean_string_push(x_21, x_12);
x_1 = x_22;
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_9, x_24);
x_26 = l___private_Init_Data_Repr_0__Nat_reprFast(x_25);
x_27 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__2;
x_28 = lean_string_append(x_27, x_26);
lean_dec(x_26);
x_29 = lean_string_append(x_28, x_27);
x_30 = lean_string_append(x_1, x_29);
lean_dec(x_29);
x_31 = lean_string_push(x_30, x_12);
x_1 = x_31;
x_2 = x_7;
goto _start;
}
}
else
{
lean_object* x_33; uint32_t x_34; uint8_t x_35; 
lean_dec(x_8);
lean_inc(x_9);
lean_ctor_set(x_3, 1, x_9);
x_33 = lean_ctor_get(x_6, 1);
x_34 = 32;
x_35 = lean_unbox(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_9, x_36);
x_38 = l___private_Init_Data_Repr_0__Nat_reprFast(x_37);
x_39 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__1;
x_40 = lean_string_append(x_39, x_38);
lean_dec(x_38);
x_41 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__2;
x_42 = lean_string_append(x_40, x_41);
x_43 = lean_string_append(x_1, x_42);
lean_dec(x_42);
x_44 = lean_string_push(x_43, x_34);
x_1 = x_44;
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_add(x_9, x_46);
x_48 = l___private_Init_Data_Repr_0__Nat_reprFast(x_47);
x_49 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__2;
x_50 = lean_string_append(x_49, x_48);
lean_dec(x_48);
x_51 = lean_string_append(x_50, x_49);
x_52 = lean_string_append(x_1, x_51);
lean_dec(x_51);
x_53 = lean_string_push(x_52, x_34);
x_1 = x_53;
x_2 = x_7;
goto _start;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_55 = lean_ctor_get(x_2, 0);
x_56 = lean_ctor_get(x_2, 1);
x_57 = lean_ctor_get(x_3, 0);
x_58 = lean_ctor_get(x_3, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_3);
x_59 = lean_ctor_get(x_55, 0);
x_60 = lean_nat_dec_le(x_58, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; uint32_t x_63; uint8_t x_64; 
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_58);
x_62 = lean_ctor_get(x_55, 1);
x_63 = 32;
x_64 = lean_unbox(x_62);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_59, x_65);
x_67 = l___private_Init_Data_Repr_0__Nat_reprFast(x_66);
x_68 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__1;
x_69 = lean_string_append(x_68, x_67);
lean_dec(x_67);
x_70 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__2;
x_71 = lean_string_append(x_69, x_70);
x_72 = lean_string_append(x_1, x_71);
lean_dec(x_71);
x_73 = lean_string_push(x_72, x_63);
x_1 = x_73;
x_2 = x_56;
x_3 = x_61;
goto _start;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_59, x_75);
x_77 = l___private_Init_Data_Repr_0__Nat_reprFast(x_76);
x_78 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__2;
x_79 = lean_string_append(x_78, x_77);
lean_dec(x_77);
x_80 = lean_string_append(x_79, x_78);
x_81 = lean_string_append(x_1, x_80);
lean_dec(x_80);
x_82 = lean_string_push(x_81, x_63);
x_1 = x_82;
x_2 = x_56;
x_3 = x_61;
goto _start;
}
}
else
{
lean_object* x_84; lean_object* x_85; uint32_t x_86; uint8_t x_87; 
lean_dec(x_58);
lean_inc(x_59);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_57);
lean_ctor_set(x_84, 1, x_59);
x_85 = lean_ctor_get(x_55, 1);
x_86 = 32;
x_87 = lean_unbox(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_add(x_59, x_88);
x_90 = l___private_Init_Data_Repr_0__Nat_reprFast(x_89);
x_91 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__1;
x_92 = lean_string_append(x_91, x_90);
lean_dec(x_90);
x_93 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__2;
x_94 = lean_string_append(x_92, x_93);
x_95 = lean_string_append(x_1, x_94);
lean_dec(x_94);
x_96 = lean_string_push(x_95, x_86);
x_1 = x_96;
x_2 = x_56;
x_3 = x_84;
goto _start;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_add(x_59, x_98);
x_100 = l___private_Init_Data_Repr_0__Nat_reprFast(x_99);
x_101 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__2;
x_102 = lean_string_append(x_101, x_100);
lean_dec(x_100);
x_103 = lean_string_append(x_102, x_101);
x_104 = lean_string_append(x_1, x_103);
lean_dec(x_103);
x_105 = lean_string_push(x_104, x_86);
x_1 = x_105;
x_2 = x_56;
x_3 = x_84;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint32_t x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_8, x_9);
lean_dec(x_8);
lean_ctor_set(x_3, 0, x_10);
x_11 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1(x_1, x_6, x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = 48;
x_15 = lean_string_push(x_12, x_14);
x_16 = 10;
x_17 = lean_string_push(x_15, x_16);
x_1 = x_17;
x_2 = x_7;
x_3 = x_13;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint32_t x_29; lean_object* x_30; uint32_t x_31; lean_object* x_32; 
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_3, 0);
x_22 = lean_ctor_get(x_3, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_3);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_21, x_23);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_22);
x_26 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1(x_1, x_19, x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = 48;
x_30 = lean_string_push(x_27, x_29);
x_31 = 10;
x_32 = lean_string_push(x_30, x_31);
x_1 = x_32;
x_2 = x_20;
x_3 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__2;
x_4 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__2(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__2(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Sat_CNF_dimacs_go(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Sat_CNF_dimacs___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Std_Sat_CNF_dimacs___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("p cnf ", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Std_Sat_CNF_dimacs___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(" ", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Std_Sat_CNF_dimacs___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("\n", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_2 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__2;
x_3 = l_Std_Sat_CNF_dimacs___closed__1;
x_4 = l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__2(x_2, x_1, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_7, x_8);
lean_dec(x_7);
x_10 = l___private_Init_Data_Repr_0__Nat_reprFast(x_9);
x_11 = l_Std_Sat_CNF_dimacs___closed__2;
x_12 = lean_string_append(x_11, x_10);
lean_dec(x_10);
x_13 = l_Std_Sat_CNF_dimacs___closed__3;
x_14 = lean_string_append(x_12, x_13);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = l___private_Init_Data_Repr_0__Nat_reprFast(x_15);
x_17 = lean_string_append(x_14, x_16);
lean_dec(x_16);
x_18 = l_Std_Sat_CNF_dimacs___closed__4;
x_19 = lean_string_append(x_17, x_18);
x_20 = lean_string_append(x_19, x_5);
lean_dec(x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Std_Sat_CNF_dimacs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Sat_CNF_dimacs(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Std_Sat_CNF_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Sat_CNF_RelabelFin(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Sat_CNF_Dimacs(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Sat_CNF_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Sat_CNF_RelabelFin(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__1 = _init_l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__1();
lean_mark_persistent(l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__1);
l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__2 = _init_l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__2();
lean_mark_persistent(l_List_foldlM___at_Std_Sat_CNF_dimacs_go___spec__1___closed__2);
l_Std_Sat_CNF_dimacs___closed__1 = _init_l_Std_Sat_CNF_dimacs___closed__1();
lean_mark_persistent(l_Std_Sat_CNF_dimacs___closed__1);
l_Std_Sat_CNF_dimacs___closed__2 = _init_l_Std_Sat_CNF_dimacs___closed__2();
lean_mark_persistent(l_Std_Sat_CNF_dimacs___closed__2);
l_Std_Sat_CNF_dimacs___closed__3 = _init_l_Std_Sat_CNF_dimacs___closed__3();
lean_mark_persistent(l_Std_Sat_CNF_dimacs___closed__3);
l_Std_Sat_CNF_dimacs___closed__4 = _init_l_Std_Sat_CNF_dimacs___closed__4();
lean_mark_persistent(l_Std_Sat_CNF_dimacs___closed__4);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
