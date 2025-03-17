// Lean compiler output
// Module: Lean.Util.CollectAxioms
// Imports: Lean.MonadEnv Lean.Util.FoldConsts
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
LEAN_EXPORT lean_object* l_Lean_CollectAxioms_collect(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_CollectAxioms_collect___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_collectAxioms___rarg___lambda__1___closed__1;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
static lean_object* l_Lean_collectAxioms___rarg___lambda__1___closed__2;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_collectAxioms___rarg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectAxioms___rarg___lambda__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_collectAxioms(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
lean_dec(x_4);
x_8 = lean_array_uget(x_1, x_2);
lean_inc(x_5);
x_9 = l_Lean_CollectAxioms_collect(x_8, x_5, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = 1;
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_15; 
lean_dec(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at_Lean_CollectAxioms_collect___spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
lean_inc(x_2);
x_8 = l_Lean_CollectAxioms_collect(x_6, x_2, x_3);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_1 = x_7;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_CollectAxioms_collect(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = l_Lean_NameSet_contains(x_4, x_1);
if (x_6 == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_3, 1);
lean_dec(x_8);
x_9 = lean_ctor_get(x_3, 0);
lean_dec(x_9);
x_10 = lean_box(0);
lean_inc(x_1);
x_11 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_1, x_10);
lean_inc(x_5);
lean_inc(x_11);
lean_ctor_set(x_3, 0, x_11);
x_12 = 0;
lean_inc(x_1);
lean_inc(x_2);
x_13 = l_Lean_Environment_find_x3f(x_2, x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_array_push(x_5, x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_11);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
case 1:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Expr_getUsedConstants(x_21);
x_23 = lean_array_get_size(x_22);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_nat_dec_lt(x_24, x_23);
if (x_25 == 0)
{
lean_dec(x_23);
lean_dec(x_22);
x_26 = x_3;
goto block_37;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_23, x_23);
if (x_38 == 0)
{
lean_dec(x_23);
lean_dec(x_22);
x_26 = x_3;
goto block_37;
}
else
{
size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; 
x_39 = 0;
x_40 = lean_usize_of_nat(x_23);
lean_dec(x_23);
lean_inc(x_2);
x_41 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_22, x_39, x_40, x_10, x_2, x_3);
lean_dec(x_22);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_26 = x_42;
goto block_37;
}
}
block_37:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = l_Lean_Expr_getUsedConstants(x_27);
x_29 = lean_array_get_size(x_28);
x_30 = lean_nat_dec_lt(x_24, x_29);
if (x_30 == 0)
{
lean_object* x_31; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_10);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
else
{
uint8_t x_32; 
x_32 = lean_nat_dec_le(x_29, x_29);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
x_34 = 0;
x_35 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_36 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_28, x_34, x_35, x_10, x_2, x_26);
lean_dec(x_28);
return x_36;
}
}
}
}
case 2:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_43 = lean_ctor_get(x_15, 0);
lean_inc(x_43);
lean_dec(x_15);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 2);
lean_inc(x_45);
lean_dec(x_44);
x_46 = l_Lean_Expr_getUsedConstants(x_45);
x_47 = lean_array_get_size(x_46);
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_nat_dec_lt(x_48, x_47);
if (x_49 == 0)
{
lean_dec(x_47);
lean_dec(x_46);
x_50 = x_3;
goto block_61;
}
else
{
uint8_t x_62; 
x_62 = lean_nat_dec_le(x_47, x_47);
if (x_62 == 0)
{
lean_dec(x_47);
lean_dec(x_46);
x_50 = x_3;
goto block_61;
}
else
{
size_t x_63; size_t x_64; lean_object* x_65; lean_object* x_66; 
x_63 = 0;
x_64 = lean_usize_of_nat(x_47);
lean_dec(x_47);
lean_inc(x_2);
x_65 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_46, x_63, x_64, x_10, x_2, x_3);
lean_dec(x_46);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_50 = x_66;
goto block_61;
}
}
block_61:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
lean_dec(x_43);
x_52 = l_Lean_Expr_getUsedConstants(x_51);
x_53 = lean_array_get_size(x_52);
x_54 = lean_nat_dec_lt(x_48, x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_2);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_10);
lean_ctor_set(x_55, 1, x_50);
return x_55;
}
else
{
uint8_t x_56; 
x_56 = lean_nat_dec_le(x_53, x_53);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_2);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_10);
lean_ctor_set(x_57, 1, x_50);
return x_57;
}
else
{
size_t x_58; size_t x_59; lean_object* x_60; 
x_58 = 0;
x_59 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_60 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_52, x_58, x_59, x_10, x_2, x_50);
lean_dec(x_52);
return x_60;
}
}
}
}
case 3:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_67 = lean_ctor_get(x_15, 0);
lean_inc(x_67);
lean_dec(x_15);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_68, 2);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Lean_Expr_getUsedConstants(x_69);
x_71 = lean_array_get_size(x_70);
x_72 = lean_unsigned_to_nat(0u);
x_73 = lean_nat_dec_lt(x_72, x_71);
if (x_73 == 0)
{
lean_dec(x_71);
lean_dec(x_70);
x_74 = x_3;
goto block_85;
}
else
{
uint8_t x_86; 
x_86 = lean_nat_dec_le(x_71, x_71);
if (x_86 == 0)
{
lean_dec(x_71);
lean_dec(x_70);
x_74 = x_3;
goto block_85;
}
else
{
size_t x_87; size_t x_88; lean_object* x_89; lean_object* x_90; 
x_87 = 0;
x_88 = lean_usize_of_nat(x_71);
lean_dec(x_71);
lean_inc(x_2);
x_89 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_70, x_87, x_88, x_10, x_2, x_3);
lean_dec(x_70);
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
lean_dec(x_89);
x_74 = x_90;
goto block_85;
}
}
block_85:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_67, 1);
lean_inc(x_75);
lean_dec(x_67);
x_76 = l_Lean_Expr_getUsedConstants(x_75);
x_77 = lean_array_get_size(x_76);
x_78 = lean_nat_dec_lt(x_72, x_77);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_2);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_10);
lean_ctor_set(x_79, 1, x_74);
return x_79;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_77, x_77);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_2);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_10);
lean_ctor_set(x_81, 1, x_74);
return x_81;
}
else
{
size_t x_82; size_t x_83; lean_object* x_84; 
x_82 = 0;
x_83 = lean_usize_of_nat(x_77);
lean_dec(x_77);
x_84 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_76, x_82, x_83, x_10, x_2, x_74);
lean_dec(x_76);
return x_84;
}
}
}
}
case 4:
{
lean_object* x_91; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_10);
lean_ctor_set(x_91, 1, x_3);
return x_91;
}
case 5:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_92 = lean_ctor_get(x_15, 0);
lean_inc(x_92);
lean_dec(x_15);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_93, 2);
lean_inc(x_94);
lean_dec(x_93);
x_95 = l_Lean_Expr_getUsedConstants(x_94);
x_96 = lean_array_get_size(x_95);
x_97 = lean_unsigned_to_nat(0u);
x_98 = lean_nat_dec_lt(x_97, x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_96);
lean_dec(x_95);
x_99 = lean_ctor_get(x_92, 4);
lean_inc(x_99);
lean_dec(x_92);
x_100 = l_List_forM___at_Lean_CollectAxioms_collect___spec__2(x_99, x_2, x_3);
return x_100;
}
else
{
uint8_t x_101; 
x_101 = lean_nat_dec_le(x_96, x_96);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_96);
lean_dec(x_95);
x_102 = lean_ctor_get(x_92, 4);
lean_inc(x_102);
lean_dec(x_92);
x_103 = l_List_forM___at_Lean_CollectAxioms_collect___spec__2(x_102, x_2, x_3);
return x_103;
}
else
{
size_t x_104; size_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_104 = 0;
x_105 = lean_usize_of_nat(x_96);
lean_dec(x_96);
lean_inc(x_2);
x_106 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_95, x_104, x_105, x_10, x_2, x_3);
lean_dec(x_95);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_108 = lean_ctor_get(x_92, 4);
lean_inc(x_108);
lean_dec(x_92);
x_109 = l_List_forM___at_Lean_CollectAxioms_collect___spec__2(x_108, x_2, x_107);
return x_109;
}
}
}
default: 
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_110 = lean_ctor_get(x_15, 0);
lean_inc(x_110);
lean_dec(x_15);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
lean_dec(x_110);
x_112 = lean_ctor_get(x_111, 2);
lean_inc(x_112);
lean_dec(x_111);
x_113 = l_Lean_Expr_getUsedConstants(x_112);
x_114 = lean_array_get_size(x_113);
x_115 = lean_unsigned_to_nat(0u);
x_116 = lean_nat_dec_lt(x_115, x_114);
if (x_116 == 0)
{
lean_object* x_117; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_2);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_10);
lean_ctor_set(x_117, 1, x_3);
return x_117;
}
else
{
uint8_t x_118; 
x_118 = lean_nat_dec_le(x_114, x_114);
if (x_118 == 0)
{
lean_object* x_119; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_2);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_10);
lean_ctor_set(x_119, 1, x_3);
return x_119;
}
else
{
size_t x_120; size_t x_121; lean_object* x_122; 
x_120 = 0;
x_121 = lean_usize_of_nat(x_114);
lean_dec(x_114);
x_122 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_113, x_120, x_121, x_10, x_2, x_3);
lean_dec(x_113);
return x_122;
}
}
}
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; 
lean_dec(x_3);
x_123 = lean_box(0);
lean_inc(x_1);
x_124 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_1, x_123);
lean_inc(x_5);
lean_inc(x_124);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_5);
x_126 = 0;
lean_inc(x_1);
lean_inc(x_2);
x_127 = l_Lean_Environment_find_x3f(x_2, x_1, x_126);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
lean_dec(x_124);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_123);
lean_ctor_set(x_128, 1, x_125);
return x_128;
}
else
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
lean_dec(x_127);
switch (lean_obj_tag(x_129)) {
case 0:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_129);
lean_dec(x_125);
lean_dec(x_2);
x_130 = lean_array_push(x_5, x_1);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_124);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_123);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
case 1:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; 
lean_dec(x_124);
lean_dec(x_5);
lean_dec(x_1);
x_133 = lean_ctor_get(x_129, 0);
lean_inc(x_133);
lean_dec(x_129);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_134, 2);
lean_inc(x_135);
lean_dec(x_134);
x_136 = l_Lean_Expr_getUsedConstants(x_135);
x_137 = lean_array_get_size(x_136);
x_138 = lean_unsigned_to_nat(0u);
x_139 = lean_nat_dec_lt(x_138, x_137);
if (x_139 == 0)
{
lean_dec(x_137);
lean_dec(x_136);
x_140 = x_125;
goto block_151;
}
else
{
uint8_t x_152; 
x_152 = lean_nat_dec_le(x_137, x_137);
if (x_152 == 0)
{
lean_dec(x_137);
lean_dec(x_136);
x_140 = x_125;
goto block_151;
}
else
{
size_t x_153; size_t x_154; lean_object* x_155; lean_object* x_156; 
x_153 = 0;
x_154 = lean_usize_of_nat(x_137);
lean_dec(x_137);
lean_inc(x_2);
x_155 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_136, x_153, x_154, x_123, x_2, x_125);
lean_dec(x_136);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_140 = x_156;
goto block_151;
}
}
block_151:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_141 = lean_ctor_get(x_133, 1);
lean_inc(x_141);
lean_dec(x_133);
x_142 = l_Lean_Expr_getUsedConstants(x_141);
x_143 = lean_array_get_size(x_142);
x_144 = lean_nat_dec_lt(x_138, x_143);
if (x_144 == 0)
{
lean_object* x_145; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_2);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_123);
lean_ctor_set(x_145, 1, x_140);
return x_145;
}
else
{
uint8_t x_146; 
x_146 = lean_nat_dec_le(x_143, x_143);
if (x_146 == 0)
{
lean_object* x_147; 
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_2);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_123);
lean_ctor_set(x_147, 1, x_140);
return x_147;
}
else
{
size_t x_148; size_t x_149; lean_object* x_150; 
x_148 = 0;
x_149 = lean_usize_of_nat(x_143);
lean_dec(x_143);
x_150 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_142, x_148, x_149, x_123, x_2, x_140);
lean_dec(x_142);
return x_150;
}
}
}
}
case 2:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; 
lean_dec(x_124);
lean_dec(x_5);
lean_dec(x_1);
x_157 = lean_ctor_get(x_129, 0);
lean_inc(x_157);
lean_dec(x_129);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_158, 2);
lean_inc(x_159);
lean_dec(x_158);
x_160 = l_Lean_Expr_getUsedConstants(x_159);
x_161 = lean_array_get_size(x_160);
x_162 = lean_unsigned_to_nat(0u);
x_163 = lean_nat_dec_lt(x_162, x_161);
if (x_163 == 0)
{
lean_dec(x_161);
lean_dec(x_160);
x_164 = x_125;
goto block_175;
}
else
{
uint8_t x_176; 
x_176 = lean_nat_dec_le(x_161, x_161);
if (x_176 == 0)
{
lean_dec(x_161);
lean_dec(x_160);
x_164 = x_125;
goto block_175;
}
else
{
size_t x_177; size_t x_178; lean_object* x_179; lean_object* x_180; 
x_177 = 0;
x_178 = lean_usize_of_nat(x_161);
lean_dec(x_161);
lean_inc(x_2);
x_179 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_160, x_177, x_178, x_123, x_2, x_125);
lean_dec(x_160);
x_180 = lean_ctor_get(x_179, 1);
lean_inc(x_180);
lean_dec(x_179);
x_164 = x_180;
goto block_175;
}
}
block_175:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_165 = lean_ctor_get(x_157, 1);
lean_inc(x_165);
lean_dec(x_157);
x_166 = l_Lean_Expr_getUsedConstants(x_165);
x_167 = lean_array_get_size(x_166);
x_168 = lean_nat_dec_lt(x_162, x_167);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_2);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_123);
lean_ctor_set(x_169, 1, x_164);
return x_169;
}
else
{
uint8_t x_170; 
x_170 = lean_nat_dec_le(x_167, x_167);
if (x_170 == 0)
{
lean_object* x_171; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_2);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_123);
lean_ctor_set(x_171, 1, x_164);
return x_171;
}
else
{
size_t x_172; size_t x_173; lean_object* x_174; 
x_172 = 0;
x_173 = lean_usize_of_nat(x_167);
lean_dec(x_167);
x_174 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_166, x_172, x_173, x_123, x_2, x_164);
lean_dec(x_166);
return x_174;
}
}
}
}
case 3:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; lean_object* x_188; 
lean_dec(x_124);
lean_dec(x_5);
lean_dec(x_1);
x_181 = lean_ctor_get(x_129, 0);
lean_inc(x_181);
lean_dec(x_129);
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_182, 2);
lean_inc(x_183);
lean_dec(x_182);
x_184 = l_Lean_Expr_getUsedConstants(x_183);
x_185 = lean_array_get_size(x_184);
x_186 = lean_unsigned_to_nat(0u);
x_187 = lean_nat_dec_lt(x_186, x_185);
if (x_187 == 0)
{
lean_dec(x_185);
lean_dec(x_184);
x_188 = x_125;
goto block_199;
}
else
{
uint8_t x_200; 
x_200 = lean_nat_dec_le(x_185, x_185);
if (x_200 == 0)
{
lean_dec(x_185);
lean_dec(x_184);
x_188 = x_125;
goto block_199;
}
else
{
size_t x_201; size_t x_202; lean_object* x_203; lean_object* x_204; 
x_201 = 0;
x_202 = lean_usize_of_nat(x_185);
lean_dec(x_185);
lean_inc(x_2);
x_203 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_184, x_201, x_202, x_123, x_2, x_125);
lean_dec(x_184);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec(x_203);
x_188 = x_204;
goto block_199;
}
}
block_199:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_189 = lean_ctor_get(x_181, 1);
lean_inc(x_189);
lean_dec(x_181);
x_190 = l_Lean_Expr_getUsedConstants(x_189);
x_191 = lean_array_get_size(x_190);
x_192 = lean_nat_dec_lt(x_186, x_191);
if (x_192 == 0)
{
lean_object* x_193; 
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_2);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_123);
lean_ctor_set(x_193, 1, x_188);
return x_193;
}
else
{
uint8_t x_194; 
x_194 = lean_nat_dec_le(x_191, x_191);
if (x_194 == 0)
{
lean_object* x_195; 
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_2);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_123);
lean_ctor_set(x_195, 1, x_188);
return x_195;
}
else
{
size_t x_196; size_t x_197; lean_object* x_198; 
x_196 = 0;
x_197 = lean_usize_of_nat(x_191);
lean_dec(x_191);
x_198 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_190, x_196, x_197, x_123, x_2, x_188);
lean_dec(x_190);
return x_198;
}
}
}
}
case 4:
{
lean_object* x_205; 
lean_dec(x_129);
lean_dec(x_124);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_205 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_205, 0, x_123);
lean_ctor_set(x_205, 1, x_125);
return x_205;
}
case 5:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
lean_dec(x_124);
lean_dec(x_5);
lean_dec(x_1);
x_206 = lean_ctor_get(x_129, 0);
lean_inc(x_206);
lean_dec(x_129);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_207, 2);
lean_inc(x_208);
lean_dec(x_207);
x_209 = l_Lean_Expr_getUsedConstants(x_208);
x_210 = lean_array_get_size(x_209);
x_211 = lean_unsigned_to_nat(0u);
x_212 = lean_nat_dec_lt(x_211, x_210);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_210);
lean_dec(x_209);
x_213 = lean_ctor_get(x_206, 4);
lean_inc(x_213);
lean_dec(x_206);
x_214 = l_List_forM___at_Lean_CollectAxioms_collect___spec__2(x_213, x_2, x_125);
return x_214;
}
else
{
uint8_t x_215; 
x_215 = lean_nat_dec_le(x_210, x_210);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_210);
lean_dec(x_209);
x_216 = lean_ctor_get(x_206, 4);
lean_inc(x_216);
lean_dec(x_206);
x_217 = l_List_forM___at_Lean_CollectAxioms_collect___spec__2(x_216, x_2, x_125);
return x_217;
}
else
{
size_t x_218; size_t x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_218 = 0;
x_219 = lean_usize_of_nat(x_210);
lean_dec(x_210);
lean_inc(x_2);
x_220 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_209, x_218, x_219, x_123, x_2, x_125);
lean_dec(x_209);
x_221 = lean_ctor_get(x_220, 1);
lean_inc(x_221);
lean_dec(x_220);
x_222 = lean_ctor_get(x_206, 4);
lean_inc(x_222);
lean_dec(x_206);
x_223 = l_List_forM___at_Lean_CollectAxioms_collect___spec__2(x_222, x_2, x_221);
return x_223;
}
}
}
default: 
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; 
lean_dec(x_124);
lean_dec(x_5);
lean_dec(x_1);
x_224 = lean_ctor_get(x_129, 0);
lean_inc(x_224);
lean_dec(x_129);
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
lean_dec(x_224);
x_226 = lean_ctor_get(x_225, 2);
lean_inc(x_226);
lean_dec(x_225);
x_227 = l_Lean_Expr_getUsedConstants(x_226);
x_228 = lean_array_get_size(x_227);
x_229 = lean_unsigned_to_nat(0u);
x_230 = lean_nat_dec_lt(x_229, x_228);
if (x_230 == 0)
{
lean_object* x_231; 
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_2);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_123);
lean_ctor_set(x_231, 1, x_125);
return x_231;
}
else
{
uint8_t x_232; 
x_232 = lean_nat_dec_le(x_228, x_228);
if (x_232 == 0)
{
lean_object* x_233; 
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_2);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_123);
lean_ctor_set(x_233, 1, x_125);
return x_233;
}
else
{
size_t x_234; size_t x_235; lean_object* x_236; 
x_234 = 0;
x_235 = lean_usize_of_nat(x_228);
lean_dec(x_228);
x_236 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_227, x_234, x_235, x_123, x_2, x_125);
lean_dec(x_227);
return x_236;
}
}
}
}
}
}
}
else
{
lean_object* x_237; lean_object* x_238; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_237 = lean_box(0);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_3);
return x_238;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_1);
return x_9;
}
}
static lean_object* _init_l_Lean_collectAxioms___rarg___lambda__1___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_array_mk(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_collectAxioms___rarg___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_NameSet_empty;
x_2 = l_Lean_collectAxioms___rarg___lambda__1___closed__1;
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms___rarg___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = l_Lean_collectAxioms___rarg___lambda__1___closed__2;
x_5 = l_Lean_CollectAxioms_collect(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_apply_2(x_8, lean_box(0), x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_alloc_closure((void*)(l_Lean_collectAxioms___rarg___lambda__1), 3, 2);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_1);
x_7 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_collectAxioms(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lean_collectAxioms___rarg), 3, 0);
return x_2;
}
}
lean_object* initialize_Lean_MonadEnv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Util_CollectAxioms(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_MonadEnv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FoldConsts(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_collectAxioms___rarg___lambda__1___closed__1 = _init_l_Lean_collectAxioms___rarg___lambda__1___closed__1();
lean_mark_persistent(l_Lean_collectAxioms___rarg___lambda__1___closed__1);
l_Lean_collectAxioms___rarg___lambda__1___closed__2 = _init_l_Lean_collectAxioms___rarg___lambda__1___closed__2();
lean_mark_persistent(l_Lean_collectAxioms___rarg___lambda__1___closed__2);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
