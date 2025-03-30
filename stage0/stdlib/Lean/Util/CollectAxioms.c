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
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_Lean_CollectAxioms_collect___spec__2(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_collectAxioms___rarg___lambda__1___closed__1;
lean_object* lean_task_get_own(lean_object*);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
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
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_task_get_own(x_12);
lean_inc(x_1);
x_14 = lean_environment_find(x_13, x_1);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_array_push(x_5, x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
case 1:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_20 = lean_ctor_get(x_16, 0);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Expr_getUsedConstants(x_22);
x_24 = lean_array_get_size(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_nat_dec_lt(x_25, x_24);
if (x_26 == 0)
{
lean_dec(x_24);
lean_dec(x_23);
x_27 = x_3;
goto block_38;
}
else
{
uint8_t x_39; 
x_39 = lean_nat_dec_le(x_24, x_24);
if (x_39 == 0)
{
lean_dec(x_24);
lean_dec(x_23);
x_27 = x_3;
goto block_38;
}
else
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = 0;
x_41 = lean_usize_of_nat(x_24);
lean_dec(x_24);
lean_inc(x_2);
x_42 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_23, x_40, x_41, x_10, x_2, x_3);
lean_dec(x_23);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_27 = x_43;
goto block_38;
}
}
block_38:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = l_Lean_Expr_getUsedConstants(x_28);
x_30 = lean_array_get_size(x_29);
x_31 = lean_nat_dec_lt(x_25, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_30, x_30);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_2);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_10);
lean_ctor_set(x_34, 1, x_27);
return x_34;
}
else
{
size_t x_35; size_t x_36; lean_object* x_37; 
x_35 = 0;
x_36 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_37 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_29, x_35, x_36, x_10, x_2, x_27);
lean_dec(x_29);
return x_37;
}
}
}
}
case 2:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_44 = lean_ctor_get(x_16, 0);
lean_inc(x_44);
lean_dec(x_16);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_45, 2);
lean_inc(x_46);
lean_dec(x_45);
x_47 = l_Lean_Expr_getUsedConstants(x_46);
x_48 = lean_array_get_size(x_47);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_nat_dec_lt(x_49, x_48);
if (x_50 == 0)
{
lean_dec(x_48);
lean_dec(x_47);
x_51 = x_3;
goto block_62;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_48, x_48);
if (x_63 == 0)
{
lean_dec(x_48);
lean_dec(x_47);
x_51 = x_3;
goto block_62;
}
else
{
size_t x_64; size_t x_65; lean_object* x_66; lean_object* x_67; 
x_64 = 0;
x_65 = lean_usize_of_nat(x_48);
lean_dec(x_48);
lean_inc(x_2);
x_66 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_47, x_64, x_65, x_10, x_2, x_3);
lean_dec(x_47);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_51 = x_67;
goto block_62;
}
}
block_62:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_44, 1);
lean_inc(x_52);
lean_dec(x_44);
x_53 = l_Lean_Expr_getUsedConstants(x_52);
x_54 = lean_array_get_size(x_53);
x_55 = lean_nat_dec_lt(x_49, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_2);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_10);
lean_ctor_set(x_56, 1, x_51);
return x_56;
}
else
{
uint8_t x_57; 
x_57 = lean_nat_dec_le(x_54, x_54);
if (x_57 == 0)
{
lean_object* x_58; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_2);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_10);
lean_ctor_set(x_58, 1, x_51);
return x_58;
}
else
{
size_t x_59; size_t x_60; lean_object* x_61; 
x_59 = 0;
x_60 = lean_usize_of_nat(x_54);
lean_dec(x_54);
x_61 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_53, x_59, x_60, x_10, x_2, x_51);
lean_dec(x_53);
return x_61;
}
}
}
}
case 3:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_68 = lean_ctor_get(x_16, 0);
lean_inc(x_68);
lean_dec(x_16);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_69, 2);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Lean_Expr_getUsedConstants(x_70);
x_72 = lean_array_get_size(x_71);
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_nat_dec_lt(x_73, x_72);
if (x_74 == 0)
{
lean_dec(x_72);
lean_dec(x_71);
x_75 = x_3;
goto block_86;
}
else
{
uint8_t x_87; 
x_87 = lean_nat_dec_le(x_72, x_72);
if (x_87 == 0)
{
lean_dec(x_72);
lean_dec(x_71);
x_75 = x_3;
goto block_86;
}
else
{
size_t x_88; size_t x_89; lean_object* x_90; lean_object* x_91; 
x_88 = 0;
x_89 = lean_usize_of_nat(x_72);
lean_dec(x_72);
lean_inc(x_2);
x_90 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_71, x_88, x_89, x_10, x_2, x_3);
lean_dec(x_71);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_75 = x_91;
goto block_86;
}
}
block_86:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_68, 1);
lean_inc(x_76);
lean_dec(x_68);
x_77 = l_Lean_Expr_getUsedConstants(x_76);
x_78 = lean_array_get_size(x_77);
x_79 = lean_nat_dec_lt(x_73, x_78);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_2);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_10);
lean_ctor_set(x_80, 1, x_75);
return x_80;
}
else
{
uint8_t x_81; 
x_81 = lean_nat_dec_le(x_78, x_78);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_2);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_10);
lean_ctor_set(x_82, 1, x_75);
return x_82;
}
else
{
size_t x_83; size_t x_84; lean_object* x_85; 
x_83 = 0;
x_84 = lean_usize_of_nat(x_78);
lean_dec(x_78);
x_85 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_77, x_83, x_84, x_10, x_2, x_75);
lean_dec(x_77);
return x_85;
}
}
}
}
case 4:
{
lean_object* x_92; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_10);
lean_ctor_set(x_92, 1, x_3);
return x_92;
}
case 5:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_93 = lean_ctor_get(x_16, 0);
lean_inc(x_93);
lean_dec(x_16);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_94, 2);
lean_inc(x_95);
lean_dec(x_94);
x_96 = l_Lean_Expr_getUsedConstants(x_95);
x_97 = lean_array_get_size(x_96);
x_98 = lean_unsigned_to_nat(0u);
x_99 = lean_nat_dec_lt(x_98, x_97);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
lean_dec(x_97);
lean_dec(x_96);
x_100 = lean_ctor_get(x_93, 4);
lean_inc(x_100);
lean_dec(x_93);
x_101 = l_List_forM___at_Lean_CollectAxioms_collect___spec__2(x_100, x_2, x_3);
return x_101;
}
else
{
uint8_t x_102; 
x_102 = lean_nat_dec_le(x_97, x_97);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_97);
lean_dec(x_96);
x_103 = lean_ctor_get(x_93, 4);
lean_inc(x_103);
lean_dec(x_93);
x_104 = l_List_forM___at_Lean_CollectAxioms_collect___spec__2(x_103, x_2, x_3);
return x_104;
}
else
{
size_t x_105; size_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_105 = 0;
x_106 = lean_usize_of_nat(x_97);
lean_dec(x_97);
lean_inc(x_2);
x_107 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_96, x_105, x_106, x_10, x_2, x_3);
lean_dec(x_96);
x_108 = lean_ctor_get(x_107, 1);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_ctor_get(x_93, 4);
lean_inc(x_109);
lean_dec(x_93);
x_110 = l_List_forM___at_Lean_CollectAxioms_collect___spec__2(x_109, x_2, x_108);
return x_110;
}
}
}
default: 
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_111 = lean_ctor_get(x_16, 0);
lean_inc(x_111);
lean_dec(x_16);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_ctor_get(x_112, 2);
lean_inc(x_113);
lean_dec(x_112);
x_114 = l_Lean_Expr_getUsedConstants(x_113);
x_115 = lean_array_get_size(x_114);
x_116 = lean_unsigned_to_nat(0u);
x_117 = lean_nat_dec_lt(x_116, x_115);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_2);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_10);
lean_ctor_set(x_118, 1, x_3);
return x_118;
}
else
{
uint8_t x_119; 
x_119 = lean_nat_dec_le(x_115, x_115);
if (x_119 == 0)
{
lean_object* x_120; 
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_2);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_10);
lean_ctor_set(x_120, 1, x_3);
return x_120;
}
else
{
size_t x_121; size_t x_122; lean_object* x_123; 
x_121 = 0;
x_122 = lean_usize_of_nat(x_115);
lean_dec(x_115);
x_123 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_114, x_121, x_122, x_10, x_2, x_3);
lean_dec(x_114);
return x_123;
}
}
}
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_3);
x_124 = lean_box(0);
lean_inc(x_1);
x_125 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_1, x_124);
lean_inc(x_5);
lean_inc(x_125);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_5);
x_127 = lean_ctor_get(x_2, 1);
lean_inc(x_127);
x_128 = lean_task_get_own(x_127);
lean_inc(x_1);
x_129 = lean_environment_find(x_128, x_1);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; 
lean_dec(x_125);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_124);
lean_ctor_set(x_130, 1, x_126);
return x_130;
}
else
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
lean_dec(x_129);
switch (lean_obj_tag(x_131)) {
case 0:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_dec(x_131);
lean_dec(x_126);
lean_dec(x_2);
x_132 = lean_array_push(x_5, x_1);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_125);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_124);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
case 1:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; 
lean_dec(x_125);
lean_dec(x_5);
lean_dec(x_1);
x_135 = lean_ctor_get(x_131, 0);
lean_inc(x_135);
lean_dec(x_131);
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_136, 2);
lean_inc(x_137);
lean_dec(x_136);
x_138 = l_Lean_Expr_getUsedConstants(x_137);
x_139 = lean_array_get_size(x_138);
x_140 = lean_unsigned_to_nat(0u);
x_141 = lean_nat_dec_lt(x_140, x_139);
if (x_141 == 0)
{
lean_dec(x_139);
lean_dec(x_138);
x_142 = x_126;
goto block_153;
}
else
{
uint8_t x_154; 
x_154 = lean_nat_dec_le(x_139, x_139);
if (x_154 == 0)
{
lean_dec(x_139);
lean_dec(x_138);
x_142 = x_126;
goto block_153;
}
else
{
size_t x_155; size_t x_156; lean_object* x_157; lean_object* x_158; 
x_155 = 0;
x_156 = lean_usize_of_nat(x_139);
lean_dec(x_139);
lean_inc(x_2);
x_157 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_138, x_155, x_156, x_124, x_2, x_126);
lean_dec(x_138);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_142 = x_158;
goto block_153;
}
}
block_153:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_143 = lean_ctor_get(x_135, 1);
lean_inc(x_143);
lean_dec(x_135);
x_144 = l_Lean_Expr_getUsedConstants(x_143);
x_145 = lean_array_get_size(x_144);
x_146 = lean_nat_dec_lt(x_140, x_145);
if (x_146 == 0)
{
lean_object* x_147; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_2);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_124);
lean_ctor_set(x_147, 1, x_142);
return x_147;
}
else
{
uint8_t x_148; 
x_148 = lean_nat_dec_le(x_145, x_145);
if (x_148 == 0)
{
lean_object* x_149; 
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_2);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_124);
lean_ctor_set(x_149, 1, x_142);
return x_149;
}
else
{
size_t x_150; size_t x_151; lean_object* x_152; 
x_150 = 0;
x_151 = lean_usize_of_nat(x_145);
lean_dec(x_145);
x_152 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_144, x_150, x_151, x_124, x_2, x_142);
lean_dec(x_144);
return x_152;
}
}
}
}
case 2:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; 
lean_dec(x_125);
lean_dec(x_5);
lean_dec(x_1);
x_159 = lean_ctor_get(x_131, 0);
lean_inc(x_159);
lean_dec(x_131);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_160, 2);
lean_inc(x_161);
lean_dec(x_160);
x_162 = l_Lean_Expr_getUsedConstants(x_161);
x_163 = lean_array_get_size(x_162);
x_164 = lean_unsigned_to_nat(0u);
x_165 = lean_nat_dec_lt(x_164, x_163);
if (x_165 == 0)
{
lean_dec(x_163);
lean_dec(x_162);
x_166 = x_126;
goto block_177;
}
else
{
uint8_t x_178; 
x_178 = lean_nat_dec_le(x_163, x_163);
if (x_178 == 0)
{
lean_dec(x_163);
lean_dec(x_162);
x_166 = x_126;
goto block_177;
}
else
{
size_t x_179; size_t x_180; lean_object* x_181; lean_object* x_182; 
x_179 = 0;
x_180 = lean_usize_of_nat(x_163);
lean_dec(x_163);
lean_inc(x_2);
x_181 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_162, x_179, x_180, x_124, x_2, x_126);
lean_dec(x_162);
x_182 = lean_ctor_get(x_181, 1);
lean_inc(x_182);
lean_dec(x_181);
x_166 = x_182;
goto block_177;
}
}
block_177:
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_167 = lean_ctor_get(x_159, 1);
lean_inc(x_167);
lean_dec(x_159);
x_168 = l_Lean_Expr_getUsedConstants(x_167);
x_169 = lean_array_get_size(x_168);
x_170 = lean_nat_dec_lt(x_164, x_169);
if (x_170 == 0)
{
lean_object* x_171; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_2);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_124);
lean_ctor_set(x_171, 1, x_166);
return x_171;
}
else
{
uint8_t x_172; 
x_172 = lean_nat_dec_le(x_169, x_169);
if (x_172 == 0)
{
lean_object* x_173; 
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_2);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_124);
lean_ctor_set(x_173, 1, x_166);
return x_173;
}
else
{
size_t x_174; size_t x_175; lean_object* x_176; 
x_174 = 0;
x_175 = lean_usize_of_nat(x_169);
lean_dec(x_169);
x_176 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_168, x_174, x_175, x_124, x_2, x_166);
lean_dec(x_168);
return x_176;
}
}
}
}
case 3:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; lean_object* x_190; 
lean_dec(x_125);
lean_dec(x_5);
lean_dec(x_1);
x_183 = lean_ctor_get(x_131, 0);
lean_inc(x_183);
lean_dec(x_131);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_184, 2);
lean_inc(x_185);
lean_dec(x_184);
x_186 = l_Lean_Expr_getUsedConstants(x_185);
x_187 = lean_array_get_size(x_186);
x_188 = lean_unsigned_to_nat(0u);
x_189 = lean_nat_dec_lt(x_188, x_187);
if (x_189 == 0)
{
lean_dec(x_187);
lean_dec(x_186);
x_190 = x_126;
goto block_201;
}
else
{
uint8_t x_202; 
x_202 = lean_nat_dec_le(x_187, x_187);
if (x_202 == 0)
{
lean_dec(x_187);
lean_dec(x_186);
x_190 = x_126;
goto block_201;
}
else
{
size_t x_203; size_t x_204; lean_object* x_205; lean_object* x_206; 
x_203 = 0;
x_204 = lean_usize_of_nat(x_187);
lean_dec(x_187);
lean_inc(x_2);
x_205 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_186, x_203, x_204, x_124, x_2, x_126);
lean_dec(x_186);
x_206 = lean_ctor_get(x_205, 1);
lean_inc(x_206);
lean_dec(x_205);
x_190 = x_206;
goto block_201;
}
}
block_201:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_191 = lean_ctor_get(x_183, 1);
lean_inc(x_191);
lean_dec(x_183);
x_192 = l_Lean_Expr_getUsedConstants(x_191);
x_193 = lean_array_get_size(x_192);
x_194 = lean_nat_dec_lt(x_188, x_193);
if (x_194 == 0)
{
lean_object* x_195; 
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_2);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_124);
lean_ctor_set(x_195, 1, x_190);
return x_195;
}
else
{
uint8_t x_196; 
x_196 = lean_nat_dec_le(x_193, x_193);
if (x_196 == 0)
{
lean_object* x_197; 
lean_dec(x_193);
lean_dec(x_192);
lean_dec(x_2);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_124);
lean_ctor_set(x_197, 1, x_190);
return x_197;
}
else
{
size_t x_198; size_t x_199; lean_object* x_200; 
x_198 = 0;
x_199 = lean_usize_of_nat(x_193);
lean_dec(x_193);
x_200 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_192, x_198, x_199, x_124, x_2, x_190);
lean_dec(x_192);
return x_200;
}
}
}
}
case 4:
{
lean_object* x_207; 
lean_dec(x_131);
lean_dec(x_125);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_124);
lean_ctor_set(x_207, 1, x_126);
return x_207;
}
case 5:
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
lean_dec(x_125);
lean_dec(x_5);
lean_dec(x_1);
x_208 = lean_ctor_get(x_131, 0);
lean_inc(x_208);
lean_dec(x_131);
x_209 = lean_ctor_get(x_208, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_209, 2);
lean_inc(x_210);
lean_dec(x_209);
x_211 = l_Lean_Expr_getUsedConstants(x_210);
x_212 = lean_array_get_size(x_211);
x_213 = lean_unsigned_to_nat(0u);
x_214 = lean_nat_dec_lt(x_213, x_212);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; 
lean_dec(x_212);
lean_dec(x_211);
x_215 = lean_ctor_get(x_208, 4);
lean_inc(x_215);
lean_dec(x_208);
x_216 = l_List_forM___at_Lean_CollectAxioms_collect___spec__2(x_215, x_2, x_126);
return x_216;
}
else
{
uint8_t x_217; 
x_217 = lean_nat_dec_le(x_212, x_212);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; 
lean_dec(x_212);
lean_dec(x_211);
x_218 = lean_ctor_get(x_208, 4);
lean_inc(x_218);
lean_dec(x_208);
x_219 = l_List_forM___at_Lean_CollectAxioms_collect___spec__2(x_218, x_2, x_126);
return x_219;
}
else
{
size_t x_220; size_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_220 = 0;
x_221 = lean_usize_of_nat(x_212);
lean_dec(x_212);
lean_inc(x_2);
x_222 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_211, x_220, x_221, x_124, x_2, x_126);
lean_dec(x_211);
x_223 = lean_ctor_get(x_222, 1);
lean_inc(x_223);
lean_dec(x_222);
x_224 = lean_ctor_get(x_208, 4);
lean_inc(x_224);
lean_dec(x_208);
x_225 = l_List_forM___at_Lean_CollectAxioms_collect___spec__2(x_224, x_2, x_223);
return x_225;
}
}
}
default: 
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
lean_dec(x_125);
lean_dec(x_5);
lean_dec(x_1);
x_226 = lean_ctor_get(x_131, 0);
lean_inc(x_226);
lean_dec(x_131);
x_227 = lean_ctor_get(x_226, 0);
lean_inc(x_227);
lean_dec(x_226);
x_228 = lean_ctor_get(x_227, 2);
lean_inc(x_228);
lean_dec(x_227);
x_229 = l_Lean_Expr_getUsedConstants(x_228);
x_230 = lean_array_get_size(x_229);
x_231 = lean_unsigned_to_nat(0u);
x_232 = lean_nat_dec_lt(x_231, x_230);
if (x_232 == 0)
{
lean_object* x_233; 
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_2);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_124);
lean_ctor_set(x_233, 1, x_126);
return x_233;
}
else
{
uint8_t x_234; 
x_234 = lean_nat_dec_le(x_230, x_230);
if (x_234 == 0)
{
lean_object* x_235; 
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_2);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_124);
lean_ctor_set(x_235, 1, x_126);
return x_235;
}
else
{
size_t x_236; size_t x_237; lean_object* x_238; 
x_236 = 0;
x_237 = lean_usize_of_nat(x_230);
lean_dec(x_230);
x_238 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_229, x_236, x_237, x_124, x_2, x_126);
lean_dec(x_229);
return x_238;
}
}
}
}
}
}
}
else
{
lean_object* x_239; lean_object* x_240; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_239 = lean_box(0);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_3);
return x_240;
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
