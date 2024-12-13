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
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*);
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
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
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
lean_inc(x_2);
x_12 = l_Lean_Environment_find_x3f(x_2, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_array_push(x_5, x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Expr_getUsedConstants(x_20);
x_22 = lean_array_get_size(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_lt(x_23, x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
x_25 = x_3;
goto block_36;
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_le(x_22, x_22);
if (x_37 == 0)
{
lean_dec(x_22);
lean_dec(x_21);
x_25 = x_3;
goto block_36;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_38 = 0;
x_39 = lean_usize_of_nat(x_22);
lean_dec(x_22);
lean_inc(x_2);
x_40 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_21, x_38, x_39, x_10, x_2, x_3);
lean_dec(x_21);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_25 = x_41;
goto block_36;
}
}
block_36:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = l_Lean_Expr_getUsedConstants(x_26);
x_28 = lean_array_get_size(x_27);
x_29 = lean_nat_dec_lt(x_23, x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_2);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_10);
lean_ctor_set(x_30, 1, x_25);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_28, x_28);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
x_33 = 0;
x_34 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_35 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_27, x_33, x_34, x_10, x_2, x_25);
lean_dec(x_27);
return x_35;
}
}
}
}
case 2:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_42 = lean_ctor_get(x_14, 0);
lean_inc(x_42);
lean_dec(x_14);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
lean_dec(x_43);
x_45 = l_Lean_Expr_getUsedConstants(x_44);
x_46 = lean_array_get_size(x_45);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_nat_dec_lt(x_47, x_46);
if (x_48 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
x_49 = x_3;
goto block_60;
}
else
{
uint8_t x_61; 
x_61 = lean_nat_dec_le(x_46, x_46);
if (x_61 == 0)
{
lean_dec(x_46);
lean_dec(x_45);
x_49 = x_3;
goto block_60;
}
else
{
size_t x_62; size_t x_63; lean_object* x_64; lean_object* x_65; 
x_62 = 0;
x_63 = lean_usize_of_nat(x_46);
lean_dec(x_46);
lean_inc(x_2);
x_64 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_45, x_62, x_63, x_10, x_2, x_3);
lean_dec(x_45);
x_65 = lean_ctor_get(x_64, 1);
lean_inc(x_65);
lean_dec(x_64);
x_49 = x_65;
goto block_60;
}
}
block_60:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
lean_dec(x_42);
x_51 = l_Lean_Expr_getUsedConstants(x_50);
x_52 = lean_array_get_size(x_51);
x_53 = lean_nat_dec_lt(x_47, x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_2);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_10);
lean_ctor_set(x_54, 1, x_49);
return x_54;
}
else
{
uint8_t x_55; 
x_55 = lean_nat_dec_le(x_52, x_52);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_2);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_10);
lean_ctor_set(x_56, 1, x_49);
return x_56;
}
else
{
size_t x_57; size_t x_58; lean_object* x_59; 
x_57 = 0;
x_58 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_59 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_51, x_57, x_58, x_10, x_2, x_49);
lean_dec(x_51);
return x_59;
}
}
}
}
case 3:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_66 = lean_ctor_get(x_14, 0);
lean_inc(x_66);
lean_dec(x_14);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 2);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Lean_Expr_getUsedConstants(x_68);
x_70 = lean_array_get_size(x_69);
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_dec_lt(x_71, x_70);
if (x_72 == 0)
{
lean_dec(x_70);
lean_dec(x_69);
x_73 = x_3;
goto block_84;
}
else
{
uint8_t x_85; 
x_85 = lean_nat_dec_le(x_70, x_70);
if (x_85 == 0)
{
lean_dec(x_70);
lean_dec(x_69);
x_73 = x_3;
goto block_84;
}
else
{
size_t x_86; size_t x_87; lean_object* x_88; lean_object* x_89; 
x_86 = 0;
x_87 = lean_usize_of_nat(x_70);
lean_dec(x_70);
lean_inc(x_2);
x_88 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_69, x_86, x_87, x_10, x_2, x_3);
lean_dec(x_69);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_73 = x_89;
goto block_84;
}
}
block_84:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_ctor_get(x_66, 1);
lean_inc(x_74);
lean_dec(x_66);
x_75 = l_Lean_Expr_getUsedConstants(x_74);
x_76 = lean_array_get_size(x_75);
x_77 = lean_nat_dec_lt(x_71, x_76);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_2);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_10);
lean_ctor_set(x_78, 1, x_73);
return x_78;
}
else
{
uint8_t x_79; 
x_79 = lean_nat_dec_le(x_76, x_76);
if (x_79 == 0)
{
lean_object* x_80; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_2);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_10);
lean_ctor_set(x_80, 1, x_73);
return x_80;
}
else
{
size_t x_81; size_t x_82; lean_object* x_83; 
x_81 = 0;
x_82 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_83 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_75, x_81, x_82, x_10, x_2, x_73);
lean_dec(x_75);
return x_83;
}
}
}
}
case 4:
{
lean_object* x_90; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_10);
lean_ctor_set(x_90, 1, x_3);
return x_90;
}
case 5:
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_91 = lean_ctor_get(x_14, 0);
lean_inc(x_91);
lean_dec(x_14);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 2);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l_Lean_Expr_getUsedConstants(x_93);
x_95 = lean_array_get_size(x_94);
x_96 = lean_unsigned_to_nat(0u);
x_97 = lean_nat_dec_lt(x_96, x_95);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_95);
lean_dec(x_94);
x_98 = lean_ctor_get(x_91, 4);
lean_inc(x_98);
lean_dec(x_91);
x_99 = l_List_forM___at_Lean_CollectAxioms_collect___spec__2(x_98, x_2, x_3);
return x_99;
}
else
{
uint8_t x_100; 
x_100 = lean_nat_dec_le(x_95, x_95);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
lean_dec(x_95);
lean_dec(x_94);
x_101 = lean_ctor_get(x_91, 4);
lean_inc(x_101);
lean_dec(x_91);
x_102 = l_List_forM___at_Lean_CollectAxioms_collect___spec__2(x_101, x_2, x_3);
return x_102;
}
else
{
size_t x_103; size_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_103 = 0;
x_104 = lean_usize_of_nat(x_95);
lean_dec(x_95);
lean_inc(x_2);
x_105 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_94, x_103, x_104, x_10, x_2, x_3);
lean_dec(x_94);
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
x_107 = lean_ctor_get(x_91, 4);
lean_inc(x_107);
lean_dec(x_91);
x_108 = l_List_forM___at_Lean_CollectAxioms_collect___spec__2(x_107, x_2, x_106);
return x_108;
}
}
}
default: 
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_dec(x_11);
lean_dec(x_5);
lean_dec(x_1);
x_109 = lean_ctor_get(x_14, 0);
lean_inc(x_109);
lean_dec(x_14);
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
lean_dec(x_109);
x_111 = lean_ctor_get(x_110, 2);
lean_inc(x_111);
lean_dec(x_110);
x_112 = l_Lean_Expr_getUsedConstants(x_111);
x_113 = lean_array_get_size(x_112);
x_114 = lean_unsigned_to_nat(0u);
x_115 = lean_nat_dec_lt(x_114, x_113);
if (x_115 == 0)
{
lean_object* x_116; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_2);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_10);
lean_ctor_set(x_116, 1, x_3);
return x_116;
}
else
{
uint8_t x_117; 
x_117 = lean_nat_dec_le(x_113, x_113);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_2);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_10);
lean_ctor_set(x_118, 1, x_3);
return x_118;
}
else
{
size_t x_119; size_t x_120; lean_object* x_121; 
x_119 = 0;
x_120 = lean_usize_of_nat(x_113);
lean_dec(x_113);
x_121 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_112, x_119, x_120, x_10, x_2, x_3);
lean_dec(x_112);
return x_121;
}
}
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_3);
x_122 = lean_box(0);
lean_inc(x_1);
x_123 = l_Lean_RBNode_insert___at_Lean_NameSet_insert___spec__1(x_4, x_1, x_122);
lean_inc(x_5);
lean_inc(x_123);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_5);
lean_inc(x_2);
x_125 = l_Lean_Environment_find_x3f(x_2, x_1);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; 
lean_dec(x_123);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_122);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
else
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_125, 0);
lean_inc(x_127);
lean_dec(x_125);
switch (lean_obj_tag(x_127)) {
case 0:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_127);
lean_dec(x_124);
lean_dec(x_2);
x_128 = lean_array_push(x_5, x_1);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_123);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_122);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
case 1:
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; uint8_t x_137; lean_object* x_138; 
lean_dec(x_123);
lean_dec(x_5);
lean_dec(x_1);
x_131 = lean_ctor_get(x_127, 0);
lean_inc(x_131);
lean_dec(x_127);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_132, 2);
lean_inc(x_133);
lean_dec(x_132);
x_134 = l_Lean_Expr_getUsedConstants(x_133);
x_135 = lean_array_get_size(x_134);
x_136 = lean_unsigned_to_nat(0u);
x_137 = lean_nat_dec_lt(x_136, x_135);
if (x_137 == 0)
{
lean_dec(x_135);
lean_dec(x_134);
x_138 = x_124;
goto block_149;
}
else
{
uint8_t x_150; 
x_150 = lean_nat_dec_le(x_135, x_135);
if (x_150 == 0)
{
lean_dec(x_135);
lean_dec(x_134);
x_138 = x_124;
goto block_149;
}
else
{
size_t x_151; size_t x_152; lean_object* x_153; lean_object* x_154; 
x_151 = 0;
x_152 = lean_usize_of_nat(x_135);
lean_dec(x_135);
lean_inc(x_2);
x_153 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_134, x_151, x_152, x_122, x_2, x_124);
lean_dec(x_134);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec(x_153);
x_138 = x_154;
goto block_149;
}
}
block_149:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_139 = lean_ctor_get(x_131, 1);
lean_inc(x_139);
lean_dec(x_131);
x_140 = l_Lean_Expr_getUsedConstants(x_139);
x_141 = lean_array_get_size(x_140);
x_142 = lean_nat_dec_lt(x_136, x_141);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_2);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_122);
lean_ctor_set(x_143, 1, x_138);
return x_143;
}
else
{
uint8_t x_144; 
x_144 = lean_nat_dec_le(x_141, x_141);
if (x_144 == 0)
{
lean_object* x_145; 
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_2);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_122);
lean_ctor_set(x_145, 1, x_138);
return x_145;
}
else
{
size_t x_146; size_t x_147; lean_object* x_148; 
x_146 = 0;
x_147 = lean_usize_of_nat(x_141);
lean_dec(x_141);
x_148 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_140, x_146, x_147, x_122, x_2, x_138);
lean_dec(x_140);
return x_148;
}
}
}
}
case 2:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; lean_object* x_162; 
lean_dec(x_123);
lean_dec(x_5);
lean_dec(x_1);
x_155 = lean_ctor_get(x_127, 0);
lean_inc(x_155);
lean_dec(x_127);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_156, 2);
lean_inc(x_157);
lean_dec(x_156);
x_158 = l_Lean_Expr_getUsedConstants(x_157);
x_159 = lean_array_get_size(x_158);
x_160 = lean_unsigned_to_nat(0u);
x_161 = lean_nat_dec_lt(x_160, x_159);
if (x_161 == 0)
{
lean_dec(x_159);
lean_dec(x_158);
x_162 = x_124;
goto block_173;
}
else
{
uint8_t x_174; 
x_174 = lean_nat_dec_le(x_159, x_159);
if (x_174 == 0)
{
lean_dec(x_159);
lean_dec(x_158);
x_162 = x_124;
goto block_173;
}
else
{
size_t x_175; size_t x_176; lean_object* x_177; lean_object* x_178; 
x_175 = 0;
x_176 = lean_usize_of_nat(x_159);
lean_dec(x_159);
lean_inc(x_2);
x_177 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_158, x_175, x_176, x_122, x_2, x_124);
lean_dec(x_158);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
lean_dec(x_177);
x_162 = x_178;
goto block_173;
}
}
block_173:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_163 = lean_ctor_get(x_155, 1);
lean_inc(x_163);
lean_dec(x_155);
x_164 = l_Lean_Expr_getUsedConstants(x_163);
x_165 = lean_array_get_size(x_164);
x_166 = lean_nat_dec_lt(x_160, x_165);
if (x_166 == 0)
{
lean_object* x_167; 
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_2);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_122);
lean_ctor_set(x_167, 1, x_162);
return x_167;
}
else
{
uint8_t x_168; 
x_168 = lean_nat_dec_le(x_165, x_165);
if (x_168 == 0)
{
lean_object* x_169; 
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_2);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_122);
lean_ctor_set(x_169, 1, x_162);
return x_169;
}
else
{
size_t x_170; size_t x_171; lean_object* x_172; 
x_170 = 0;
x_171 = lean_usize_of_nat(x_165);
lean_dec(x_165);
x_172 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_164, x_170, x_171, x_122, x_2, x_162);
lean_dec(x_164);
return x_172;
}
}
}
}
case 3:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; lean_object* x_186; 
lean_dec(x_123);
lean_dec(x_5);
lean_dec(x_1);
x_179 = lean_ctor_get(x_127, 0);
lean_inc(x_179);
lean_dec(x_127);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_180, 2);
lean_inc(x_181);
lean_dec(x_180);
x_182 = l_Lean_Expr_getUsedConstants(x_181);
x_183 = lean_array_get_size(x_182);
x_184 = lean_unsigned_to_nat(0u);
x_185 = lean_nat_dec_lt(x_184, x_183);
if (x_185 == 0)
{
lean_dec(x_183);
lean_dec(x_182);
x_186 = x_124;
goto block_197;
}
else
{
uint8_t x_198; 
x_198 = lean_nat_dec_le(x_183, x_183);
if (x_198 == 0)
{
lean_dec(x_183);
lean_dec(x_182);
x_186 = x_124;
goto block_197;
}
else
{
size_t x_199; size_t x_200; lean_object* x_201; lean_object* x_202; 
x_199 = 0;
x_200 = lean_usize_of_nat(x_183);
lean_dec(x_183);
lean_inc(x_2);
x_201 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_182, x_199, x_200, x_122, x_2, x_124);
lean_dec(x_182);
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
lean_dec(x_201);
x_186 = x_202;
goto block_197;
}
}
block_197:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_187 = lean_ctor_get(x_179, 1);
lean_inc(x_187);
lean_dec(x_179);
x_188 = l_Lean_Expr_getUsedConstants(x_187);
x_189 = lean_array_get_size(x_188);
x_190 = lean_nat_dec_lt(x_184, x_189);
if (x_190 == 0)
{
lean_object* x_191; 
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_2);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_122);
lean_ctor_set(x_191, 1, x_186);
return x_191;
}
else
{
uint8_t x_192; 
x_192 = lean_nat_dec_le(x_189, x_189);
if (x_192 == 0)
{
lean_object* x_193; 
lean_dec(x_189);
lean_dec(x_188);
lean_dec(x_2);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_122);
lean_ctor_set(x_193, 1, x_186);
return x_193;
}
else
{
size_t x_194; size_t x_195; lean_object* x_196; 
x_194 = 0;
x_195 = lean_usize_of_nat(x_189);
lean_dec(x_189);
x_196 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_188, x_194, x_195, x_122, x_2, x_186);
lean_dec(x_188);
return x_196;
}
}
}
}
case 4:
{
lean_object* x_203; 
lean_dec(x_127);
lean_dec(x_123);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_122);
lean_ctor_set(x_203, 1, x_124);
return x_203;
}
case 5:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; 
lean_dec(x_123);
lean_dec(x_5);
lean_dec(x_1);
x_204 = lean_ctor_get(x_127, 0);
lean_inc(x_204);
lean_dec(x_127);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_205, 2);
lean_inc(x_206);
lean_dec(x_205);
x_207 = l_Lean_Expr_getUsedConstants(x_206);
x_208 = lean_array_get_size(x_207);
x_209 = lean_unsigned_to_nat(0u);
x_210 = lean_nat_dec_lt(x_209, x_208);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; 
lean_dec(x_208);
lean_dec(x_207);
x_211 = lean_ctor_get(x_204, 4);
lean_inc(x_211);
lean_dec(x_204);
x_212 = l_List_forM___at_Lean_CollectAxioms_collect___spec__2(x_211, x_2, x_124);
return x_212;
}
else
{
uint8_t x_213; 
x_213 = lean_nat_dec_le(x_208, x_208);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_208);
lean_dec(x_207);
x_214 = lean_ctor_get(x_204, 4);
lean_inc(x_214);
lean_dec(x_204);
x_215 = l_List_forM___at_Lean_CollectAxioms_collect___spec__2(x_214, x_2, x_124);
return x_215;
}
else
{
size_t x_216; size_t x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_216 = 0;
x_217 = lean_usize_of_nat(x_208);
lean_dec(x_208);
lean_inc(x_2);
x_218 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_207, x_216, x_217, x_122, x_2, x_124);
lean_dec(x_207);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
lean_dec(x_218);
x_220 = lean_ctor_get(x_204, 4);
lean_inc(x_220);
lean_dec(x_204);
x_221 = l_List_forM___at_Lean_CollectAxioms_collect___spec__2(x_220, x_2, x_219);
return x_221;
}
}
}
default: 
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
lean_dec(x_123);
lean_dec(x_5);
lean_dec(x_1);
x_222 = lean_ctor_get(x_127, 0);
lean_inc(x_222);
lean_dec(x_127);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
lean_dec(x_222);
x_224 = lean_ctor_get(x_223, 2);
lean_inc(x_224);
lean_dec(x_223);
x_225 = l_Lean_Expr_getUsedConstants(x_224);
x_226 = lean_array_get_size(x_225);
x_227 = lean_unsigned_to_nat(0u);
x_228 = lean_nat_dec_lt(x_227, x_226);
if (x_228 == 0)
{
lean_object* x_229; 
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_2);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_122);
lean_ctor_set(x_229, 1, x_124);
return x_229;
}
else
{
uint8_t x_230; 
x_230 = lean_nat_dec_le(x_226, x_226);
if (x_230 == 0)
{
lean_object* x_231; 
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_2);
x_231 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_231, 0, x_122);
lean_ctor_set(x_231, 1, x_124);
return x_231;
}
else
{
size_t x_232; size_t x_233; lean_object* x_234; 
x_232 = 0;
x_233 = lean_usize_of_nat(x_226);
lean_dec(x_226);
x_234 = l_Array_foldlMUnsafe_fold___at_Lean_CollectAxioms_collect___spec__1(x_225, x_232, x_233, x_122, x_2, x_124);
lean_dec(x_225);
return x_234;
}
}
}
}
}
}
}
else
{
lean_object* x_235; lean_object* x_236; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_235 = lean_box(0);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_3);
return x_236;
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
