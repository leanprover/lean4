// Lean compiler output
// Module: Lake.Build.Target.Fetch
// Imports: Lake.Build.Job Lake.Config.Monad
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
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetch(lean_object*);
static lean_object* l_Lake_BuildKey_fetch___rarg___closed__6;
static lean_object* l_Lake_BuildKey_fetch___rarg___closed__5;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
static lean_object* l_Lake_BuildKey_fetch___rarg___closed__7;
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_TargetArray_fetch___spec__1(lean_object*);
lean_object* l_Lake_Workspace_findModule_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_fetch___rarg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_TargetArray_fetch___spec__1___rarg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_BuildKey_toString(lean_object*);
lean_object* l_Lake_Job_collectArray___rarg(lean_object*);
static lean_object* l_Lake_BuildKey_fetch___rarg___closed__3;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_TargetArray_fetch___spec__1___rarg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___rarg___lambda__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_fetch(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_BuildKey_fetch___rarg___closed__2;
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT uint8_t l_Lake_BuildKey_fetch___rarg___lambda__1(lean_object*);
static lean_object* l_Lake_BuildKey_fetch___rarg___closed__4;
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
static lean_object* l_Lake_BuildKey_fetch___rarg___closed__1;
LEAN_EXPORT uint8_t l_Lake_BuildKey_fetch___rarg___lambda__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = 0;
return x_2;
}
}
static lean_object* _init_l_Lake_BuildKey_fetch___rarg___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid target '", 16, 16);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildKey_fetch___rarg___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("': module '", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildKey_fetch___rarg___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_BuildKey_fetch___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildKey_fetch___rarg___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("' not found in workspace", 24, 24);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildKey_fetch___rarg___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("': package '", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildKey_fetch___rarg___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unsupported target ", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildKey_fetch___rarg___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(": fetching builtin targets by key is not currently supported", 60, 60);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_6, 1);
lean_inc(x_11);
lean_inc(x_9);
x_12 = l_Lake_Workspace_findModule_x3f(x_9, x_11);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_13 = l_Lake_BuildKey_toString(x_1);
x_14 = !lean_is_exclusive(x_1);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_15 = lean_ctor_get(x_1, 1);
lean_dec(x_15);
x_16 = lean_ctor_get(x_1, 0);
lean_dec(x_16);
x_17 = l_Lake_BuildKey_fetch___rarg___closed__1;
x_18 = lean_string_append(x_17, x_13);
lean_dec(x_13);
x_19 = l_Lake_BuildKey_fetch___rarg___closed__2;
x_20 = lean_string_append(x_18, x_19);
x_21 = 1;
x_22 = l_Lake_BuildKey_fetch___rarg___closed__3;
x_23 = l_Lean_Name_toString(x_9, x_21, x_22);
x_24 = lean_string_append(x_20, x_23);
lean_dec(x_23);
x_25 = l_Lake_BuildKey_fetch___rarg___closed__4;
x_26 = lean_string_append(x_24, x_25);
x_27 = 3;
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_27);
x_29 = lean_array_get_size(x_7);
x_30 = lean_array_push(x_7, x_28);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_30);
lean_ctor_set(x_1, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_1);
lean_ctor_set(x_31, 1, x_8);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_1);
x_32 = l_Lake_BuildKey_fetch___rarg___closed__1;
x_33 = lean_string_append(x_32, x_13);
lean_dec(x_13);
x_34 = l_Lake_BuildKey_fetch___rarg___closed__2;
x_35 = lean_string_append(x_33, x_34);
x_36 = 1;
x_37 = l_Lake_BuildKey_fetch___rarg___closed__3;
x_38 = l_Lean_Name_toString(x_9, x_36, x_37);
x_39 = lean_string_append(x_35, x_38);
lean_dec(x_38);
x_40 = l_Lake_BuildKey_fetch___rarg___closed__4;
x_41 = lean_string_append(x_39, x_40);
x_42 = 3;
x_43 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_42);
x_44 = lean_array_get_size(x_7);
x_45 = lean_array_push(x_7, x_43);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_8);
return x_47;
}
}
else
{
uint8_t x_48; 
lean_dec(x_9);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_49 = lean_ctor_get(x_1, 1);
lean_dec(x_49);
x_50 = lean_ctor_get(x_1, 0);
lean_dec(x_50);
x_51 = lean_ctor_get(x_12, 0);
lean_inc(x_51);
lean_dec(x_12);
lean_ctor_set(x_1, 0, x_51);
x_52 = lean_apply_6(x_3, x_1, x_4, x_5, x_6, x_7, x_8);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_1);
x_53 = lean_ctor_get(x_12, 0);
lean_inc(x_53);
lean_dec(x_12);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_10);
x_55 = lean_apply_6(x_3, x_54, x_4, x_5, x_6, x_7, x_8);
return x_55;
}
}
}
case 1:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_6, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_58, 4);
lean_inc(x_59);
lean_dec(x_58);
x_60 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_59, x_56);
lean_dec(x_59);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; uint8_t x_62; 
lean_dec(x_57);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_61 = l_Lake_BuildKey_toString(x_1);
x_62 = !lean_is_exclusive(x_1);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_63 = lean_ctor_get(x_1, 1);
lean_dec(x_63);
x_64 = lean_ctor_get(x_1, 0);
lean_dec(x_64);
x_65 = l_Lake_BuildKey_fetch___rarg___closed__1;
x_66 = lean_string_append(x_65, x_61);
lean_dec(x_61);
x_67 = l_Lake_BuildKey_fetch___rarg___closed__5;
x_68 = lean_string_append(x_66, x_67);
x_69 = 1;
x_70 = l_Lake_BuildKey_fetch___rarg___closed__3;
x_71 = l_Lean_Name_toString(x_56, x_69, x_70);
x_72 = lean_string_append(x_68, x_71);
lean_dec(x_71);
x_73 = l_Lake_BuildKey_fetch___rarg___closed__4;
x_74 = lean_string_append(x_72, x_73);
x_75 = 3;
x_76 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set_uint8(x_76, sizeof(void*)*1, x_75);
x_77 = lean_array_get_size(x_7);
x_78 = lean_array_push(x_7, x_76);
lean_ctor_set(x_1, 1, x_78);
lean_ctor_set(x_1, 0, x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_1);
lean_ctor_set(x_79, 1, x_8);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_1);
x_80 = l_Lake_BuildKey_fetch___rarg___closed__1;
x_81 = lean_string_append(x_80, x_61);
lean_dec(x_61);
x_82 = l_Lake_BuildKey_fetch___rarg___closed__5;
x_83 = lean_string_append(x_81, x_82);
x_84 = 1;
x_85 = l_Lake_BuildKey_fetch___rarg___closed__3;
x_86 = l_Lean_Name_toString(x_56, x_84, x_85);
x_87 = lean_string_append(x_83, x_86);
lean_dec(x_86);
x_88 = l_Lake_BuildKey_fetch___rarg___closed__4;
x_89 = lean_string_append(x_87, x_88);
x_90 = 3;
x_91 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set_uint8(x_91, sizeof(void*)*1, x_90);
x_92 = lean_array_get_size(x_7);
x_93 = lean_array_push(x_7, x_91);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_8);
return x_95;
}
}
else
{
uint8_t x_96; 
lean_dec(x_56);
x_96 = !lean_is_exclusive(x_1);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_1, 1);
lean_dec(x_97);
x_98 = lean_ctor_get(x_1, 0);
lean_dec(x_98);
x_99 = lean_ctor_get(x_60, 0);
lean_inc(x_99);
lean_dec(x_60);
lean_ctor_set(x_1, 0, x_99);
x_100 = lean_apply_6(x_3, x_1, x_4, x_5, x_6, x_7, x_8);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_1);
x_101 = lean_ctor_get(x_60, 0);
lean_inc(x_101);
lean_dec(x_60);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_57);
x_103 = lean_apply_6(x_3, x_102, x_4, x_5, x_6, x_7, x_8);
return x_103;
}
}
}
case 2:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_104 = l_Lake_BuildKey_toString(x_1);
x_105 = l_Lake_BuildKey_fetch___rarg___closed__6;
x_106 = lean_string_append(x_105, x_104);
lean_dec(x_104);
x_107 = l_Lake_BuildKey_fetch___rarg___closed__7;
x_108 = lean_string_append(x_106, x_107);
x_109 = 3;
x_110 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set_uint8(x_110, sizeof(void*)*1, x_109);
x_111 = lean_array_get_size(x_7);
x_112 = lean_array_push(x_7, x_110);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_8);
return x_114;
}
default: 
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_ctor_get(x_1, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_1, 1);
lean_inc(x_116);
x_117 = lean_ctor_get(x_6, 1);
lean_inc(x_117);
x_118 = lean_ctor_get(x_117, 4);
lean_inc(x_118);
lean_dec(x_117);
x_119 = l_Lake_RBNode_dFind___at_Lake_Workspace_findPackage_x3f___spec__1(x_118, x_115);
lean_dec(x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; uint8_t x_121; 
lean_dec(x_116);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_1);
x_120 = l_Lake_BuildKey_toString(x_1);
x_121 = !lean_is_exclusive(x_1);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_122 = lean_ctor_get(x_1, 1);
lean_dec(x_122);
x_123 = lean_ctor_get(x_1, 0);
lean_dec(x_123);
x_124 = l_Lake_BuildKey_fetch___rarg___closed__1;
x_125 = lean_string_append(x_124, x_120);
lean_dec(x_120);
x_126 = l_Lake_BuildKey_fetch___rarg___closed__5;
x_127 = lean_string_append(x_125, x_126);
x_128 = 1;
x_129 = l_Lake_BuildKey_fetch___rarg___closed__3;
x_130 = l_Lean_Name_toString(x_115, x_128, x_129);
x_131 = lean_string_append(x_127, x_130);
lean_dec(x_130);
x_132 = l_Lake_BuildKey_fetch___rarg___closed__4;
x_133 = lean_string_append(x_131, x_132);
x_134 = 3;
x_135 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set_uint8(x_135, sizeof(void*)*1, x_134);
x_136 = lean_array_get_size(x_7);
x_137 = lean_array_push(x_7, x_135);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_137);
lean_ctor_set(x_1, 0, x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_1);
lean_ctor_set(x_138, 1, x_8);
return x_138;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_1);
x_139 = l_Lake_BuildKey_fetch___rarg___closed__1;
x_140 = lean_string_append(x_139, x_120);
lean_dec(x_120);
x_141 = l_Lake_BuildKey_fetch___rarg___closed__5;
x_142 = lean_string_append(x_140, x_141);
x_143 = 1;
x_144 = l_Lake_BuildKey_fetch___rarg___closed__3;
x_145 = l_Lean_Name_toString(x_115, x_143, x_144);
x_146 = lean_string_append(x_142, x_145);
lean_dec(x_145);
x_147 = l_Lake_BuildKey_fetch___rarg___closed__4;
x_148 = lean_string_append(x_146, x_147);
x_149 = 3;
x_150 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set_uint8(x_150, sizeof(void*)*1, x_149);
x_151 = lean_array_get_size(x_7);
x_152 = lean_array_push(x_7, x_150);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_8);
return x_154;
}
}
else
{
uint8_t x_155; 
lean_dec(x_115);
x_155 = !lean_is_exclusive(x_1);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_1, 1);
lean_dec(x_156);
x_157 = lean_ctor_get(x_1, 0);
lean_dec(x_157);
x_158 = lean_ctor_get(x_119, 0);
lean_inc(x_158);
lean_dec(x_119);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 0, x_158);
x_159 = lean_apply_6(x_3, x_1, x_4, x_5, x_6, x_7, x_8);
return x_159;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_1);
x_160 = lean_ctor_get(x_119, 0);
lean_inc(x_160);
lean_dec(x_119);
x_161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_116);
x_162 = lean_apply_6(x_3, x_161, x_4, x_5, x_6, x_7, x_8);
return x_162;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_BuildKey_fetch___rarg), 8, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildKey_fetch___rarg___lambda__1___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_BuildKey_fetch___rarg___lambda__1(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_BuildKey_fetch___rarg(x_1, lean_box(0), x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_fetch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Target_fetch___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_TargetArray_fetch___spec__1___rarg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_uget(x_3, x_2);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_3, x_2, x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_16 = l_Lake_BuildKey_fetch___rarg(x_13, lean_box(0), x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = 1;
x_22 = lean_usize_add(x_2, x_21);
x_23 = lean_array_uset(x_15, x_2, x_19);
x_2 = x_22;
x_3 = x_23;
x_8 = x_20;
x_9 = x_18;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_16);
if (x_25 == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_16, 0);
lean_dec(x_26);
x_27 = !lean_is_exclusive(x_17);
if (x_27 == 0)
{
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_17, 0);
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_17);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_ctor_set(x_16, 0, x_30);
return x_16;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
lean_dec(x_16);
x_32 = lean_ctor_get(x_17, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_17, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_34 = x_17;
} else {
 lean_dec_ref(x_17);
 x_34 = lean_box(0);
}
if (lean_is_scalar(x_34)) {
 x_35 = lean_alloc_ctor(1, 2, 0);
} else {
 x_35 = x_34;
}
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_37 = !lean_is_exclusive(x_16);
if (x_37 == 0)
{
return x_16;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_16, 0);
x_39 = lean_ctor_get(x_16, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_16);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_TargetArray_fetch___spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at_Lake_TargetArray_fetch___spec__1___rarg___boxed), 9, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetch___rarg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_array_size(x_1);
x_9 = 0;
x_10 = l_Array_mapMUnsafe_map___at_Lake_TargetArray_fetch___spec__1___rarg(x_8, x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = l_Lake_Job_collectArray___rarg(x_15);
lean_dec(x_15);
lean_ctor_set(x_11, 0, x_16);
return x_10;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_11, 0);
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_11);
x_19 = l_Lake_Job_collectArray___rarg(x_17);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_10, 1);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_24 = x_11;
} else {
 lean_dec_ref(x_11);
 x_24 = lean_box(0);
}
x_25 = l_Lake_Job_collectArray___rarg(x_22);
lean_dec(x_22);
if (lean_is_scalar(x_24)) {
 x_26 = lean_alloc_ctor(0, 2, 0);
} else {
 x_26 = x_24;
}
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_21);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_10);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_10, 0);
lean_dec(x_29);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
return x_10;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_11, 0);
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_11);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_10, 0, x_33);
return x_10;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_dec(x_10);
x_35 = lean_ctor_get(x_11, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_11, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_37 = x_11;
} else {
 lean_dec_ref(x_11);
 x_37 = lean_box(0);
}
if (lean_is_scalar(x_37)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_37;
}
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_34);
return x_39;
}
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_10);
if (x_40 == 0)
{
return x_10;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_10, 0);
x_42 = lean_ctor_get(x_10, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_10);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_TargetArray_fetch(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_TargetArray_fetch___rarg), 7, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_Lake_TargetArray_fetch___spec__1___rarg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l_Array_mapMUnsafe_map___at_Lake_TargetArray_fetch___spec__1___rarg(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
lean_object* initialize_Lake_Build_Job(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Config_Monad(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Target_Fetch(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Job(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Config_Monad(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_BuildKey_fetch___rarg___closed__1 = _init_l_Lake_BuildKey_fetch___rarg___closed__1();
lean_mark_persistent(l_Lake_BuildKey_fetch___rarg___closed__1);
l_Lake_BuildKey_fetch___rarg___closed__2 = _init_l_Lake_BuildKey_fetch___rarg___closed__2();
lean_mark_persistent(l_Lake_BuildKey_fetch___rarg___closed__2);
l_Lake_BuildKey_fetch___rarg___closed__3 = _init_l_Lake_BuildKey_fetch___rarg___closed__3();
lean_mark_persistent(l_Lake_BuildKey_fetch___rarg___closed__3);
l_Lake_BuildKey_fetch___rarg___closed__4 = _init_l_Lake_BuildKey_fetch___rarg___closed__4();
lean_mark_persistent(l_Lake_BuildKey_fetch___rarg___closed__4);
l_Lake_BuildKey_fetch___rarg___closed__5 = _init_l_Lake_BuildKey_fetch___rarg___closed__5();
lean_mark_persistent(l_Lake_BuildKey_fetch___rarg___closed__5);
l_Lake_BuildKey_fetch___rarg___closed__6 = _init_l_Lake_BuildKey_fetch___rarg___closed__6();
lean_mark_persistent(l_Lake_BuildKey_fetch___rarg___closed__6);
l_Lake_BuildKey_fetch___rarg___closed__7 = _init_l_Lake_BuildKey_fetch___rarg___closed__7();
lean_mark_persistent(l_Lake_BuildKey_fetch___rarg___closed__7);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
