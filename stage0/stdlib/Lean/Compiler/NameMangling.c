// Lean compiler output
// Module: Lean.Compiler.NameMangling
// Imports: Lean.Data.Name
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
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* lean_mk_module_initialization_function_name(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2;
static lean_object* l_Lean_mkModuleInitializationFunctionName___closed__1;
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint32_t l_Nat_digitChar(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeatTR_loop___at___private_Lean_Compiler_NameMangling_0__String_mangleAux___spec__1(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1;
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Compiler_NameMangling_0__String_mangleAux___spec__2(lean_object*, lean_object*);
static lean_object* l_String_mangle___closed__1;
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3;
lean_object* l_List_lengthTRAux___rarg(lean_object*, lean_object*);
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
static lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_name_mangle(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_String_mangle(lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeatTR_loop___at___private_Lean_Compiler_NameMangling_0__String_mangleAux___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_1);
x_7 = 48;
x_8 = lean_string_push(x_2, x_7);
x_1 = x_6;
x_2 = x_8;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___private_Lean_Compiler_NameMangling_0__String_mangleAux___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_unbox_uint32(x_3);
lean_dec(x_3);
x_6 = lean_string_push(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_U", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_u", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_x", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("__", 2, 2);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__String_mangleAux(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; lean_object* x_99; uint8_t x_118; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_1, x_6);
lean_dec(x_1);
x_8 = 65;
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_string_utf8_get(x_9, x_10);
x_118 = lean_uint32_dec_le(x_8, x_11);
if (x_118 == 0)
{
uint32_t x_119; uint8_t x_120; 
x_119 = 97;
x_120 = lean_uint32_dec_le(x_119, x_11);
if (x_120 == 0)
{
lean_object* x_121; 
lean_dec(x_10);
lean_dec(x_9);
x_121 = lean_box(0);
x_99 = x_121;
goto block_117;
}
else
{
uint32_t x_122; uint8_t x_123; 
x_122 = 122;
x_123 = lean_uint32_dec_le(x_11, x_122);
if (x_123 == 0)
{
lean_object* x_124; 
lean_dec(x_10);
lean_dec(x_9);
x_124 = lean_box(0);
x_99 = x_124;
goto block_117;
}
else
{
uint8_t x_125; 
x_125 = !lean_is_exclusive(x_2);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_126 = lean_ctor_get(x_2, 1);
lean_dec(x_126);
x_127 = lean_ctor_get(x_2, 0);
lean_dec(x_127);
x_128 = lean_string_push(x_3, x_11);
x_129 = lean_string_utf8_next(x_9, x_10);
lean_dec(x_10);
lean_ctor_set(x_2, 1, x_129);
x_1 = x_7;
x_3 = x_128;
goto _start;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_2);
x_131 = lean_string_push(x_3, x_11);
x_132 = lean_string_utf8_next(x_9, x_10);
lean_dec(x_10);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_9);
lean_ctor_set(x_133, 1, x_132);
x_1 = x_7;
x_2 = x_133;
x_3 = x_131;
goto _start;
}
}
}
}
else
{
uint32_t x_135; uint8_t x_136; 
x_135 = 90;
x_136 = lean_uint32_dec_le(x_11, x_135);
if (x_136 == 0)
{
uint32_t x_137; uint8_t x_138; 
x_137 = 97;
x_138 = lean_uint32_dec_le(x_137, x_11);
if (x_138 == 0)
{
lean_object* x_139; 
lean_dec(x_10);
lean_dec(x_9);
x_139 = lean_box(0);
x_99 = x_139;
goto block_117;
}
else
{
uint32_t x_140; uint8_t x_141; 
x_140 = 122;
x_141 = lean_uint32_dec_le(x_11, x_140);
if (x_141 == 0)
{
lean_object* x_142; 
lean_dec(x_10);
lean_dec(x_9);
x_142 = lean_box(0);
x_99 = x_142;
goto block_117;
}
else
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_2);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_2, 1);
lean_dec(x_144);
x_145 = lean_ctor_get(x_2, 0);
lean_dec(x_145);
x_146 = lean_string_push(x_3, x_11);
x_147 = lean_string_utf8_next(x_9, x_10);
lean_dec(x_10);
lean_ctor_set(x_2, 1, x_147);
x_1 = x_7;
x_3 = x_146;
goto _start;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_2);
x_149 = lean_string_push(x_3, x_11);
x_150 = lean_string_utf8_next(x_9, x_10);
lean_dec(x_10);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_9);
lean_ctor_set(x_151, 1, x_150);
x_1 = x_7;
x_2 = x_151;
x_3 = x_149;
goto _start;
}
}
}
}
else
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_2);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_2, 1);
lean_dec(x_154);
x_155 = lean_ctor_get(x_2, 0);
lean_dec(x_155);
x_156 = lean_string_push(x_3, x_11);
x_157 = lean_string_utf8_next(x_9, x_10);
lean_dec(x_10);
lean_ctor_set(x_2, 1, x_157);
x_1 = x_7;
x_3 = x_156;
goto _start;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_2);
x_159 = lean_string_push(x_3, x_11);
x_160 = lean_string_utf8_next(x_9, x_10);
lean_dec(x_10);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_9);
lean_ctor_set(x_161, 1, x_160);
x_1 = x_7;
x_2 = x_161;
x_3 = x_159;
goto _start;
}
}
}
block_98:
{
uint32_t x_13; uint8_t x_14; 
lean_dec(x_12);
x_13 = 95;
x_14 = lean_uint32_dec_eq(x_11, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_uint32_to_nat(x_11);
x_16 = lean_unsigned_to_nat(256u);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_unsigned_to_nat(65536u);
x_19 = lean_nat_dec_lt(x_15, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_20 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1;
x_21 = lean_string_append(x_3, x_20);
x_22 = lean_unsigned_to_nat(16u);
x_23 = l_Nat_toDigits(x_22, x_15);
x_24 = l_List_lengthTRAux___rarg(x_23, x_4);
x_25 = lean_unsigned_to_nat(8u);
x_26 = lean_nat_sub(x_25, x_24);
lean_dec(x_24);
x_27 = l_Nat_repeatTR_loop___at___private_Lean_Compiler_NameMangling_0__String_mangleAux___spec__1(x_26, x_21);
x_28 = l_List_foldl___at___private_Lean_Compiler_NameMangling_0__String_mangleAux___spec__2(x_27, x_23);
x_29 = !lean_is_exclusive(x_2);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_2, 0);
x_31 = lean_ctor_get(x_2, 1);
x_32 = lean_string_utf8_next(x_30, x_31);
lean_dec(x_31);
lean_ctor_set(x_2, 1, x_32);
x_1 = x_7;
x_3 = x_28;
goto _start;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_2, 0);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_2);
x_36 = lean_string_utf8_next(x_34, x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_1 = x_7;
x_2 = x_37;
x_3 = x_28;
goto _start;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint32_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint32_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint32_t x_52; lean_object* x_53; lean_object* x_54; uint32_t x_55; lean_object* x_56; uint8_t x_57; 
x_39 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2;
x_40 = lean_string_append(x_3, x_39);
x_41 = lean_unsigned_to_nat(4096u);
x_42 = lean_nat_div(x_15, x_41);
x_43 = l_Nat_digitChar(x_42);
lean_dec(x_42);
x_44 = lean_string_push(x_40, x_43);
x_45 = lean_nat_mod(x_15, x_41);
lean_dec(x_15);
x_46 = lean_nat_div(x_45, x_16);
x_47 = l_Nat_digitChar(x_46);
lean_dec(x_46);
x_48 = lean_string_push(x_44, x_47);
x_49 = lean_nat_mod(x_45, x_16);
lean_dec(x_45);
x_50 = lean_unsigned_to_nat(16u);
x_51 = lean_nat_div(x_49, x_50);
x_52 = l_Nat_digitChar(x_51);
lean_dec(x_51);
x_53 = lean_string_push(x_48, x_52);
x_54 = lean_nat_mod(x_49, x_50);
lean_dec(x_49);
x_55 = l_Nat_digitChar(x_54);
lean_dec(x_54);
x_56 = lean_string_push(x_53, x_55);
x_57 = !lean_is_exclusive(x_2);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_2, 0);
x_59 = lean_ctor_get(x_2, 1);
x_60 = lean_string_utf8_next(x_58, x_59);
lean_dec(x_59);
lean_ctor_set(x_2, 1, x_60);
x_1 = x_7;
x_3 = x_56;
goto _start;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_2, 0);
x_63 = lean_ctor_get(x_2, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_2);
x_64 = lean_string_utf8_next(x_62, x_63);
lean_dec(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_64);
x_1 = x_7;
x_2 = x_65;
x_3 = x_56;
goto _start;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint32_t x_71; lean_object* x_72; lean_object* x_73; uint32_t x_74; lean_object* x_75; uint8_t x_76; 
x_67 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3;
x_68 = lean_string_append(x_3, x_67);
x_69 = lean_unsigned_to_nat(16u);
x_70 = lean_nat_div(x_15, x_69);
x_71 = l_Nat_digitChar(x_70);
lean_dec(x_70);
x_72 = lean_string_push(x_68, x_71);
x_73 = lean_nat_mod(x_15, x_69);
lean_dec(x_15);
x_74 = l_Nat_digitChar(x_73);
lean_dec(x_73);
x_75 = lean_string_push(x_72, x_74);
x_76 = !lean_is_exclusive(x_2);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_2, 0);
x_78 = lean_ctor_get(x_2, 1);
x_79 = lean_string_utf8_next(x_77, x_78);
lean_dec(x_78);
lean_ctor_set(x_2, 1, x_79);
x_1 = x_7;
x_3 = x_75;
goto _start;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_2, 0);
x_82 = lean_ctor_get(x_2, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_2);
x_83 = lean_string_utf8_next(x_81, x_82);
lean_dec(x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_83);
x_1 = x_7;
x_2 = x_84;
x_3 = x_75;
goto _start;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_86 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__4;
x_87 = lean_string_append(x_3, x_86);
x_88 = !lean_is_exclusive(x_2);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_2, 0);
x_90 = lean_ctor_get(x_2, 1);
x_91 = lean_string_utf8_next(x_89, x_90);
lean_dec(x_90);
lean_ctor_set(x_2, 1, x_91);
x_1 = x_7;
x_3 = x_87;
goto _start;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_93 = lean_ctor_get(x_2, 0);
x_94 = lean_ctor_get(x_2, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_2);
x_95 = lean_string_utf8_next(x_93, x_94);
lean_dec(x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
x_1 = x_7;
x_2 = x_96;
x_3 = x_87;
goto _start;
}
}
}
block_117:
{
uint32_t x_100; uint8_t x_101; 
lean_dec(x_99);
x_100 = 48;
x_101 = lean_uint32_dec_le(x_100, x_11);
if (x_101 == 0)
{
lean_object* x_102; 
x_102 = lean_box(0);
x_12 = x_102;
goto block_98;
}
else
{
uint32_t x_103; uint8_t x_104; 
x_103 = 57;
x_104 = lean_uint32_dec_le(x_11, x_103);
if (x_104 == 0)
{
lean_object* x_105; 
x_105 = lean_box(0);
x_12 = x_105;
goto block_98;
}
else
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_string_push(x_3, x_11);
x_107 = !lean_is_exclusive(x_2);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_2, 0);
x_109 = lean_ctor_get(x_2, 1);
x_110 = lean_string_utf8_next(x_108, x_109);
lean_dec(x_109);
lean_ctor_set(x_2, 1, x_110);
x_1 = x_7;
x_3 = x_106;
goto _start;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_2, 0);
x_113 = lean_ctor_get(x_2, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_2);
x_114 = lean_string_utf8_next(x_112, x_113);
lean_dec(x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
x_1 = x_7;
x_2 = x_115;
x_3 = x_106;
goto _start;
}
}
}
}
}
else
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
}
static lean_object* _init_l_String_mangle___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_String_mangle(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_string_length(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_String_mangle___closed__1;
x_6 = l___private_Lean_Compiler_NameMangling_0__String_mangleAux(x_2, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("_", 1, 1);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = l_String_mangle___closed__1;
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_String_mangle(x_4);
if (lean_obj_tag(x_3) == 0)
{
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(x_3);
x_7 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1;
x_8 = lean_string_append(x_6, x_7);
x_9 = lean_string_append(x_8, x_5);
lean_dec(x_5);
return x_9;
}
}
default: 
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(x_10);
x_13 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1;
x_14 = lean_string_append(x_12, x_13);
x_15 = l___private_Init_Data_Repr_0__Nat_reprFast(x_11);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = lean_string_append(x_16, x_13);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* lean_name_mangle(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux(x_1);
x_4 = lean_string_append(x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_mkModuleInitializationFunctionName___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("initialize_", 11, 11);
return x_1;
}
}
LEAN_EXPORT lean_object* lean_mk_module_initialization_function_name(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_String_mangle___closed__1;
x_3 = lean_name_mangle(x_1, x_2);
x_4 = l_Lean_mkModuleInitializationFunctionName___closed__1;
x_5 = lean_string_append(x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
lean_object* initialize_Lean_Data_Name(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_NameMangling(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1 = _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__1);
l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2 = _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__2);
l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3 = _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__3);
l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__4 = _init_l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__4();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__String_mangleAux___closed__4);
l_String_mangle___closed__1 = _init_l_String_mangle___closed__1();
lean_mark_persistent(l_String_mangle___closed__1);
l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1 = _init_l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1();
lean_mark_persistent(l___private_Lean_Compiler_NameMangling_0__Lean_Name_mangleAux___closed__1);
l_Lean_mkModuleInitializationFunctionName___closed__1 = _init_l_Lean_mkModuleInitializationFunctionName___closed__1();
lean_mark_persistent(l_Lean_mkModuleInitializationFunctionName___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
