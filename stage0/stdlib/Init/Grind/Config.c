// Lean compiler output
// Module: Init.Grind.Config
// Imports: public import Init.Core
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
static const lean_ctor_object l_Lean_Grind_instInhabitedConfig_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*11 + 32, .m_other = 11, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Grind_instInhabitedConfig_default___closed__0 = (const lean_object*)&l_Lean_Grind_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instInhabitedConfig_default = (const lean_object*)&l_Lean_Grind_instInhabitedConfig_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instInhabitedConfig = (const lean_object*)&l_Lean_Grind_instInhabitedConfig_default___closed__0_value;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Grind_instBEqConfig_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqConfig_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Grind_instBEqConfig___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Grind_instBEqConfig_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Grind_instBEqConfig___closed__0 = (const lean_object*)&l_Lean_Grind_instBEqConfig___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Grind_instBEqConfig = (const lean_object*)&l_Lean_Grind_instBEqConfig___closed__0_value;
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_nat_dec_eq(x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Grind_instBEqConfig_beq(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; uint8_t x_81; lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_85; uint8_t x_86; uint8_t x_87; lean_object* x_88; uint8_t x_93; uint8_t x_99; uint8_t x_105; uint8_t x_119; uint8_t x_126; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 3);
x_7 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 4);
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_1, 2);
x_11 = lean_ctor_get(x_1, 3);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 5);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 6);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 7);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 8);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 9);
x_17 = lean_ctor_get(x_1, 4);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 10);
x_19 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 11);
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 12);
x_21 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 13);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 14);
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 15);
x_24 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 16);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 17);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 18);
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 19);
x_28 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 20);
x_29 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 21);
x_30 = lean_ctor_get(x_1, 5);
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 22);
x_32 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 23);
x_33 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 24);
x_34 = lean_ctor_get(x_1, 6);
x_35 = lean_ctor_get(x_1, 7);
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 25);
x_37 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 26);
x_38 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 27);
x_39 = lean_ctor_get(x_1, 8);
x_40 = lean_ctor_get(x_1, 9);
x_41 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 28);
x_42 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 29);
x_43 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 30);
x_44 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 31);
x_45 = lean_ctor_get(x_1, 10);
x_46 = lean_ctor_get_uint8(x_2, sizeof(void*)*11);
x_47 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 1);
x_48 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 2);
x_49 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 3);
x_50 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 4);
x_51 = lean_ctor_get(x_2, 0);
x_52 = lean_ctor_get(x_2, 1);
x_53 = lean_ctor_get(x_2, 2);
x_54 = lean_ctor_get(x_2, 3);
x_55 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 5);
x_56 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 6);
x_57 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 7);
x_58 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 8);
x_59 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 9);
x_60 = lean_ctor_get(x_2, 4);
x_61 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 10);
x_62 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 11);
x_63 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 12);
x_64 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 13);
x_65 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 14);
x_66 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 15);
x_67 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 16);
x_68 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 17);
x_69 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 18);
x_70 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 19);
x_71 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 20);
x_72 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 21);
x_73 = lean_ctor_get(x_2, 5);
x_74 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 22);
x_75 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 23);
x_76 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 24);
x_77 = lean_ctor_get(x_2, 6);
x_78 = lean_ctor_get(x_2, 7);
x_79 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 25);
x_80 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 26);
x_81 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 27);
x_82 = lean_ctor_get(x_2, 8);
x_83 = lean_ctor_get(x_2, 9);
x_84 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 28);
x_85 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 29);
x_86 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 30);
x_87 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 31);
x_88 = lean_ctor_get(x_2, 10);
if (x_3 == 0)
{
if (x_46 == 0)
{
goto block_136;
}
else
{
return x_3;
}
}
else
{
if (x_46 == 0)
{
return x_46;
}
else
{
goto block_136;
}
}
block_91:
{
if (x_44 == 0)
{
if (x_87 == 0)
{
uint8_t x_89; 
x_89 = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(x_45, x_88);
return x_89;
}
else
{
return x_44;
}
}
else
{
if (x_87 == 0)
{
return x_87;
}
else
{
uint8_t x_90; 
x_90 = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(x_45, x_88);
return x_90;
}
}
}
block_92:
{
if (x_43 == 0)
{
if (x_86 == 0)
{
goto block_91;
}
else
{
return x_43;
}
}
else
{
if (x_86 == 0)
{
return x_86;
}
else
{
goto block_91;
}
}
}
block_94:
{
if (x_93 == 0)
{
return x_93;
}
else
{
if (x_42 == 0)
{
if (x_85 == 0)
{
goto block_92;
}
else
{
return x_42;
}
}
else
{
if (x_85 == 0)
{
return x_85;
}
else
{
goto block_92;
}
}
}
}
block_97:
{
uint8_t x_95; 
x_95 = lean_nat_dec_eq(x_39, x_82);
if (x_95 == 0)
{
return x_95;
}
else
{
uint8_t x_96; 
x_96 = lean_nat_dec_eq(x_40, x_83);
if (x_96 == 0)
{
return x_96;
}
else
{
if (x_41 == 0)
{
if (x_84 == 0)
{
x_93 = x_96;
goto block_94;
}
else
{
return x_41;
}
}
else
{
x_93 = x_84;
goto block_94;
}
}
}
}
block_98:
{
if (x_38 == 0)
{
if (x_81 == 0)
{
goto block_97;
}
else
{
return x_38;
}
}
else
{
if (x_81 == 0)
{
return x_81;
}
else
{
goto block_97;
}
}
}
block_100:
{
if (x_99 == 0)
{
return x_99;
}
else
{
if (x_37 == 0)
{
if (x_80 == 0)
{
goto block_98;
}
else
{
return x_37;
}
}
else
{
if (x_80 == 0)
{
return x_80;
}
else
{
goto block_98;
}
}
}
}
block_103:
{
uint8_t x_101; 
x_101 = lean_nat_dec_eq(x_34, x_77);
if (x_101 == 0)
{
return x_101;
}
else
{
uint8_t x_102; 
x_102 = lean_nat_dec_eq(x_35, x_78);
if (x_102 == 0)
{
return x_102;
}
else
{
if (x_36 == 0)
{
if (x_79 == 0)
{
x_99 = x_102;
goto block_100;
}
else
{
return x_36;
}
}
else
{
x_99 = x_79;
goto block_100;
}
}
}
}
block_104:
{
if (x_33 == 0)
{
if (x_76 == 0)
{
goto block_103;
}
else
{
return x_33;
}
}
else
{
if (x_76 == 0)
{
return x_76;
}
else
{
goto block_103;
}
}
}
block_106:
{
if (x_105 == 0)
{
return x_105;
}
else
{
if (x_32 == 0)
{
if (x_75 == 0)
{
goto block_104;
}
else
{
return x_32;
}
}
else
{
if (x_75 == 0)
{
return x_75;
}
else
{
goto block_104;
}
}
}
}
block_108:
{
uint8_t x_107; 
x_107 = lean_nat_dec_eq(x_30, x_73);
if (x_107 == 0)
{
return x_107;
}
else
{
if (x_31 == 0)
{
if (x_74 == 0)
{
x_105 = x_107;
goto block_106;
}
else
{
return x_31;
}
}
else
{
x_105 = x_74;
goto block_106;
}
}
}
block_109:
{
if (x_29 == 0)
{
if (x_72 == 0)
{
goto block_108;
}
else
{
return x_29;
}
}
else
{
if (x_72 == 0)
{
return x_72;
}
else
{
goto block_108;
}
}
}
block_110:
{
if (x_28 == 0)
{
if (x_71 == 0)
{
goto block_109;
}
else
{
return x_28;
}
}
else
{
if (x_71 == 0)
{
return x_71;
}
else
{
goto block_109;
}
}
}
block_111:
{
if (x_27 == 0)
{
if (x_70 == 0)
{
goto block_110;
}
else
{
return x_27;
}
}
else
{
if (x_70 == 0)
{
return x_70;
}
else
{
goto block_110;
}
}
}
block_112:
{
if (x_26 == 0)
{
if (x_69 == 0)
{
goto block_111;
}
else
{
return x_26;
}
}
else
{
if (x_69 == 0)
{
return x_69;
}
else
{
goto block_111;
}
}
}
block_113:
{
if (x_25 == 0)
{
if (x_68 == 0)
{
goto block_112;
}
else
{
return x_25;
}
}
else
{
if (x_68 == 0)
{
return x_68;
}
else
{
goto block_112;
}
}
}
block_114:
{
if (x_24 == 0)
{
if (x_67 == 0)
{
goto block_113;
}
else
{
return x_24;
}
}
else
{
if (x_67 == 0)
{
return x_67;
}
else
{
goto block_113;
}
}
}
block_115:
{
if (x_23 == 0)
{
if (x_66 == 0)
{
goto block_114;
}
else
{
return x_23;
}
}
else
{
if (x_66 == 0)
{
return x_66;
}
else
{
goto block_114;
}
}
}
block_116:
{
if (x_22 == 0)
{
if (x_65 == 0)
{
goto block_115;
}
else
{
return x_22;
}
}
else
{
if (x_65 == 0)
{
return x_65;
}
else
{
goto block_115;
}
}
}
block_117:
{
if (x_21 == 0)
{
if (x_64 == 0)
{
goto block_116;
}
else
{
return x_21;
}
}
else
{
if (x_64 == 0)
{
return x_64;
}
else
{
goto block_116;
}
}
}
block_118:
{
if (x_20 == 0)
{
if (x_63 == 0)
{
goto block_117;
}
else
{
return x_20;
}
}
else
{
if (x_63 == 0)
{
return x_63;
}
else
{
goto block_117;
}
}
}
block_120:
{
if (x_119 == 0)
{
return x_119;
}
else
{
if (x_19 == 0)
{
if (x_62 == 0)
{
goto block_118;
}
else
{
return x_19;
}
}
else
{
if (x_62 == 0)
{
return x_62;
}
else
{
goto block_118;
}
}
}
}
block_122:
{
uint8_t x_121; 
x_121 = lean_nat_dec_eq(x_17, x_60);
if (x_121 == 0)
{
return x_121;
}
else
{
if (x_18 == 0)
{
if (x_61 == 0)
{
x_119 = x_121;
goto block_120;
}
else
{
return x_18;
}
}
else
{
x_119 = x_61;
goto block_120;
}
}
}
block_123:
{
if (x_16 == 0)
{
if (x_59 == 0)
{
goto block_122;
}
else
{
return x_16;
}
}
else
{
if (x_59 == 0)
{
return x_59;
}
else
{
goto block_122;
}
}
}
block_124:
{
if (x_15 == 0)
{
if (x_58 == 0)
{
goto block_123;
}
else
{
return x_15;
}
}
else
{
if (x_58 == 0)
{
return x_58;
}
else
{
goto block_123;
}
}
}
block_125:
{
if (x_14 == 0)
{
if (x_57 == 0)
{
goto block_124;
}
else
{
return x_14;
}
}
else
{
if (x_57 == 0)
{
return x_57;
}
else
{
goto block_124;
}
}
}
block_127:
{
if (x_126 == 0)
{
return x_126;
}
else
{
if (x_13 == 0)
{
if (x_56 == 0)
{
goto block_125;
}
else
{
return x_13;
}
}
else
{
if (x_56 == 0)
{
return x_56;
}
else
{
goto block_125;
}
}
}
}
block_132:
{
uint8_t x_128; 
x_128 = lean_nat_dec_eq(x_8, x_51);
if (x_128 == 0)
{
return x_128;
}
else
{
uint8_t x_129; 
x_129 = lean_nat_dec_eq(x_9, x_52);
if (x_129 == 0)
{
return x_129;
}
else
{
uint8_t x_130; 
x_130 = lean_nat_dec_eq(x_10, x_53);
if (x_130 == 0)
{
return x_130;
}
else
{
uint8_t x_131; 
x_131 = lean_nat_dec_eq(x_11, x_54);
if (x_131 == 0)
{
return x_131;
}
else
{
if (x_12 == 0)
{
if (x_55 == 0)
{
x_126 = x_131;
goto block_127;
}
else
{
return x_12;
}
}
else
{
x_126 = x_55;
goto block_127;
}
}
}
}
}
}
block_133:
{
if (x_7 == 0)
{
if (x_50 == 0)
{
goto block_132;
}
else
{
return x_7;
}
}
else
{
if (x_50 == 0)
{
return x_50;
}
else
{
goto block_132;
}
}
}
block_134:
{
if (x_6 == 0)
{
if (x_49 == 0)
{
goto block_133;
}
else
{
return x_6;
}
}
else
{
if (x_49 == 0)
{
return x_49;
}
else
{
goto block_133;
}
}
}
block_135:
{
if (x_5 == 0)
{
if (x_48 == 0)
{
goto block_134;
}
else
{
return x_5;
}
}
else
{
if (x_48 == 0)
{
return x_48;
}
else
{
goto block_134;
}
}
}
block_136:
{
if (x_4 == 0)
{
if (x_47 == 0)
{
goto block_135;
}
else
{
return x_4;
}
}
else
{
if (x_47 == 0)
{
return x_47;
}
else
{
goto block_135;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_instBEqConfig_beq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Grind_instBEqConfig_beq(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Grind_Config(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Core(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Grind_Config(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Core(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Config(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Grind_Config(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Grind_Config(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Grind_Config(builtin);
}
#ifdef __cplusplus
}
#endif
