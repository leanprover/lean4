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
uint8_t x_3; uint8_t x_4; uint8_t x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; lean_object* x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_83; uint8_t x_84; uint8_t x_85; lean_object* x_86; uint8_t x_91; uint8_t x_97; uint8_t x_103; uint8_t x_117; uint8_t x_124; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*11);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 3);
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 4);
x_12 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 5);
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 6);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 7);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 8);
x_16 = lean_ctor_get(x_1, 4);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 9);
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
x_29 = lean_ctor_get(x_1, 5);
x_30 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 21);
x_31 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 22);
x_32 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 23);
x_33 = lean_ctor_get(x_1, 6);
x_34 = lean_ctor_get(x_1, 7);
x_35 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 24);
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 25);
x_37 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 26);
x_38 = lean_ctor_get(x_1, 8);
x_39 = lean_ctor_get(x_1, 9);
x_40 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 27);
x_41 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 28);
x_42 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 29);
x_43 = lean_ctor_get_uint8(x_1, sizeof(void*)*11 + 30);
x_44 = lean_ctor_get(x_1, 10);
x_45 = lean_ctor_get_uint8(x_2, sizeof(void*)*11);
x_46 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 1);
x_47 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 2);
x_48 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 3);
x_49 = lean_ctor_get(x_2, 0);
x_50 = lean_ctor_get(x_2, 1);
x_51 = lean_ctor_get(x_2, 2);
x_52 = lean_ctor_get(x_2, 3);
x_53 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 4);
x_54 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 5);
x_55 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 6);
x_56 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 7);
x_57 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 8);
x_58 = lean_ctor_get(x_2, 4);
x_59 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 9);
x_60 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 10);
x_61 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 11);
x_62 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 12);
x_63 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 13);
x_64 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 14);
x_65 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 15);
x_66 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 16);
x_67 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 17);
x_68 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 18);
x_69 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 19);
x_70 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 20);
x_71 = lean_ctor_get(x_2, 5);
x_72 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 21);
x_73 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 22);
x_74 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 23);
x_75 = lean_ctor_get(x_2, 6);
x_76 = lean_ctor_get(x_2, 7);
x_77 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 24);
x_78 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 25);
x_79 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 26);
x_80 = lean_ctor_get(x_2, 8);
x_81 = lean_ctor_get(x_2, 9);
x_82 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 27);
x_83 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 28);
x_84 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 29);
x_85 = lean_ctor_get_uint8(x_2, sizeof(void*)*11 + 30);
x_86 = lean_ctor_get(x_2, 10);
if (x_3 == 0)
{
if (x_45 == 0)
{
goto block_133;
}
else
{
return x_3;
}
}
else
{
if (x_45 == 0)
{
return x_45;
}
else
{
goto block_133;
}
}
block_89:
{
if (x_43 == 0)
{
if (x_85 == 0)
{
uint8_t x_87; 
x_87 = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(x_44, x_86);
return x_87;
}
else
{
return x_43;
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
uint8_t x_88; 
x_88 = l_instBEqOption_beq___at___00Lean_Grind_instBEqConfig_beq_spec__0(x_44, x_86);
return x_88;
}
}
}
block_90:
{
if (x_42 == 0)
{
if (x_84 == 0)
{
goto block_89;
}
else
{
return x_42;
}
}
else
{
if (x_84 == 0)
{
return x_84;
}
else
{
goto block_89;
}
}
}
block_92:
{
if (x_91 == 0)
{
return x_91;
}
else
{
if (x_41 == 0)
{
if (x_83 == 0)
{
goto block_90;
}
else
{
return x_41;
}
}
else
{
if (x_83 == 0)
{
return x_83;
}
else
{
goto block_90;
}
}
}
}
block_95:
{
uint8_t x_93; 
x_93 = lean_nat_dec_eq(x_38, x_80);
if (x_93 == 0)
{
return x_93;
}
else
{
uint8_t x_94; 
x_94 = lean_nat_dec_eq(x_39, x_81);
if (x_94 == 0)
{
return x_94;
}
else
{
if (x_40 == 0)
{
if (x_82 == 0)
{
x_91 = x_94;
goto block_92;
}
else
{
return x_40;
}
}
else
{
x_91 = x_82;
goto block_92;
}
}
}
}
block_96:
{
if (x_37 == 0)
{
if (x_79 == 0)
{
goto block_95;
}
else
{
return x_37;
}
}
else
{
if (x_79 == 0)
{
return x_79;
}
else
{
goto block_95;
}
}
}
block_98:
{
if (x_97 == 0)
{
return x_97;
}
else
{
if (x_36 == 0)
{
if (x_78 == 0)
{
goto block_96;
}
else
{
return x_36;
}
}
else
{
if (x_78 == 0)
{
return x_78;
}
else
{
goto block_96;
}
}
}
}
block_101:
{
uint8_t x_99; 
x_99 = lean_nat_dec_eq(x_33, x_75);
if (x_99 == 0)
{
return x_99;
}
else
{
uint8_t x_100; 
x_100 = lean_nat_dec_eq(x_34, x_76);
if (x_100 == 0)
{
return x_100;
}
else
{
if (x_35 == 0)
{
if (x_77 == 0)
{
x_97 = x_100;
goto block_98;
}
else
{
return x_35;
}
}
else
{
x_97 = x_77;
goto block_98;
}
}
}
}
block_102:
{
if (x_32 == 0)
{
if (x_74 == 0)
{
goto block_101;
}
else
{
return x_32;
}
}
else
{
if (x_74 == 0)
{
return x_74;
}
else
{
goto block_101;
}
}
}
block_104:
{
if (x_103 == 0)
{
return x_103;
}
else
{
if (x_31 == 0)
{
if (x_73 == 0)
{
goto block_102;
}
else
{
return x_31;
}
}
else
{
if (x_73 == 0)
{
return x_73;
}
else
{
goto block_102;
}
}
}
}
block_106:
{
uint8_t x_105; 
x_105 = lean_nat_dec_eq(x_29, x_71);
if (x_105 == 0)
{
return x_105;
}
else
{
if (x_30 == 0)
{
if (x_72 == 0)
{
x_103 = x_105;
goto block_104;
}
else
{
return x_30;
}
}
else
{
x_103 = x_72;
goto block_104;
}
}
}
block_107:
{
if (x_28 == 0)
{
if (x_70 == 0)
{
goto block_106;
}
else
{
return x_28;
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
goto block_106;
}
}
}
block_108:
{
if (x_27 == 0)
{
if (x_69 == 0)
{
goto block_107;
}
else
{
return x_27;
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
goto block_107;
}
}
}
block_109:
{
if (x_26 == 0)
{
if (x_68 == 0)
{
goto block_108;
}
else
{
return x_26;
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
goto block_108;
}
}
}
block_110:
{
if (x_25 == 0)
{
if (x_67 == 0)
{
goto block_109;
}
else
{
return x_25;
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
goto block_109;
}
}
}
block_111:
{
if (x_24 == 0)
{
if (x_66 == 0)
{
goto block_110;
}
else
{
return x_24;
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
goto block_110;
}
}
}
block_112:
{
if (x_23 == 0)
{
if (x_65 == 0)
{
goto block_111;
}
else
{
return x_23;
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
goto block_111;
}
}
}
block_113:
{
if (x_22 == 0)
{
if (x_64 == 0)
{
goto block_112;
}
else
{
return x_22;
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
goto block_112;
}
}
}
block_114:
{
if (x_21 == 0)
{
if (x_63 == 0)
{
goto block_113;
}
else
{
return x_21;
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
goto block_113;
}
}
}
block_115:
{
if (x_20 == 0)
{
if (x_62 == 0)
{
goto block_114;
}
else
{
return x_20;
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
goto block_114;
}
}
}
block_116:
{
if (x_19 == 0)
{
if (x_61 == 0)
{
goto block_115;
}
else
{
return x_19;
}
}
else
{
if (x_61 == 0)
{
return x_61;
}
else
{
goto block_115;
}
}
}
block_118:
{
if (x_117 == 0)
{
return x_117;
}
else
{
if (x_18 == 0)
{
if (x_60 == 0)
{
goto block_116;
}
else
{
return x_18;
}
}
else
{
if (x_60 == 0)
{
return x_60;
}
else
{
goto block_116;
}
}
}
}
block_120:
{
uint8_t x_119; 
x_119 = lean_nat_dec_eq(x_16, x_58);
if (x_119 == 0)
{
return x_119;
}
else
{
if (x_17 == 0)
{
if (x_59 == 0)
{
x_117 = x_119;
goto block_118;
}
else
{
return x_17;
}
}
else
{
x_117 = x_59;
goto block_118;
}
}
}
block_121:
{
if (x_15 == 0)
{
if (x_57 == 0)
{
goto block_120;
}
else
{
return x_15;
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
goto block_120;
}
}
}
block_122:
{
if (x_14 == 0)
{
if (x_56 == 0)
{
goto block_121;
}
else
{
return x_14;
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
goto block_121;
}
}
}
block_123:
{
if (x_13 == 0)
{
if (x_55 == 0)
{
goto block_122;
}
else
{
return x_13;
}
}
else
{
if (x_55 == 0)
{
return x_55;
}
else
{
goto block_122;
}
}
}
block_125:
{
if (x_124 == 0)
{
return x_124;
}
else
{
if (x_12 == 0)
{
if (x_54 == 0)
{
goto block_123;
}
else
{
return x_12;
}
}
else
{
if (x_54 == 0)
{
return x_54;
}
else
{
goto block_123;
}
}
}
}
block_130:
{
uint8_t x_126; 
x_126 = lean_nat_dec_eq(x_7, x_49);
if (x_126 == 0)
{
return x_126;
}
else
{
uint8_t x_127; 
x_127 = lean_nat_dec_eq(x_8, x_50);
if (x_127 == 0)
{
return x_127;
}
else
{
uint8_t x_128; 
x_128 = lean_nat_dec_eq(x_9, x_51);
if (x_128 == 0)
{
return x_128;
}
else
{
uint8_t x_129; 
x_129 = lean_nat_dec_eq(x_10, x_52);
if (x_129 == 0)
{
return x_129;
}
else
{
if (x_11 == 0)
{
if (x_53 == 0)
{
x_124 = x_129;
goto block_125;
}
else
{
return x_11;
}
}
else
{
x_124 = x_53;
goto block_125;
}
}
}
}
}
}
block_131:
{
if (x_6 == 0)
{
if (x_48 == 0)
{
goto block_130;
}
else
{
return x_6;
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
goto block_130;
}
}
}
block_132:
{
if (x_5 == 0)
{
if (x_47 == 0)
{
goto block_131;
}
else
{
return x_5;
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
goto block_131;
}
}
}
block_133:
{
if (x_4 == 0)
{
if (x_46 == 0)
{
goto block_132;
}
else
{
return x_4;
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
goto block_132;
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
lean_object* initialize_Init_Core(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_Config(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
