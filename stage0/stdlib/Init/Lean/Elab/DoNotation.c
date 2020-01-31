// Lean compiler output
// Module: Init.Lean.Elab.DoNotation
// Imports: Init.Lean.Elab.Term Init.Lean.Elab.Quotation
#include "runtime/lean.h"
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
lean_object* l_Lean_Elab_Term_elabDo___lambda__1(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_identKind___closed__2;
extern lean_object* l_Array_empty___closed__1;
extern lean_object* l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__9;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Elab_Term_getMainModule___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Term_do___elambda__1___closed__2;
extern lean_object* l___private_Init_Lean_Elab_Quotation_11__letBindRhss___main___closed__17;
extern lean_object* l_Lean_mkAppStx___closed__8;
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDo(lean_object*);
extern lean_object* l_Lean_mkTermIdFromIdent___closed__2;
extern lean_object* l___private_Init_Lean_Parser_Parser_14__antiquotNestedExpr___elambda__1___closed__2;
extern lean_object* l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(lean_object*);
extern lean_object* l_Lean_Parser_Term_doId___elambda__1___closed__2;
extern lean_object* l_Lean_Elab_Term_expandCDot_x3f___closed__3;
lean_object* lean_name_mk_string(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_fun___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_getCurrMacroScope(lean_object*, lean_object*);
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__59;
uint8_t l_coeDecidableEq(uint8_t);
extern lean_object* l_Lean_Elab_Term_expandCDot_x3f___closed__2;
lean_object* l_Lean_Elab_Term_elabDo___closed__1;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__3;
lean_object* l_Lean_Elab_Term_elabDo___lambda__1___closed__3;
extern lean_object* l_Lean_nullKind___closed__2;
extern lean_object* l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__43;
extern lean_object* l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__1;
lean_object* l_Lean_Elab_Term_adaptExpander(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabDo___lambda__1___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
lean_object* l_Lean_Elab_Term_elabDo___lambda__1___closed__1;
lean_object* l_Lean_Elab_Term_addBuiltinTermElab(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabDo(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__2;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Term_elabDo___lambda__1___closed__2;
lean_object* _init_l_Lean_Elab_Term_elabDo___lambda__1___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("HasBind.bind");
return x_1;
}
}
lean_object* _init_l_Lean_Elab_Term_elabDo___lambda__1___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Elab_Term_elabDo___lambda__1___closed__1;
x_2 = lean_string_utf8_byte_size(x_1);
return x_2;
}
}
lean_object* _init_l_Lean_Elab_Term_elabDo___lambda__1___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lean_Elab_Term_elabDo___lambda__1___closed__1;
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Elab_Term_elabDo___lambda__1___closed__2;
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
lean_object* l_Lean_Elab_Term_elabDo___lambda__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_156; uint8_t x_157; 
x_156 = l_Lean_Parser_Term_do___elambda__1___closed__2;
lean_inc(x_1);
x_157 = l_Lean_Syntax_isOfKind(x_1, x_156);
if (x_157 == 0)
{
uint8_t x_158; 
x_158 = 0;
x_4 = x_158;
goto block_155;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_159 = l_Lean_Syntax_getArgs(x_1);
x_160 = lean_array_get_size(x_159);
lean_dec(x_159);
x_161 = lean_unsigned_to_nat(2u);
x_162 = lean_nat_dec_eq(x_160, x_161);
lean_dec(x_160);
x_4 = x_162;
goto block_155;
}
block_155:
{
uint8_t x_5; 
x_5 = l_coeDecidableEq(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_1);
x_6 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_148; uint8_t x_149; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = l_Lean_Syntax_getArg(x_1, x_7);
lean_dec(x_1);
x_148 = l_Lean_nullKind___closed__2;
lean_inc(x_8);
x_149 = l_Lean_Syntax_isOfKind(x_8, x_148);
if (x_149 == 0)
{
uint8_t x_150; 
x_150 = 0;
x_9 = x_150;
goto block_147;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_151 = l_Lean_Syntax_getArgs(x_8);
x_152 = lean_array_get_size(x_151);
lean_dec(x_151);
x_153 = lean_unsigned_to_nat(3u);
x_154 = lean_nat_dec_eq(x_152, x_153);
lean_dec(x_152);
x_9 = x_154;
goto block_147;
}
block_147:
{
uint8_t x_10; 
x_10 = l_coeDecidableEq(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
x_11 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_140; uint8_t x_141; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_8, x_12);
x_140 = l_Lean_Parser_Term_doId___elambda__1___closed__2;
lean_inc(x_13);
x_141 = l_Lean_Syntax_isOfKind(x_13, x_140);
if (x_141 == 0)
{
uint8_t x_142; 
x_142 = 0;
x_14 = x_142;
goto block_139;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
x_143 = l_Lean_Syntax_getArgs(x_13);
x_144 = lean_array_get_size(x_143);
lean_dec(x_143);
x_145 = lean_unsigned_to_nat(4u);
x_146 = lean_nat_dec_eq(x_144, x_145);
lean_dec(x_144);
x_14 = x_146;
goto block_139;
}
block_139:
{
uint8_t x_15; 
x_15 = l_coeDecidableEq(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_8);
x_16 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_3);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_17 = l_Lean_Syntax_getArg(x_13, x_12);
x_18 = l_Lean_identKind___closed__2;
lean_inc(x_17);
x_19 = l_Lean_Syntax_isOfKind(x_17, x_18);
x_20 = l_coeDecidableEq(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
x_21 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_3);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_133; uint8_t x_134; 
x_22 = l_Lean_Syntax_getArg(x_13, x_7);
x_133 = l_Lean_nullKind___closed__2;
lean_inc(x_22);
x_134 = l_Lean_Syntax_isOfKind(x_22, x_133);
if (x_134 == 0)
{
uint8_t x_135; 
lean_dec(x_22);
x_135 = 0;
x_23 = x_135;
goto block_132;
}
else
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_136 = l_Lean_Syntax_getArgs(x_22);
lean_dec(x_22);
x_137 = lean_array_get_size(x_136);
lean_dec(x_136);
x_138 = lean_nat_dec_eq(x_137, x_12);
lean_dec(x_137);
x_23 = x_138;
goto block_132;
}
block_132:
{
uint8_t x_24; 
x_24 = l_coeDecidableEq(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_17);
lean_dec(x_13);
lean_dec(x_8);
x_25 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_3);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_126; uint8_t x_127; 
x_26 = lean_unsigned_to_nat(3u);
x_27 = l_Lean_Syntax_getArg(x_13, x_26);
lean_dec(x_13);
x_28 = lean_unsigned_to_nat(2u);
x_29 = l_Lean_Syntax_getArg(x_8, x_28);
lean_dec(x_8);
x_126 = l_Lean_Parser_Term_doExpr___elambda__1___closed__2;
lean_inc(x_29);
x_127 = l_Lean_Syntax_isOfKind(x_29, x_126);
if (x_127 == 0)
{
uint8_t x_128; 
x_128 = 0;
x_30 = x_128;
goto block_125;
}
else
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; 
x_129 = l_Lean_Syntax_getArgs(x_29);
x_130 = lean_array_get_size(x_129);
lean_dec(x_129);
x_131 = lean_nat_dec_eq(x_130, x_7);
lean_dec(x_130);
x_30 = x_131;
goto block_125;
}
block_125:
{
uint8_t x_31; 
x_31 = l_coeDecidableEq(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec(x_17);
x_32 = l_Lean_Elab_Term_throwUnsupportedSyntax___rarg(x_3);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = l_Lean_Syntax_getArg(x_29, x_12);
lean_dec(x_29);
x_34 = l_Lean_Elab_Term_getCurrMacroScope(x_2, x_3);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Elab_Term_getMainModule___rarg(x_36);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_box(0);
x_41 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
x_42 = l_Lean_addMacroScope(x_39, x_41, x_35);
x_43 = l_Lean_Elab_Term_elabDo___lambda__1___closed__3;
x_44 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__9;
x_45 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_44);
x_46 = l_Array_empty___closed__1;
x_47 = lean_array_push(x_46, x_45);
x_48 = l___private_Init_Lean_Elab_Quotation_11__letBindRhss___main___closed__17;
x_49 = lean_array_push(x_47, x_48);
x_50 = l_Lean_mkTermIdFromIdent___closed__2;
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_array_push(x_46, x_51);
x_53 = lean_array_push(x_46, x_27);
x_54 = lean_array_push(x_46, x_17);
x_55 = lean_array_push(x_54, x_48);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_50);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_array_push(x_46, x_56);
x_58 = l_Lean_nullKind___closed__2;
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_61 = lean_array_push(x_60, x_59);
x_62 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_63 = lean_array_push(x_61, x_62);
x_64 = lean_array_push(x_63, x_33);
x_65 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
x_67 = lean_array_push(x_46, x_66);
x_68 = lean_array_push(x_67, x_48);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_58);
lean_ctor_set(x_69, 1, x_68);
x_70 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__43;
x_71 = lean_array_push(x_70, x_69);
x_72 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__59;
x_73 = lean_array_push(x_71, x_72);
x_74 = l___private_Init_Lean_Parser_Parser_14__antiquotNestedExpr___elambda__1___closed__2;
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_array_push(x_53, x_75);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_58);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_array_push(x_52, x_77);
x_79 = l_Lean_mkAppStx___closed__8;
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
lean_ctor_set(x_37, 0, x_80);
return x_37;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_81 = lean_ctor_get(x_37, 0);
x_82 = lean_ctor_get(x_37, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_37);
x_83 = lean_box(0);
x_84 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__7;
x_85 = l_Lean_addMacroScope(x_81, x_84, x_35);
x_86 = l_Lean_Elab_Term_elabDo___lambda__1___closed__3;
x_87 = l_Lean_Elab_Term_Quotation_stxQuot_expand___closed__9;
x_88 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_88, 0, x_83);
lean_ctor_set(x_88, 1, x_86);
lean_ctor_set(x_88, 2, x_85);
lean_ctor_set(x_88, 3, x_87);
x_89 = l_Array_empty___closed__1;
x_90 = lean_array_push(x_89, x_88);
x_91 = l___private_Init_Lean_Elab_Quotation_11__letBindRhss___main___closed__17;
x_92 = lean_array_push(x_90, x_91);
x_93 = l_Lean_mkTermIdFromIdent___closed__2;
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_92);
x_95 = lean_array_push(x_89, x_94);
x_96 = lean_array_push(x_89, x_27);
x_97 = lean_array_push(x_89, x_17);
x_98 = lean_array_push(x_97, x_91);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_93);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_array_push(x_89, x_99);
x_101 = l_Lean_nullKind___closed__2;
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_100);
x_103 = l_Lean_Elab_Term_expandCDot_x3f___closed__2;
x_104 = lean_array_push(x_103, x_102);
x_105 = l_Lean_Elab_Term_expandCDot_x3f___closed__3;
x_106 = lean_array_push(x_104, x_105);
x_107 = lean_array_push(x_106, x_33);
x_108 = l_Lean_Parser_Term_fun___elambda__1___closed__2;
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_107);
x_110 = lean_array_push(x_89, x_109);
x_111 = lean_array_push(x_110, x_91);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_101);
lean_ctor_set(x_112, 1, x_111);
x_113 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__43;
x_114 = lean_array_push(x_113, x_112);
x_115 = l___private_Init_Lean_Elab_Quotation_5__quoteSyntax___main___closed__59;
x_116 = lean_array_push(x_114, x_115);
x_117 = l___private_Init_Lean_Parser_Parser_14__antiquotNestedExpr___elambda__1___closed__2;
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
x_119 = lean_array_push(x_96, x_118);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_101);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_array_push(x_95, x_120);
x_122 = l_Lean_mkAppStx___closed__8;
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_82);
return x_124;
}
}
}
}
}
}
}
}
}
}
}
}
}
}
lean_object* _init_l_Lean_Elab_Term_elabDo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDo___lambda__1___boxed), 3, 0);
return x_1;
}
}
lean_object* l_Lean_Elab_Term_elabDo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Elab_Term_elabDo___closed__1;
x_6 = l_Lean_Elab_Term_adaptExpander(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
lean_object* l_Lean_Elab_Term_elabDo___lambda__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Term_elabDo___lambda__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("elabDo");
return x_1;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Elab_Term_declareBuiltinTermElab___closed__3;
x_2 = l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Term_elabDo), 4, 0);
return x_1;
}
}
lean_object* l___regBuiltinTermElab_Lean_Elab_Term_elabDo(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_Lean_Parser_Term_do___elambda__1___closed__2;
x_3 = l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__2;
x_4 = l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__3;
x_5 = l_Lean_Elab_Term_addBuiltinTermElab(x_2, x_3, x_4, x_1);
return x_5;
}
}
lean_object* initialize_Init_Lean_Elab_Term(lean_object*);
lean_object* initialize_Init_Lean_Elab_Quotation(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Elab_DoNotation(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Elab_Term(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Elab_Quotation(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Term_elabDo___lambda__1___closed__1 = _init_l_Lean_Elab_Term_elabDo___lambda__1___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabDo___lambda__1___closed__1);
l_Lean_Elab_Term_elabDo___lambda__1___closed__2 = _init_l_Lean_Elab_Term_elabDo___lambda__1___closed__2();
lean_mark_persistent(l_Lean_Elab_Term_elabDo___lambda__1___closed__2);
l_Lean_Elab_Term_elabDo___lambda__1___closed__3 = _init_l_Lean_Elab_Term_elabDo___lambda__1___closed__3();
lean_mark_persistent(l_Lean_Elab_Term_elabDo___lambda__1___closed__3);
l_Lean_Elab_Term_elabDo___closed__1 = _init_l_Lean_Elab_Term_elabDo___closed__1();
lean_mark_persistent(l_Lean_Elab_Term_elabDo___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__1 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__1();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__1);
l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__2 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__2();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__2);
l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__3 = _init_l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__3();
lean_mark_persistent(l___regBuiltinTermElab_Lean_Elab_Term_elabDo___closed__3);
res = l___regBuiltinTermElab_Lean_Elab_Term_elabDo(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
