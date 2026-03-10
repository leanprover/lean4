// Lean compiler output
// Module: Lean.Meta.KAbstract
// Imports: public import Lean.HeadIndex public import Lean.Meta.Basic
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
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
uint8_t l_Lean_instBEqHeadIndex_beq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Occurrences_contains(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_Meta_instBEqOccurrences_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_167; 
x_167 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_167 == 0)
{
lean_object* x_168; uint8_t x_169; 
lean_inc_ref(x_5);
x_168 = l_Lean_Expr_toHeadIndex(x_5);
x_169 = l_Lean_instBEqHeadIndex_beq(x_168, x_3);
lean_dec(x_168);
if (x_169 == 0)
{
x_60 = x_7;
x_61 = x_8;
x_62 = x_9;
x_63 = x_10;
x_64 = x_11;
goto block_166;
}
else
{
if (x_167 == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = l_Lean_Expr_headNumArgs(x_5);
x_171 = lean_nat_dec_eq(x_170, x_4);
lean_dec(x_170);
if (x_171 == 0)
{
x_60 = x_7;
x_61 = x_8;
x_62 = x_9;
x_63 = x_10;
x_64 = x_11;
goto block_166;
}
else
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_st_ref_get(x_9);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc_ref(x_5);
x_173 = l_Lean_Meta_isExprDefEq(x_5, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_203; 
x_174 = lean_ctor_get(x_173, 0);
x_203 = !lean_is_exclusive(x_173);
if (x_203 == 0)
{
x_175 = x_173;
x_176 = x_203;
goto block_202;
}
else
{
lean_inc(x_174);
lean_dec(x_173);
x_175 = lean_box(0);
x_176 = x_203;
goto block_202;
}
block_202:
{
uint8_t x_177; 
x_177 = lean_unbox(x_174);
lean_dec(x_174);
if (x_177 == 0)
{
lean_del_object(x_175);
lean_dec(x_172);
x_60 = x_7;
x_61 = x_8;
x_62 = x_9;
x_63 = x_10;
x_64 = x_11;
goto block_166;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
x_178 = lean_st_ref_get(x_7);
x_179 = lean_unsigned_to_nat(1u);
x_180 = lean_nat_add(x_178, x_179);
x_181 = lean_st_ref_set(x_7, x_180);
x_182 = l_Lean_Meta_Occurrences_contains(x_2, x_178);
lean_dec(x_178);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; uint8_t x_196; 
lean_del_object(x_175);
x_183 = lean_st_ref_take(x_9);
x_184 = lean_ctor_get(x_172, 0);
lean_inc_ref(x_184);
lean_dec(x_172);
x_185 = lean_ctor_get(x_183, 1);
x_186 = lean_ctor_get(x_183, 2);
x_187 = lean_ctor_get(x_183, 3);
x_188 = lean_ctor_get(x_183, 4);
x_196 = !lean_is_exclusive(x_183);
if (x_196 == 0)
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_183, 0);
lean_dec(x_197);
x_189 = x_183;
x_190 = x_196;
goto block_195;
}
else
{
lean_inc(x_188);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_183);
x_189 = lean_box(0);
x_190 = x_196;
goto block_195;
}
block_195:
{
lean_object* x_191; 
if (x_190 == 0)
{
lean_ctor_set(x_189, 0, x_184);
x_191 = x_189;
goto block_193;
}
else
{
lean_object* x_194; 
x_194 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_194, 0, x_184);
lean_ctor_set(x_194, 1, x_185);
lean_ctor_set(x_194, 2, x_186);
lean_ctor_set(x_194, 3, x_187);
lean_ctor_set(x_194, 4, x_188);
x_191 = x_194;
goto block_193;
}
block_193:
{
lean_object* x_192; 
x_192 = lean_st_ref_set(x_9, x_191);
x_60 = x_7;
x_61 = x_8;
x_62 = x_9;
x_63 = x_10;
x_64 = x_11;
goto block_166;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; 
lean_dec(x_172);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_198 = l_Lean_mkBVar(x_6);
if (x_176 == 0)
{
lean_ctor_set(x_175, 0, x_198);
x_199 = x_175;
goto block_200;
}
else
{
lean_object* x_201; 
x_201 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_201, 0, x_198);
x_199 = x_201;
goto block_200;
}
block_200:
{
return x_199;
}
}
}
}
}
else
{
lean_object* x_204; lean_object* x_205; uint8_t x_206; uint8_t x_211; 
lean_dec(x_172);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_204 = lean_ctor_get(x_173, 0);
x_211 = !lean_is_exclusive(x_173);
if (x_211 == 0)
{
x_205 = x_173;
x_206 = x_211;
goto block_210;
}
else
{
lean_inc(x_204);
lean_dec(x_173);
x_205 = lean_box(0);
x_206 = x_211;
goto block_210;
}
block_210:
{
lean_object* x_207; 
if (x_206 == 0)
{
x_207 = x_205;
goto block_208;
}
else
{
lean_object* x_209; 
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_204);
x_207 = x_209;
goto block_208;
}
block_208:
{
return x_207;
}
}
}
}
}
else
{
x_60 = x_7;
x_61 = x_8;
x_62 = x_9;
x_63 = x_10;
x_64 = x_11;
goto block_166;
}
}
}
else
{
x_60 = x_7;
x_61 = x_8;
x_62 = x_9;
x_63 = x_10;
x_64 = x_11;
goto block_166;
}
block_19:
{
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_5);
x_16 = l_Lean_Expr_app___override(x_14, x_13);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_object* x_18; 
lean_dec_ref(x_14);
lean_dec_ref(x_13);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_5);
return x_18;
}
}
block_35:
{
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_23);
lean_dec_ref(x_5);
x_27 = l_Lean_Expr_letE___override(x_25, x_21, x_24, x_22, x_20);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
size_t x_29; size_t x_30; uint8_t x_31; 
x_29 = lean_ptr_addr(x_23);
lean_dec_ref(x_23);
x_30 = lean_ptr_addr(x_22);
x_31 = lean_usize_dec_eq(x_29, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_5);
x_32 = l_Lean_Expr_letE___override(x_25, x_21, x_24, x_22, x_20);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_5);
return x_34;
}
}
}
block_47:
{
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec_ref(x_5);
x_41 = l_Lean_Expr_lam___override(x_37, x_38, x_39, x_36);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = l_Lean_instBEqBinderInfo_beq(x_36, x_36);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_5);
x_44 = l_Lean_Expr_lam___override(x_37, x_38, x_39, x_36);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
lean_object* x_46; 
lean_dec_ref(x_39);
lean_dec_ref(x_38);
lean_dec(x_37);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_5);
return x_46;
}
}
}
block_59:
{
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_5);
x_53 = l_Lean_Expr_forallE___override(x_50, x_51, x_48, x_49);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_53);
return x_54;
}
else
{
uint8_t x_55; 
x_55 = l_Lean_instBEqBinderInfo_beq(x_49, x_49);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec_ref(x_5);
x_56 = l_Lean_Expr_forallE___override(x_50, x_51, x_48, x_49);
x_57 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
else
{
lean_object* x_58; 
lean_dec_ref(x_51);
lean_dec(x_50);
lean_dec_ref(x_48);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_5);
return x_58;
}
}
}
block_166:
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_5, 0);
x_66 = lean_ctor_get(x_5, 1);
lean_inc(x_64);
lean_inc_ref(x_63);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_6);
lean_inc_ref(x_65);
lean_inc_ref(x_1);
x_67 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_65, x_6, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
lean_inc_ref(x_66);
x_69 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_66, x_6, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; size_t x_71; size_t x_72; uint8_t x_73; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_71 = lean_ptr_addr(x_65);
x_72 = lean_ptr_addr(x_68);
x_73 = lean_usize_dec_eq(x_71, x_72);
if (x_73 == 0)
{
x_13 = x_70;
x_14 = x_68;
x_15 = x_73;
goto block_19;
}
else
{
size_t x_74; size_t x_75; uint8_t x_76; 
x_74 = lean_ptr_addr(x_66);
x_75 = lean_ptr_addr(x_70);
x_76 = lean_usize_dec_eq(x_74, x_75);
x_13 = x_70;
x_14 = x_68;
x_15 = x_76;
goto block_19;
}
}
else
{
lean_dec(x_68);
lean_dec_ref(x_5);
return x_69;
}
}
else
{
lean_dec_ref(x_5);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_67;
}
}
case 10:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_5, 0);
x_78 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_78);
x_79 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_78, x_6, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_94; 
x_80 = lean_ctor_get(x_79, 0);
x_94 = !lean_is_exclusive(x_79);
if (x_94 == 0)
{
x_81 = x_79;
x_82 = x_94;
goto block_93;
}
else
{
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_box(0);
x_82 = x_94;
goto block_93;
}
block_93:
{
size_t x_83; size_t x_84; uint8_t x_85; 
x_83 = lean_ptr_addr(x_78);
x_84 = lean_ptr_addr(x_80);
x_85 = lean_usize_dec_eq(x_83, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_inc(x_77);
lean_dec_ref(x_5);
x_86 = l_Lean_Expr_mdata___override(x_77, x_80);
if (x_82 == 0)
{
lean_ctor_set(x_81, 0, x_86);
x_87 = x_81;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_86);
x_87 = x_89;
goto block_88;
}
block_88:
{
return x_87;
}
}
else
{
lean_object* x_90; 
lean_dec(x_80);
if (x_82 == 0)
{
lean_ctor_set(x_81, 0, x_5);
x_90 = x_81;
goto block_91;
}
else
{
lean_object* x_92; 
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_5);
x_90 = x_92;
goto block_91;
}
block_91:
{
return x_90;
}
}
}
}
else
{
lean_dec_ref(x_5);
return x_79;
}
}
case 11:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_5, 0);
x_96 = lean_ctor_get(x_5, 1);
x_97 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_97);
x_98 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_97, x_6, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_113; 
x_99 = lean_ctor_get(x_98, 0);
x_113 = !lean_is_exclusive(x_98);
if (x_113 == 0)
{
x_100 = x_98;
x_101 = x_113;
goto block_112;
}
else
{
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_box(0);
x_101 = x_113;
goto block_112;
}
block_112:
{
size_t x_102; size_t x_103; uint8_t x_104; 
x_102 = lean_ptr_addr(x_97);
x_103 = lean_ptr_addr(x_99);
x_104 = lean_usize_dec_eq(x_102, x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_inc(x_96);
lean_inc(x_95);
lean_dec_ref(x_5);
x_105 = l_Lean_Expr_proj___override(x_95, x_96, x_99);
if (x_101 == 0)
{
lean_ctor_set(x_100, 0, x_105);
x_106 = x_100;
goto block_107;
}
else
{
lean_object* x_108; 
x_108 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_108, 0, x_105);
x_106 = x_108;
goto block_107;
}
block_107:
{
return x_106;
}
}
else
{
lean_object* x_109; 
lean_dec(x_99);
if (x_101 == 0)
{
lean_ctor_set(x_100, 0, x_5);
x_109 = x_100;
goto block_110;
}
else
{
lean_object* x_111; 
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_5);
x_109 = x_111;
goto block_110;
}
block_110:
{
return x_109;
}
}
}
}
else
{
lean_dec_ref(x_5);
return x_98;
}
}
case 8:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; 
x_114 = lean_ctor_get(x_5, 0);
x_115 = lean_ctor_get(x_5, 1);
x_116 = lean_ctor_get(x_5, 2);
x_117 = lean_ctor_get(x_5, 3);
x_118 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_64);
lean_inc_ref(x_63);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_6);
lean_inc_ref(x_115);
lean_inc_ref(x_1);
x_119 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_115, x_6, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
lean_inc(x_64);
lean_inc_ref(x_63);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_6);
lean_inc_ref(x_116);
lean_inc_ref(x_1);
x_121 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_116, x_6, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
lean_dec_ref(x_121);
x_123 = lean_unsigned_to_nat(1u);
x_124 = lean_nat_add(x_6, x_123);
lean_dec(x_6);
lean_inc_ref(x_117);
x_125 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_117, x_124, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; size_t x_127; size_t x_128; uint8_t x_129; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = lean_ptr_addr(x_115);
x_128 = lean_ptr_addr(x_120);
x_129 = lean_usize_dec_eq(x_127, x_128);
if (x_129 == 0)
{
lean_inc(x_114);
lean_inc_ref(x_117);
x_20 = x_118;
x_21 = x_120;
x_22 = x_126;
x_23 = x_117;
x_24 = x_122;
x_25 = x_114;
x_26 = x_129;
goto block_35;
}
else
{
size_t x_130; size_t x_131; uint8_t x_132; 
x_130 = lean_ptr_addr(x_116);
x_131 = lean_ptr_addr(x_122);
x_132 = lean_usize_dec_eq(x_130, x_131);
lean_inc(x_114);
lean_inc_ref(x_117);
x_20 = x_118;
x_21 = x_120;
x_22 = x_126;
x_23 = x_117;
x_24 = x_122;
x_25 = x_114;
x_26 = x_132;
goto block_35;
}
}
else
{
lean_dec(x_122);
lean_dec(x_120);
lean_dec_ref(x_5);
return x_125;
}
}
else
{
lean_dec(x_120);
lean_dec_ref(x_5);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_121;
}
}
else
{
lean_dec_ref(x_5);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_119;
}
}
case 6:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_5, 0);
x_134 = lean_ctor_get(x_5, 1);
x_135 = lean_ctor_get(x_5, 2);
x_136 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_64);
lean_inc_ref(x_63);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_6);
lean_inc_ref(x_134);
lean_inc_ref(x_1);
x_137 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_134, x_6, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
x_139 = lean_unsigned_to_nat(1u);
x_140 = lean_nat_add(x_6, x_139);
lean_dec(x_6);
lean_inc_ref(x_135);
x_141 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_135, x_140, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; size_t x_143; size_t x_144; uint8_t x_145; 
x_142 = lean_ctor_get(x_141, 0);
lean_inc(x_142);
lean_dec_ref(x_141);
x_143 = lean_ptr_addr(x_134);
x_144 = lean_ptr_addr(x_138);
x_145 = lean_usize_dec_eq(x_143, x_144);
if (x_145 == 0)
{
lean_inc(x_133);
x_36 = x_136;
x_37 = x_133;
x_38 = x_138;
x_39 = x_142;
x_40 = x_145;
goto block_47;
}
else
{
size_t x_146; size_t x_147; uint8_t x_148; 
x_146 = lean_ptr_addr(x_135);
x_147 = lean_ptr_addr(x_142);
x_148 = lean_usize_dec_eq(x_146, x_147);
lean_inc(x_133);
x_36 = x_136;
x_37 = x_133;
x_38 = x_138;
x_39 = x_142;
x_40 = x_148;
goto block_47;
}
}
else
{
lean_dec(x_138);
lean_dec_ref(x_5);
return x_141;
}
}
else
{
lean_dec_ref(x_5);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_137;
}
}
case 7:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; 
x_149 = lean_ctor_get(x_5, 0);
x_150 = lean_ctor_get(x_5, 1);
x_151 = lean_ctor_get(x_5, 2);
x_152 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_64);
lean_inc_ref(x_63);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_6);
lean_inc_ref(x_150);
lean_inc_ref(x_1);
x_153 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_150, x_6, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
lean_dec_ref(x_153);
x_155 = lean_unsigned_to_nat(1u);
x_156 = lean_nat_add(x_6, x_155);
lean_dec(x_6);
lean_inc_ref(x_151);
x_157 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_151, x_156, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; size_t x_159; size_t x_160; uint8_t x_161; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
lean_dec_ref(x_157);
x_159 = lean_ptr_addr(x_150);
x_160 = lean_ptr_addr(x_154);
x_161 = lean_usize_dec_eq(x_159, x_160);
if (x_161 == 0)
{
lean_inc(x_149);
x_48 = x_158;
x_49 = x_152;
x_50 = x_149;
x_51 = x_154;
x_52 = x_161;
goto block_59;
}
else
{
size_t x_162; size_t x_163; uint8_t x_164; 
x_162 = lean_ptr_addr(x_151);
x_163 = lean_ptr_addr(x_158);
x_164 = lean_usize_dec_eq(x_162, x_163);
lean_inc(x_149);
x_48 = x_158;
x_49 = x_152;
x_50 = x_149;
x_51 = x_154;
x_52 = x_164;
goto block_59;
}
}
else
{
lean_dec(x_154);
lean_dec_ref(x_5);
return x_157;
}
}
else
{
lean_dec_ref(x_5);
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_153;
}
}
default: 
{
lean_object* x_165; 
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_6);
lean_dec_ref(x_1);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_5);
return x_165;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_24; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = lean_ctor_get(x_11, 1);
x_13 = lean_ctor_get(x_11, 2);
x_14 = lean_ctor_get(x_11, 3);
x_15 = lean_ctor_get(x_11, 4);
x_24 = !lean_is_exclusive(x_11);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_11, 0);
lean_dec(x_25);
x_16 = x_11;
x_17 = x_24;
goto block_23;
}
else
{
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_18; 
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_10);
x_18 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_22, 0, x_10);
lean_ctor_set(x_22, 1, x_12);
lean_ctor_set(x_22, 2, x_13);
lean_ctor_set(x_22, 3, x_14);
lean_ctor_set(x_22, 4, x_15);
x_18 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_st_ref_set(x_2, x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_9);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_41; 
x_9 = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(x_1, x_5);
x_10 = lean_ctor_get(x_9, 0);
x_41 = !lean_is_exclusive(x_9);
if (x_41 == 0)
{
x_11 = x_9;
x_12 = x_41;
goto block_40;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_41;
goto block_40;
}
block_40:
{
uint8_t x_13; uint8_t x_37; 
x_37 = l_Lean_Expr_isFVar(x_2);
if (x_37 == 0)
{
x_13 = x_37;
goto block_36;
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_box(0);
lean_inc(x_3);
x_39 = l_Lean_Meta_instBEqOccurrences_beq(x_3, x_38);
x_13 = x_39;
goto block_36;
}
block_36:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_del_object(x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_st_mk_ref(x_14);
lean_inc_ref(x_2);
x_16 = l_Lean_Expr_toHeadIndex(x_2);
x_17 = l_Lean_Expr_headNumArgs(x_2);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_2, x_3, x_16, x_17, x_10, x_18, x_15, x_4, x_5, x_6, x_7);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_3);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_28; 
x_20 = lean_ctor_get(x_19, 0);
x_28 = !lean_is_exclusive(x_19);
if (x_28 == 0)
{
x_21 = x_19;
x_22 = x_28;
goto block_27;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_st_ref_get(x_15);
lean_dec(x_15);
lean_dec(x_23);
if (x_22 == 0)
{
x_24 = x_21;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_20);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
else
{
lean_dec(x_15);
return x_19;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_mk_empty_array_with_capacity(x_29);
x_31 = lean_array_push(x_30, x_2);
x_32 = lean_expr_abstract(x_10, x_31);
lean_dec_ref(x_31);
lean_dec(x_10);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_32);
x_33 = x_11;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_32);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_kabstract(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* runtime_initialize_Lean_HeadIndex(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_KAbstract(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_HeadIndex(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_KAbstract(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_HeadIndex(uint8_t builtin);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_HeadIndex(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_KAbstract(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_KAbstract(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_KAbstract(builtin);
}
#ifdef __cplusplus
}
#endif
