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
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_56; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_172; 
x_172 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_172 == 0)
{
lean_object* x_173; uint8_t x_174; 
lean_inc_ref(x_5);
x_173 = l_Lean_Expr_toHeadIndex(x_5);
x_174 = l_Lean_instBEqHeadIndex_beq(x_173, x_3);
lean_dec(x_173);
if (x_174 == 0)
{
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = lean_box(0);
goto block_171;
}
else
{
if (x_172 == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = l_Lean_Expr_headNumArgs(x_5);
x_176 = lean_nat_dec_eq(x_175, x_4);
lean_dec(x_175);
if (x_176 == 0)
{
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = lean_box(0);
goto block_171;
}
else
{
lean_object* x_177; lean_object* x_178; 
x_177 = lean_st_ref_get(x_9);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc_ref(x_5);
x_178 = l_Lean_Meta_isExprDefEq(x_5, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; uint8_t x_208; 
x_179 = lean_ctor_get(x_178, 0);
x_208 = !lean_is_exclusive(x_178);
if (x_208 == 0)
{
x_180 = x_178;
x_181 = x_208;
goto block_207;
}
else
{
lean_inc(x_179);
lean_dec(x_178);
x_180 = lean_box(0);
x_181 = x_208;
goto block_207;
}
block_207:
{
uint8_t x_182; 
x_182 = lean_unbox(x_179);
lean_dec(x_179);
if (x_182 == 0)
{
lean_del_object(x_180);
lean_dec(x_177);
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = lean_box(0);
goto block_171;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; uint8_t x_187; 
x_183 = lean_st_ref_get(x_7);
x_184 = lean_unsigned_to_nat(1u);
x_185 = lean_nat_add(x_183, x_184);
x_186 = lean_st_ref_set(x_7, x_185);
x_187 = l_Lean_Meta_Occurrences_contains(x_2, x_183);
lean_dec(x_183);
if (x_187 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; uint8_t x_201; 
lean_del_object(x_180);
x_188 = lean_st_ref_take(x_9);
x_189 = lean_ctor_get(x_177, 0);
lean_inc_ref(x_189);
lean_dec(x_177);
x_190 = lean_ctor_get(x_188, 1);
x_191 = lean_ctor_get(x_188, 2);
x_192 = lean_ctor_get(x_188, 3);
x_193 = lean_ctor_get(x_188, 4);
x_201 = !lean_is_exclusive(x_188);
if (x_201 == 0)
{
lean_object* x_202; 
x_202 = lean_ctor_get(x_188, 0);
lean_dec(x_202);
x_194 = x_188;
x_195 = x_201;
goto block_200;
}
else
{
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_188);
x_194 = lean_box(0);
x_195 = x_201;
goto block_200;
}
block_200:
{
lean_object* x_196; 
if (x_195 == 0)
{
lean_ctor_set(x_194, 0, x_189);
x_196 = x_194;
goto block_198;
}
else
{
lean_object* x_199; 
x_199 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_199, 0, x_189);
lean_ctor_set(x_199, 1, x_190);
lean_ctor_set(x_199, 2, x_191);
lean_ctor_set(x_199, 3, x_192);
lean_ctor_set(x_199, 4, x_193);
x_196 = x_199;
goto block_198;
}
block_198:
{
lean_object* x_197; 
x_197 = lean_st_ref_set(x_9, x_196);
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = lean_box(0);
goto block_171;
}
}
}
else
{
lean_object* x_203; lean_object* x_204; 
lean_dec(x_177);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_203 = l_Lean_mkBVar(x_6);
if (x_181 == 0)
{
lean_ctor_set(x_180, 0, x_203);
x_204 = x_180;
goto block_205;
}
else
{
lean_object* x_206; 
x_206 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_206, 0, x_203);
x_204 = x_206;
goto block_205;
}
block_205:
{
return x_204;
}
}
}
}
}
else
{
lean_object* x_209; lean_object* x_210; uint8_t x_211; uint8_t x_216; 
lean_dec(x_177);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_209 = lean_ctor_get(x_178, 0);
x_216 = !lean_is_exclusive(x_178);
if (x_216 == 0)
{
x_210 = x_178;
x_211 = x_216;
goto block_215;
}
else
{
lean_inc(x_209);
lean_dec(x_178);
x_210 = lean_box(0);
x_211 = x_216;
goto block_215;
}
block_215:
{
lean_object* x_212; 
if (x_211 == 0)
{
x_212 = x_210;
goto block_213;
}
else
{
lean_object* x_214; 
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_209);
x_212 = x_214;
goto block_213;
}
block_213:
{
return x_212;
}
}
}
}
}
else
{
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = lean_box(0);
goto block_171;
}
}
}
else
{
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = lean_box(0);
goto block_171;
}
block_20:
{
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_5);
x_17 = l_Lean_Expr_app___override(x_13, x_14);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec_ref(x_14);
lean_dec_ref(x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_5);
return x_19;
}
}
block_37:
{
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_26);
lean_dec_ref(x_5);
x_29 = l_Lean_Expr_letE___override(x_25, x_24, x_23, x_27, x_22);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
else
{
size_t x_31; size_t x_32; uint8_t x_33; 
x_31 = lean_ptr_addr(x_26);
lean_dec_ref(x_26);
x_32 = lean_ptr_addr(x_27);
x_33 = lean_usize_dec_eq(x_31, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec_ref(x_5);
x_34 = l_Lean_Expr_letE___override(x_25, x_24, x_23, x_27, x_22);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
else
{
lean_object* x_36; 
lean_dec_ref(x_27);
lean_dec(x_25);
lean_dec_ref(x_24);
lean_dec_ref(x_23);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_5);
return x_36;
}
}
}
block_50:
{
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec_ref(x_5);
x_44 = l_Lean_Expr_lam___override(x_40, x_38, x_42, x_39);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_44);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = l_Lean_instBEqBinderInfo_beq(x_39, x_39);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_5);
x_47 = l_Lean_Expr_lam___override(x_40, x_38, x_42, x_39);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
else
{
lean_object* x_49; 
lean_dec_ref(x_42);
lean_dec(x_40);
lean_dec_ref(x_38);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_5);
return x_49;
}
}
}
block_63:
{
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
lean_dec_ref(x_5);
x_57 = l_Lean_Expr_forallE___override(x_54, x_51, x_53, x_55);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_57);
return x_58;
}
else
{
uint8_t x_59; 
x_59 = l_Lean_instBEqBinderInfo_beq(x_55, x_55);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_5);
x_60 = l_Lean_Expr_forallE___override(x_54, x_51, x_53, x_55);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
else
{
lean_object* x_62; 
lean_dec(x_54);
lean_dec_ref(x_53);
lean_dec_ref(x_51);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_5);
return x_62;
}
}
}
block_171:
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_5, 0);
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_68);
lean_inc_ref(x_67);
lean_inc(x_66);
lean_inc_ref(x_65);
lean_inc(x_6);
lean_inc_ref(x_70);
lean_inc_ref(x_1);
x_72 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_70, x_6, x_64, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
lean_inc_ref(x_71);
x_74 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_71, x_6, x_64, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; size_t x_76; size_t x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
lean_dec_ref(x_74);
x_76 = lean_ptr_addr(x_70);
x_77 = lean_ptr_addr(x_73);
x_78 = lean_usize_dec_eq(x_76, x_77);
if (x_78 == 0)
{
x_13 = x_73;
x_14 = x_75;
x_15 = lean_box(0);
x_16 = x_78;
goto block_20;
}
else
{
size_t x_79; size_t x_80; uint8_t x_81; 
x_79 = lean_ptr_addr(x_71);
x_80 = lean_ptr_addr(x_75);
x_81 = lean_usize_dec_eq(x_79, x_80);
x_13 = x_73;
x_14 = x_75;
x_15 = lean_box(0);
x_16 = x_81;
goto block_20;
}
}
else
{
lean_dec(x_73);
lean_dec_ref(x_5);
return x_74;
}
}
else
{
lean_dec_ref(x_5);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_72;
}
}
case 10:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_5, 0);
x_83 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_83);
x_84 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_83, x_6, x_64, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; uint8_t x_99; 
x_85 = lean_ctor_get(x_84, 0);
x_99 = !lean_is_exclusive(x_84);
if (x_99 == 0)
{
x_86 = x_84;
x_87 = x_99;
goto block_98;
}
else
{
lean_inc(x_85);
lean_dec(x_84);
x_86 = lean_box(0);
x_87 = x_99;
goto block_98;
}
block_98:
{
size_t x_88; size_t x_89; uint8_t x_90; 
x_88 = lean_ptr_addr(x_83);
x_89 = lean_ptr_addr(x_85);
x_90 = lean_usize_dec_eq(x_88, x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_inc(x_82);
lean_dec_ref(x_5);
x_91 = l_Lean_Expr_mdata___override(x_82, x_85);
if (x_87 == 0)
{
lean_ctor_set(x_86, 0, x_91);
x_92 = x_86;
goto block_93;
}
else
{
lean_object* x_94; 
x_94 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_94, 0, x_91);
x_92 = x_94;
goto block_93;
}
block_93:
{
return x_92;
}
}
else
{
lean_object* x_95; 
lean_dec(x_85);
if (x_87 == 0)
{
lean_ctor_set(x_86, 0, x_5);
x_95 = x_86;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_5);
x_95 = x_97;
goto block_96;
}
block_96:
{
return x_95;
}
}
}
}
else
{
lean_dec_ref(x_5);
return x_84;
}
}
case 11:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_5, 0);
x_101 = lean_ctor_get(x_5, 1);
x_102 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_102);
x_103 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_102, x_6, x_64, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_118; 
x_104 = lean_ctor_get(x_103, 0);
x_118 = !lean_is_exclusive(x_103);
if (x_118 == 0)
{
x_105 = x_103;
x_106 = x_118;
goto block_117;
}
else
{
lean_inc(x_104);
lean_dec(x_103);
x_105 = lean_box(0);
x_106 = x_118;
goto block_117;
}
block_117:
{
size_t x_107; size_t x_108; uint8_t x_109; 
x_107 = lean_ptr_addr(x_102);
x_108 = lean_ptr_addr(x_104);
x_109 = lean_usize_dec_eq(x_107, x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_inc(x_101);
lean_inc(x_100);
lean_dec_ref(x_5);
x_110 = l_Lean_Expr_proj___override(x_100, x_101, x_104);
if (x_106 == 0)
{
lean_ctor_set(x_105, 0, x_110);
x_111 = x_105;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_110);
x_111 = x_113;
goto block_112;
}
block_112:
{
return x_111;
}
}
else
{
lean_object* x_114; 
lean_dec(x_104);
if (x_106 == 0)
{
lean_ctor_set(x_105, 0, x_5);
x_114 = x_105;
goto block_115;
}
else
{
lean_object* x_116; 
x_116 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_116, 0, x_5);
x_114 = x_116;
goto block_115;
}
block_115:
{
return x_114;
}
}
}
}
else
{
lean_dec_ref(x_5);
return x_103;
}
}
case 8:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_119 = lean_ctor_get(x_5, 0);
x_120 = lean_ctor_get(x_5, 1);
x_121 = lean_ctor_get(x_5, 2);
x_122 = lean_ctor_get(x_5, 3);
x_123 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_68);
lean_inc_ref(x_67);
lean_inc(x_66);
lean_inc_ref(x_65);
lean_inc(x_6);
lean_inc_ref(x_120);
lean_inc_ref(x_1);
x_124 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_120, x_6, x_64, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
lean_dec_ref(x_124);
lean_inc(x_68);
lean_inc_ref(x_67);
lean_inc(x_66);
lean_inc_ref(x_65);
lean_inc(x_6);
lean_inc_ref(x_121);
lean_inc_ref(x_1);
x_126 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_121, x_6, x_64, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
lean_dec_ref(x_126);
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_nat_add(x_6, x_128);
lean_dec(x_6);
lean_inc_ref(x_122);
x_130 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_122, x_129, x_64, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; size_t x_132; size_t x_133; uint8_t x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
lean_dec_ref(x_130);
x_132 = lean_ptr_addr(x_120);
x_133 = lean_ptr_addr(x_125);
x_134 = lean_usize_dec_eq(x_132, x_133);
if (x_134 == 0)
{
lean_inc_ref(x_122);
lean_inc(x_119);
x_21 = lean_box(0);
x_22 = x_123;
x_23 = x_127;
x_24 = x_125;
x_25 = x_119;
x_26 = x_122;
x_27 = x_131;
x_28 = x_134;
goto block_37;
}
else
{
size_t x_135; size_t x_136; uint8_t x_137; 
x_135 = lean_ptr_addr(x_121);
x_136 = lean_ptr_addr(x_127);
x_137 = lean_usize_dec_eq(x_135, x_136);
lean_inc_ref(x_122);
lean_inc(x_119);
x_21 = lean_box(0);
x_22 = x_123;
x_23 = x_127;
x_24 = x_125;
x_25 = x_119;
x_26 = x_122;
x_27 = x_131;
x_28 = x_137;
goto block_37;
}
}
else
{
lean_dec(x_127);
lean_dec(x_125);
lean_dec_ref(x_5);
return x_130;
}
}
else
{
lean_dec(x_125);
lean_dec_ref(x_5);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_126;
}
}
else
{
lean_dec_ref(x_5);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_124;
}
}
case 6:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_5, 0);
x_139 = lean_ctor_get(x_5, 1);
x_140 = lean_ctor_get(x_5, 2);
x_141 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_68);
lean_inc_ref(x_67);
lean_inc(x_66);
lean_inc_ref(x_65);
lean_inc(x_6);
lean_inc_ref(x_139);
lean_inc_ref(x_1);
x_142 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_139, x_6, x_64, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
lean_dec_ref(x_142);
x_144 = lean_unsigned_to_nat(1u);
x_145 = lean_nat_add(x_6, x_144);
lean_dec(x_6);
lean_inc_ref(x_140);
x_146 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_140, x_145, x_64, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_146) == 0)
{
lean_object* x_147; size_t x_148; size_t x_149; uint8_t x_150; 
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
lean_dec_ref(x_146);
x_148 = lean_ptr_addr(x_139);
x_149 = lean_ptr_addr(x_143);
x_150 = lean_usize_dec_eq(x_148, x_149);
if (x_150 == 0)
{
lean_inc(x_138);
x_38 = x_143;
x_39 = x_141;
x_40 = x_138;
x_41 = lean_box(0);
x_42 = x_147;
x_43 = x_150;
goto block_50;
}
else
{
size_t x_151; size_t x_152; uint8_t x_153; 
x_151 = lean_ptr_addr(x_140);
x_152 = lean_ptr_addr(x_147);
x_153 = lean_usize_dec_eq(x_151, x_152);
lean_inc(x_138);
x_38 = x_143;
x_39 = x_141;
x_40 = x_138;
x_41 = lean_box(0);
x_42 = x_147;
x_43 = x_153;
goto block_50;
}
}
else
{
lean_dec(x_143);
lean_dec_ref(x_5);
return x_146;
}
}
else
{
lean_dec_ref(x_5);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_142;
}
}
case 7:
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; lean_object* x_158; 
x_154 = lean_ctor_get(x_5, 0);
x_155 = lean_ctor_get(x_5, 1);
x_156 = lean_ctor_get(x_5, 2);
x_157 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_68);
lean_inc_ref(x_67);
lean_inc(x_66);
lean_inc_ref(x_65);
lean_inc(x_6);
lean_inc_ref(x_155);
lean_inc_ref(x_1);
x_158 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_155, x_6, x_64, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_158) == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
lean_dec_ref(x_158);
x_160 = lean_unsigned_to_nat(1u);
x_161 = lean_nat_add(x_6, x_160);
lean_dec(x_6);
lean_inc_ref(x_156);
x_162 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_156, x_161, x_64, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; size_t x_164; size_t x_165; uint8_t x_166; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
lean_dec_ref(x_162);
x_164 = lean_ptr_addr(x_155);
x_165 = lean_ptr_addr(x_159);
x_166 = lean_usize_dec_eq(x_164, x_165);
if (x_166 == 0)
{
lean_inc(x_154);
x_51 = x_159;
x_52 = lean_box(0);
x_53 = x_163;
x_54 = x_154;
x_55 = x_157;
x_56 = x_166;
goto block_63;
}
else
{
size_t x_167; size_t x_168; uint8_t x_169; 
x_167 = lean_ptr_addr(x_156);
x_168 = lean_ptr_addr(x_163);
x_169 = lean_usize_dec_eq(x_167, x_168);
lean_inc(x_154);
x_51 = x_159;
x_52 = lean_box(0);
x_53 = x_163;
x_54 = x_154;
x_55 = x_157;
x_56 = x_169;
goto block_63;
}
}
else
{
lean_dec(x_159);
lean_dec_ref(x_5);
return x_162;
}
}
else
{
lean_dec_ref(x_5);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_6);
lean_dec_ref(x_1);
return x_158;
}
}
default: 
{
lean_object* x_170; 
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_6);
lean_dec_ref(x_1);
x_170 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_170, 0, x_5);
return x_170;
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
