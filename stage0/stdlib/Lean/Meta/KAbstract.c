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
static lean_object* l_Lean_Meta_kabstract___closed__0;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Meta_instBEqOccurrences_beq(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_headNumArgs(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqHeadIndex_beq(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Occurrences_contains(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_26; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_168; 
x_168 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_168 == 0)
{
lean_object* x_169; uint8_t x_170; 
lean_inc_ref(x_5);
x_169 = l_Lean_Expr_toHeadIndex(x_5);
x_170 = l_Lean_instBEqHeadIndex_beq(x_169, x_3);
lean_dec(x_169);
if (x_170 == 0)
{
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = lean_box(0);
goto block_167;
}
else
{
if (x_168 == 0)
{
lean_object* x_171; uint8_t x_172; 
x_171 = l_Lean_Expr_headNumArgs(x_5);
x_172 = lean_nat_dec_eq(x_171, x_4);
lean_dec(x_171);
if (x_172 == 0)
{
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = lean_box(0);
goto block_167;
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_st_ref_get(x_9);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc_ref(x_5);
x_174 = l_Lean_Meta_isExprDefEq(x_5, x_1, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_174) == 0)
{
uint8_t x_175; 
x_175 = !lean_is_exclusive(x_174);
if (x_175 == 0)
{
lean_object* x_176; uint8_t x_177; 
x_176 = lean_ctor_get(x_174, 0);
x_177 = lean_unbox(x_176);
lean_dec(x_176);
if (x_177 == 0)
{
lean_free_object(x_174);
lean_dec_ref(x_173);
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = lean_box(0);
goto block_167;
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
lean_object* x_183; lean_object* x_184; uint8_t x_185; 
lean_free_object(x_174);
x_183 = lean_st_ref_take(x_9);
x_184 = lean_ctor_get(x_173, 0);
lean_inc_ref(x_184);
lean_dec_ref(x_173);
x_185 = !lean_is_exclusive(x_183);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_183, 0);
lean_dec(x_186);
lean_ctor_set(x_183, 0, x_184);
x_187 = lean_st_ref_set(x_9, x_183);
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = lean_box(0);
goto block_167;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_188 = lean_ctor_get(x_183, 1);
x_189 = lean_ctor_get(x_183, 2);
x_190 = lean_ctor_get(x_183, 3);
x_191 = lean_ctor_get(x_183, 4);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_183);
x_192 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_192, 0, x_184);
lean_ctor_set(x_192, 1, x_188);
lean_ctor_set(x_192, 2, x_189);
lean_ctor_set(x_192, 3, x_190);
lean_ctor_set(x_192, 4, x_191);
x_193 = lean_st_ref_set(x_9, x_192);
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = lean_box(0);
goto block_167;
}
}
else
{
lean_object* x_194; 
lean_dec_ref(x_173);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_194 = l_Lean_mkBVar(x_6);
lean_ctor_set(x_174, 0, x_194);
return x_174;
}
}
}
else
{
lean_object* x_195; uint8_t x_196; 
x_195 = lean_ctor_get(x_174, 0);
lean_inc(x_195);
lean_dec(x_174);
x_196 = lean_unbox(x_195);
lean_dec(x_195);
if (x_196 == 0)
{
lean_dec_ref(x_173);
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = lean_box(0);
goto block_167;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_197 = lean_st_ref_get(x_7);
x_198 = lean_unsigned_to_nat(1u);
x_199 = lean_nat_add(x_197, x_198);
x_200 = lean_st_ref_set(x_7, x_199);
x_201 = l_Lean_Meta_Occurrences_contains(x_2, x_197);
lean_dec(x_197);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_202 = lean_st_ref_take(x_9);
x_203 = lean_ctor_get(x_173, 0);
lean_inc_ref(x_203);
lean_dec_ref(x_173);
x_204 = lean_ctor_get(x_202, 1);
lean_inc_ref(x_204);
x_205 = lean_ctor_get(x_202, 2);
lean_inc(x_205);
x_206 = lean_ctor_get(x_202, 3);
lean_inc_ref(x_206);
x_207 = lean_ctor_get(x_202, 4);
lean_inc_ref(x_207);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 lean_ctor_release(x_202, 2);
 lean_ctor_release(x_202, 3);
 lean_ctor_release(x_202, 4);
 x_208 = x_202;
} else {
 lean_dec_ref(x_202);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(0, 5, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_203);
lean_ctor_set(x_209, 1, x_204);
lean_ctor_set(x_209, 2, x_205);
lean_ctor_set(x_209, 3, x_206);
lean_ctor_set(x_209, 4, x_207);
x_210 = lean_st_ref_set(x_9, x_209);
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = lean_box(0);
goto block_167;
}
else
{
lean_object* x_211; lean_object* x_212; 
lean_dec_ref(x_173);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_211 = l_Lean_mkBVar(x_6);
x_212 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_212, 0, x_211);
return x_212;
}
}
}
}
else
{
uint8_t x_213; 
lean_dec_ref(x_173);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_213 = !lean_is_exclusive(x_174);
if (x_213 == 0)
{
return x_174;
}
else
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_174, 0);
lean_inc(x_214);
lean_dec(x_174);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_214);
return x_215;
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
goto block_167;
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
goto block_167;
}
block_20:
{
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec_ref(x_5);
x_17 = l_Lean_Expr_app___override(x_15, x_13);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec_ref(x_15);
lean_dec_ref(x_13);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_5);
return x_19;
}
}
block_33:
{
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec_ref(x_5);
x_27 = l_Lean_Expr_lam___override(x_23, x_22, x_21, x_25);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = l_Lean_instBEqBinderInfo_beq(x_25, x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec_ref(x_5);
x_30 = l_Lean_Expr_lam___override(x_23, x_22, x_21, x_25);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_23);
lean_dec_ref(x_22);
lean_dec_ref(x_21);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_5);
return x_32;
}
}
}
block_46:
{
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec_ref(x_5);
x_40 = l_Lean_Expr_forallE___override(x_34, x_37, x_38, x_36);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = l_Lean_instBEqBinderInfo_beq(x_36, x_36);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_5);
x_43 = l_Lean_Expr_forallE___override(x_34, x_37, x_38, x_36);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
else
{
lean_object* x_45; 
lean_dec_ref(x_38);
lean_dec_ref(x_37);
lean_dec(x_34);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_5);
return x_45;
}
}
}
block_63:
{
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec_ref(x_51);
lean_dec_ref(x_5);
x_55 = l_Lean_Expr_letE___override(x_53, x_47, x_52, x_48, x_50);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
return x_56;
}
else
{
size_t x_57; size_t x_58; uint8_t x_59; 
x_57 = lean_ptr_addr(x_51);
lean_dec_ref(x_51);
x_58 = lean_ptr_addr(x_48);
x_59 = lean_usize_dec_eq(x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_5);
x_60 = l_Lean_Expr_letE___override(x_53, x_47, x_52, x_48, x_50);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
else
{
lean_object* x_62; 
lean_dec(x_53);
lean_dec_ref(x_52);
lean_dec_ref(x_48);
lean_dec_ref(x_47);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_5);
return x_62;
}
}
}
block_167:
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
x_13 = x_75;
x_14 = lean_box(0);
x_15 = x_73;
x_16 = x_78;
goto block_20;
}
else
{
size_t x_79; size_t x_80; uint8_t x_81; 
x_79 = lean_ptr_addr(x_71);
x_80 = lean_ptr_addr(x_75);
x_81 = lean_usize_dec_eq(x_79, x_80);
x_13 = x_75;
x_14 = lean_box(0);
x_15 = x_73;
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
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_72;
}
}
case 6:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_5, 0);
x_83 = lean_ctor_get(x_5, 1);
x_84 = lean_ctor_get(x_5, 2);
x_85 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_68);
lean_inc_ref(x_67);
lean_inc(x_66);
lean_inc_ref(x_65);
lean_inc(x_6);
lean_inc_ref(x_83);
lean_inc_ref(x_1);
x_86 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_83, x_6, x_64, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_nat_add(x_6, x_88);
lean_dec(x_6);
lean_inc_ref(x_84);
x_90 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_84, x_89, x_64, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; size_t x_92; size_t x_93; uint8_t x_94; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec_ref(x_90);
x_92 = lean_ptr_addr(x_83);
x_93 = lean_ptr_addr(x_87);
x_94 = lean_usize_dec_eq(x_92, x_93);
if (x_94 == 0)
{
lean_inc(x_82);
x_21 = x_91;
x_22 = x_87;
x_23 = x_82;
x_24 = lean_box(0);
x_25 = x_85;
x_26 = x_94;
goto block_33;
}
else
{
size_t x_95; size_t x_96; uint8_t x_97; 
x_95 = lean_ptr_addr(x_84);
x_96 = lean_ptr_addr(x_91);
x_97 = lean_usize_dec_eq(x_95, x_96);
lean_inc(x_82);
x_21 = x_91;
x_22 = x_87;
x_23 = x_82;
x_24 = lean_box(0);
x_25 = x_85;
x_26 = x_97;
goto block_33;
}
}
else
{
lean_dec(x_87);
lean_dec_ref(x_5);
return x_90;
}
}
else
{
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_86;
}
}
case 7:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_5, 0);
x_99 = lean_ctor_get(x_5, 1);
x_100 = lean_ctor_get(x_5, 2);
x_101 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_68);
lean_inc_ref(x_67);
lean_inc(x_66);
lean_inc_ref(x_65);
lean_inc(x_6);
lean_inc_ref(x_99);
lean_inc_ref(x_1);
x_102 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_99, x_6, x_64, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
lean_dec_ref(x_102);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_add(x_6, x_104);
lean_dec(x_6);
lean_inc_ref(x_100);
x_106 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_100, x_105, x_64, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; size_t x_108; size_t x_109; uint8_t x_110; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
x_108 = lean_ptr_addr(x_99);
x_109 = lean_ptr_addr(x_103);
x_110 = lean_usize_dec_eq(x_108, x_109);
if (x_110 == 0)
{
lean_inc(x_98);
x_34 = x_98;
x_35 = lean_box(0);
x_36 = x_101;
x_37 = x_103;
x_38 = x_107;
x_39 = x_110;
goto block_46;
}
else
{
size_t x_111; size_t x_112; uint8_t x_113; 
x_111 = lean_ptr_addr(x_100);
x_112 = lean_ptr_addr(x_107);
x_113 = lean_usize_dec_eq(x_111, x_112);
lean_inc(x_98);
x_34 = x_98;
x_35 = lean_box(0);
x_36 = x_101;
x_37 = x_103;
x_38 = x_107;
x_39 = x_113;
goto block_46;
}
}
else
{
lean_dec(x_103);
lean_dec_ref(x_5);
return x_106;
}
}
else
{
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_102;
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
lean_inc(x_68);
lean_inc_ref(x_67);
lean_inc(x_66);
lean_inc_ref(x_65);
lean_inc(x_6);
lean_inc_ref(x_115);
lean_inc_ref(x_1);
x_119 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_115, x_6, x_64, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
lean_dec_ref(x_119);
lean_inc(x_68);
lean_inc_ref(x_67);
lean_inc(x_66);
lean_inc_ref(x_65);
lean_inc(x_6);
lean_inc_ref(x_116);
lean_inc_ref(x_1);
x_121 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_116, x_6, x_64, x_65, x_66, x_67, x_68);
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
x_125 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_117, x_124, x_64, x_65, x_66, x_67, x_68);
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
x_47 = x_120;
x_48 = x_126;
x_49 = lean_box(0);
x_50 = x_118;
x_51 = x_117;
x_52 = x_122;
x_53 = x_114;
x_54 = x_129;
goto block_63;
}
else
{
size_t x_130; size_t x_131; uint8_t x_132; 
x_130 = lean_ptr_addr(x_116);
x_131 = lean_ptr_addr(x_122);
x_132 = lean_usize_dec_eq(x_130, x_131);
lean_inc(x_114);
lean_inc_ref(x_117);
x_47 = x_120;
x_48 = x_126;
x_49 = lean_box(0);
x_50 = x_118;
x_51 = x_117;
x_52 = x_122;
x_53 = x_114;
x_54 = x_132;
goto block_63;
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
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_121;
}
}
else
{
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_119;
}
}
case 10:
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_5, 0);
x_134 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_134);
x_135 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_134, x_6, x_64, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_135) == 0)
{
uint8_t x_136; 
x_136 = !lean_is_exclusive(x_135);
if (x_136 == 0)
{
lean_object* x_137; size_t x_138; size_t x_139; uint8_t x_140; 
x_137 = lean_ctor_get(x_135, 0);
x_138 = lean_ptr_addr(x_134);
x_139 = lean_ptr_addr(x_137);
x_140 = lean_usize_dec_eq(x_138, x_139);
if (x_140 == 0)
{
lean_object* x_141; 
lean_inc(x_133);
lean_dec_ref(x_5);
x_141 = l_Lean_Expr_mdata___override(x_133, x_137);
lean_ctor_set(x_135, 0, x_141);
return x_135;
}
else
{
lean_dec(x_137);
lean_ctor_set(x_135, 0, x_5);
return x_135;
}
}
else
{
lean_object* x_142; size_t x_143; size_t x_144; uint8_t x_145; 
x_142 = lean_ctor_get(x_135, 0);
lean_inc(x_142);
lean_dec(x_135);
x_143 = lean_ptr_addr(x_134);
x_144 = lean_ptr_addr(x_142);
x_145 = lean_usize_dec_eq(x_143, x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_inc(x_133);
lean_dec_ref(x_5);
x_146 = l_Lean_Expr_mdata___override(x_133, x_142);
x_147 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_147, 0, x_146);
return x_147;
}
else
{
lean_object* x_148; 
lean_dec(x_142);
x_148 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_148, 0, x_5);
return x_148;
}
}
}
else
{
lean_dec_ref(x_5);
return x_135;
}
}
case 11:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_5, 0);
x_150 = lean_ctor_get(x_5, 1);
x_151 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_151);
x_152 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_151, x_6, x_64, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_152) == 0)
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
lean_object* x_154; size_t x_155; size_t x_156; uint8_t x_157; 
x_154 = lean_ctor_get(x_152, 0);
x_155 = lean_ptr_addr(x_151);
x_156 = lean_ptr_addr(x_154);
x_157 = lean_usize_dec_eq(x_155, x_156);
if (x_157 == 0)
{
lean_object* x_158; 
lean_inc(x_150);
lean_inc(x_149);
lean_dec_ref(x_5);
x_158 = l_Lean_Expr_proj___override(x_149, x_150, x_154);
lean_ctor_set(x_152, 0, x_158);
return x_152;
}
else
{
lean_dec(x_154);
lean_ctor_set(x_152, 0, x_5);
return x_152;
}
}
else
{
lean_object* x_159; size_t x_160; size_t x_161; uint8_t x_162; 
x_159 = lean_ctor_get(x_152, 0);
lean_inc(x_159);
lean_dec(x_152);
x_160 = lean_ptr_addr(x_151);
x_161 = lean_ptr_addr(x_159);
x_162 = lean_usize_dec_eq(x_160, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_inc(x_150);
lean_inc(x_149);
lean_dec_ref(x_5);
x_163 = l_Lean_Expr_proj___override(x_149, x_150, x_159);
x_164 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_164, 0, x_163);
return x_164;
}
else
{
lean_object* x_165; 
lean_dec(x_159);
x_165 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_165, 0, x_5);
return x_165;
}
}
}
else
{
lean_dec_ref(x_5);
return x_152;
}
}
default: 
{
lean_object* x_166; 
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_66);
lean_dec_ref(x_65);
lean_dec(x_6);
lean_dec_ref(x_1);
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_5);
return x_166;
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
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_6);
x_8 = l_Lean_instantiateMVarsCore(x_7, x_1);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec_ref(x_8);
x_11 = lean_st_ref_take(x_2);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_10);
x_14 = lean_st_ref_set(x_2, x_11);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_11, 1);
x_17 = lean_ctor_get(x_11, 2);
x_18 = lean_ctor_get(x_11, 3);
x_19 = lean_ctor_get(x_11, 4);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_9);
return x_22;
}
}
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
static lean_object* _init_l_Lean_Meta_kabstract___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_29; 
x_9 = l_Lean_instantiateMVars___at___00Lean_Meta_kabstract_spec__0___redArg(x_1, x_5);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 x_11 = x_9;
} else {
 lean_dec_ref(x_9);
 x_11 = lean_box(0);
}
x_29 = l_Lean_Expr_isFVar(x_2);
if (x_29 == 0)
{
x_12 = x_29;
goto block_28;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_box(0);
lean_inc(x_3);
x_31 = l_Lean_Meta_instBEqOccurrences_beq(x_3, x_30);
x_12 = x_31;
goto block_28;
}
block_28:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_st_mk_ref(x_13);
lean_inc_ref(x_2);
x_15 = l_Lean_Expr_toHeadIndex(x_2);
x_16 = l_Lean_Expr_headNumArgs(x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l___private_Lean_Meta_KAbstract_0__Lean_Meta_kabstract_visit(x_2, x_3, x_15, x_16, x_10, x_17, x_14, x_4, x_5, x_6, x_7);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_3);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_st_ref_get(x_14);
lean_dec(x_14);
lean_dec(x_20);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_st_ref_get(x_14);
lean_dec(x_14);
lean_dec(x_22);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_21);
return x_23;
}
}
else
{
lean_dec(x_14);
return x_18;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_24 = l_Lean_Meta_kabstract___closed__0;
x_25 = lean_array_push(x_24, x_2);
x_26 = lean_expr_abstract(x_10, x_25);
lean_dec_ref(x_25);
lean_dec(x_10);
if (lean_is_scalar(x_11)) {
 x_27 = lean_alloc_ctor(0, 1, 0);
} else {
 x_27 = x_11;
}
lean_ctor_set(x_27, 0, x_26);
return x_27;
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
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_kabstract(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* initialize_Lean_HeadIndex(uint8_t builtin);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_HeadIndex(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_kabstract___closed__0 = _init_l_Lean_Meta_kabstract___closed__0();
lean_mark_persistent(l_Lean_Meta_kabstract___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
