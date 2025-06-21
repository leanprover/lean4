// Lean compiler output
// Module: Lean.Meta.KAbstract
// Imports: Lean.HeadIndex Lean.Meta.Basic
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
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint8_t l_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1336_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_headNumArgs(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Occurrences_contains(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_92_(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; uint8_t x_39; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_179; 
x_179 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_179 == 0)
{
lean_object* x_180; uint8_t x_181; 
lean_inc(x_5);
x_180 = l_Lean_Expr_toHeadIndex(x_5);
x_181 = l_Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_92_(x_180, x_3);
lean_dec(x_180);
if (x_181 == 0)
{
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = x_12;
goto block_178;
}
else
{
if (x_179 == 0)
{
lean_object* x_182; uint8_t x_183; 
x_182 = l_Lean_Expr_headNumArgs(x_5);
x_183 = lean_nat_dec_eq(x_182, x_4);
lean_dec(x_182);
if (x_183 == 0)
{
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = x_12;
goto block_178;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_st_ref_get(x_9, x_12);
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_5);
x_187 = l_Lean_Meta_isExprDefEq(x_5, x_1, x_8, x_9, x_10, x_11, x_186);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; uint8_t x_189; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
lean_dec(x_188);
if (x_189 == 0)
{
lean_object* x_190; 
lean_dec(x_185);
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
lean_dec(x_187);
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = x_190;
goto block_178;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; 
x_191 = lean_ctor_get(x_187, 1);
lean_inc(x_191);
lean_dec(x_187);
x_192 = lean_st_ref_get(x_7, x_191);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_unsigned_to_nat(1u);
x_196 = lean_nat_add(x_193, x_195);
x_197 = lean_st_ref_set(x_7, x_196, x_194);
x_198 = !lean_is_exclusive(x_197);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_199 = lean_ctor_get(x_197, 1);
x_200 = lean_ctor_get(x_197, 0);
lean_dec(x_200);
x_201 = l_Lean_Meta_Occurrences_contains(x_2, x_193);
lean_dec(x_193);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
lean_free_object(x_197);
x_202 = lean_st_ref_take(x_9, x_199);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_205 = lean_ctor_get(x_185, 0);
lean_inc(x_205);
lean_dec(x_185);
x_206 = !lean_is_exclusive(x_203);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_203, 0);
lean_dec(x_207);
lean_ctor_set(x_203, 0, x_205);
x_208 = lean_st_ref_set(x_9, x_203, x_204);
x_209 = lean_ctor_get(x_208, 1);
lean_inc(x_209);
lean_dec(x_208);
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = x_209;
goto block_178;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_210 = lean_ctor_get(x_203, 1);
x_211 = lean_ctor_get(x_203, 2);
x_212 = lean_ctor_get(x_203, 3);
x_213 = lean_ctor_get(x_203, 4);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_203);
x_214 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_214, 0, x_205);
lean_ctor_set(x_214, 1, x_210);
lean_ctor_set(x_214, 2, x_211);
lean_ctor_set(x_214, 3, x_212);
lean_ctor_set(x_214, 4, x_213);
x_215 = lean_st_ref_set(x_9, x_214, x_204);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = x_216;
goto block_178;
}
}
else
{
lean_object* x_217; 
lean_dec(x_185);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_217 = l_Lean_Expr_bvar___override(x_6);
lean_ctor_set(x_197, 0, x_217);
return x_197;
}
}
else
{
lean_object* x_218; uint8_t x_219; 
x_218 = lean_ctor_get(x_197, 1);
lean_inc(x_218);
lean_dec(x_197);
x_219 = l_Lean_Meta_Occurrences_contains(x_2, x_193);
lean_dec(x_193);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_220 = lean_st_ref_take(x_9, x_218);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = lean_ctor_get(x_185, 0);
lean_inc(x_223);
lean_dec(x_185);
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
x_225 = lean_ctor_get(x_221, 2);
lean_inc(x_225);
x_226 = lean_ctor_get(x_221, 3);
lean_inc(x_226);
x_227 = lean_ctor_get(x_221, 4);
lean_inc(x_227);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 lean_ctor_release(x_221, 2);
 lean_ctor_release(x_221, 3);
 lean_ctor_release(x_221, 4);
 x_228 = x_221;
} else {
 lean_dec_ref(x_221);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(0, 5, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_223);
lean_ctor_set(x_229, 1, x_224);
lean_ctor_set(x_229, 2, x_225);
lean_ctor_set(x_229, 3, x_226);
lean_ctor_set(x_229, 4, x_227);
x_230 = lean_st_ref_set(x_9, x_229, x_222);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_64 = x_7;
x_65 = x_8;
x_66 = x_9;
x_67 = x_10;
x_68 = x_11;
x_69 = x_231;
goto block_178;
}
else
{
lean_object* x_232; lean_object* x_233; 
lean_dec(x_185);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_232 = l_Lean_Expr_bvar___override(x_6);
x_233 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_233, 0, x_232);
lean_ctor_set(x_233, 1, x_218);
return x_233;
}
}
}
}
else
{
uint8_t x_234; 
lean_dec(x_185);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_234 = !lean_is_exclusive(x_187);
if (x_234 == 0)
{
return x_187;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_187, 0);
x_236 = lean_ctor_get(x_187, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_187);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
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
x_69 = x_12;
goto block_178;
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
x_69 = x_12;
goto block_178;
}
block_20:
{
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
x_17 = l_Lean_Expr_app___override(x_13, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
block_33:
{
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_5);
x_27 = l_Lean_Expr_lam___override(x_24, x_23, x_22, x_21);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_21, x_21);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_5);
x_30 = l_Lean_Expr_lam___override(x_24, x_23, x_22, x_21);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_25);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_5);
lean_ctor_set(x_32, 1, x_25);
return x_32;
}
}
}
block_46:
{
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
x_40 = l_Lean_Expr_forallE___override(x_35, x_38, x_34, x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
return x_41;
}
else
{
uint8_t x_42; 
x_42 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_37, x_37);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_5);
x_43 = l_Lean_Expr_forallE___override(x_35, x_38, x_34, x_37);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_36);
return x_44;
}
else
{
lean_object* x_45; 
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_34);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_5);
lean_ctor_set(x_45, 1, x_36);
return x_45;
}
}
}
block_63:
{
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_53);
lean_dec(x_5);
x_55 = l_Lean_Expr_letE___override(x_49, x_48, x_52, x_51, x_47);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_50);
return x_56;
}
else
{
size_t x_57; size_t x_58; uint8_t x_59; 
x_57 = lean_ptr_addr(x_53);
lean_dec(x_53);
x_58 = lean_ptr_addr(x_51);
x_59 = lean_usize_dec_eq(x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_5);
x_60 = l_Lean_Expr_letE___override(x_49, x_48, x_52, x_51, x_47);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_50);
return x_61;
}
else
{
lean_object* x_62; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_48);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_5);
lean_ctor_set(x_62, 1, x_50);
return x_62;
}
}
}
block_178:
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_5, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_5, 1);
lean_inc(x_71);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_6);
lean_inc(x_70);
lean_inc(x_1);
x_72 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_70, x_6, x_64, x_65, x_66, x_67, x_68, x_69);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_71);
x_75 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_71, x_6, x_64, x_65, x_66, x_67, x_68, x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; size_t x_78; size_t x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ptr_addr(x_70);
lean_dec(x_70);
x_79 = lean_ptr_addr(x_73);
x_80 = lean_usize_dec_eq(x_78, x_79);
if (x_80 == 0)
{
lean_dec(x_71);
x_13 = x_73;
x_14 = x_76;
x_15 = x_77;
x_16 = x_80;
goto block_20;
}
else
{
size_t x_81; size_t x_82; uint8_t x_83; 
x_81 = lean_ptr_addr(x_71);
lean_dec(x_71);
x_82 = lean_ptr_addr(x_76);
x_83 = lean_usize_dec_eq(x_81, x_82);
x_13 = x_73;
x_14 = x_76;
x_15 = x_77;
x_16 = x_83;
goto block_20;
}
}
else
{
lean_dec(x_73);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_5);
return x_75;
}
}
else
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_72;
}
}
case 6:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; 
x_84 = lean_ctor_get(x_5, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_5, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_5, 2);
lean_inc(x_86);
x_87 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_6);
lean_inc(x_85);
lean_inc(x_1);
x_88 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_85, x_6, x_64, x_65, x_66, x_67, x_68, x_69);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_add(x_6, x_91);
lean_dec(x_6);
lean_inc(x_86);
x_93 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_86, x_92, x_64, x_65, x_66, x_67, x_68, x_90);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; size_t x_96; size_t x_97; uint8_t x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ptr_addr(x_85);
lean_dec(x_85);
x_97 = lean_ptr_addr(x_89);
x_98 = lean_usize_dec_eq(x_96, x_97);
if (x_98 == 0)
{
lean_dec(x_86);
x_21 = x_87;
x_22 = x_94;
x_23 = x_89;
x_24 = x_84;
x_25 = x_95;
x_26 = x_98;
goto block_33;
}
else
{
size_t x_99; size_t x_100; uint8_t x_101; 
x_99 = lean_ptr_addr(x_86);
lean_dec(x_86);
x_100 = lean_ptr_addr(x_94);
x_101 = lean_usize_dec_eq(x_99, x_100);
x_21 = x_87;
x_22 = x_94;
x_23 = x_89;
x_24 = x_84;
x_25 = x_95;
x_26 = x_101;
goto block_33;
}
}
else
{
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_5);
return x_93;
}
}
else
{
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_88;
}
}
case 7:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; 
x_102 = lean_ctor_get(x_5, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_5, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_5, 2);
lean_inc(x_104);
x_105 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_6);
lean_inc(x_103);
lean_inc(x_1);
x_106 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_103, x_6, x_64, x_65, x_66, x_67, x_68, x_69);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_unsigned_to_nat(1u);
x_110 = lean_nat_add(x_6, x_109);
lean_dec(x_6);
lean_inc(x_104);
x_111 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_104, x_110, x_64, x_65, x_66, x_67, x_68, x_108);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; size_t x_114; size_t x_115; uint8_t x_116; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ptr_addr(x_103);
lean_dec(x_103);
x_115 = lean_ptr_addr(x_107);
x_116 = lean_usize_dec_eq(x_114, x_115);
if (x_116 == 0)
{
lean_dec(x_104);
x_34 = x_112;
x_35 = x_102;
x_36 = x_113;
x_37 = x_105;
x_38 = x_107;
x_39 = x_116;
goto block_46;
}
else
{
size_t x_117; size_t x_118; uint8_t x_119; 
x_117 = lean_ptr_addr(x_104);
lean_dec(x_104);
x_118 = lean_ptr_addr(x_112);
x_119 = lean_usize_dec_eq(x_117, x_118);
x_34 = x_112;
x_35 = x_102;
x_36 = x_113;
x_37 = x_105;
x_38 = x_107;
x_39 = x_119;
goto block_46;
}
}
else
{
lean_dec(x_107);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_5);
return x_111;
}
}
else
{
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_106;
}
}
case 8:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; lean_object* x_125; 
x_120 = lean_ctor_get(x_5, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_5, 1);
lean_inc(x_121);
x_122 = lean_ctor_get(x_5, 2);
lean_inc(x_122);
x_123 = lean_ctor_get(x_5, 3);
lean_inc(x_123);
x_124 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_6);
lean_inc(x_121);
lean_inc(x_1);
x_125 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_121, x_6, x_64, x_65, x_66, x_67, x_68, x_69);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
lean_inc(x_68);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_6);
lean_inc(x_122);
lean_inc(x_1);
x_128 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_122, x_6, x_64, x_65, x_66, x_67, x_68, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_unsigned_to_nat(1u);
x_132 = lean_nat_add(x_6, x_131);
lean_dec(x_6);
lean_inc(x_123);
x_133 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_123, x_132, x_64, x_65, x_66, x_67, x_68, x_130);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; size_t x_136; size_t x_137; uint8_t x_138; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_ptr_addr(x_121);
lean_dec(x_121);
x_137 = lean_ptr_addr(x_126);
x_138 = lean_usize_dec_eq(x_136, x_137);
if (x_138 == 0)
{
lean_dec(x_122);
x_47 = x_124;
x_48 = x_126;
x_49 = x_120;
x_50 = x_135;
x_51 = x_134;
x_52 = x_129;
x_53 = x_123;
x_54 = x_138;
goto block_63;
}
else
{
size_t x_139; size_t x_140; uint8_t x_141; 
x_139 = lean_ptr_addr(x_122);
lean_dec(x_122);
x_140 = lean_ptr_addr(x_129);
x_141 = lean_usize_dec_eq(x_139, x_140);
x_47 = x_124;
x_48 = x_126;
x_49 = x_120;
x_50 = x_135;
x_51 = x_134;
x_52 = x_129;
x_53 = x_123;
x_54 = x_141;
goto block_63;
}
}
else
{
lean_dec(x_129);
lean_dec(x_126);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_5);
return x_133;
}
}
else
{
lean_dec(x_126);
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_128;
}
}
else
{
lean_dec(x_123);
lean_dec(x_122);
lean_dec(x_121);
lean_dec(x_120);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_125;
}
}
case 10:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_5, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_5, 1);
lean_inc(x_143);
lean_inc(x_143);
x_144 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_143, x_6, x_64, x_65, x_66, x_67, x_68, x_69);
if (lean_obj_tag(x_144) == 0)
{
uint8_t x_145; 
x_145 = !lean_is_exclusive(x_144);
if (x_145 == 0)
{
lean_object* x_146; size_t x_147; size_t x_148; uint8_t x_149; 
x_146 = lean_ctor_get(x_144, 0);
x_147 = lean_ptr_addr(x_143);
lean_dec(x_143);
x_148 = lean_ptr_addr(x_146);
x_149 = lean_usize_dec_eq(x_147, x_148);
if (x_149 == 0)
{
lean_object* x_150; 
lean_dec(x_5);
x_150 = l_Lean_Expr_mdata___override(x_142, x_146);
lean_ctor_set(x_144, 0, x_150);
return x_144;
}
else
{
lean_dec(x_146);
lean_dec(x_142);
lean_ctor_set(x_144, 0, x_5);
return x_144;
}
}
else
{
lean_object* x_151; lean_object* x_152; size_t x_153; size_t x_154; uint8_t x_155; 
x_151 = lean_ctor_get(x_144, 0);
x_152 = lean_ctor_get(x_144, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_144);
x_153 = lean_ptr_addr(x_143);
lean_dec(x_143);
x_154 = lean_ptr_addr(x_151);
x_155 = lean_usize_dec_eq(x_153, x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_5);
x_156 = l_Lean_Expr_mdata___override(x_142, x_151);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_152);
return x_157;
}
else
{
lean_object* x_158; 
lean_dec(x_151);
lean_dec(x_142);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_5);
lean_ctor_set(x_158, 1, x_152);
return x_158;
}
}
}
else
{
lean_dec(x_143);
lean_dec(x_142);
lean_dec(x_5);
return x_144;
}
}
case 11:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_159 = lean_ctor_get(x_5, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_5, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_5, 2);
lean_inc(x_161);
lean_inc(x_161);
x_162 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_161, x_6, x_64, x_65, x_66, x_67, x_68, x_69);
if (lean_obj_tag(x_162) == 0)
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_162);
if (x_163 == 0)
{
lean_object* x_164; size_t x_165; size_t x_166; uint8_t x_167; 
x_164 = lean_ctor_get(x_162, 0);
x_165 = lean_ptr_addr(x_161);
lean_dec(x_161);
x_166 = lean_ptr_addr(x_164);
x_167 = lean_usize_dec_eq(x_165, x_166);
if (x_167 == 0)
{
lean_object* x_168; 
lean_dec(x_5);
x_168 = l_Lean_Expr_proj___override(x_159, x_160, x_164);
lean_ctor_set(x_162, 0, x_168);
return x_162;
}
else
{
lean_dec(x_164);
lean_dec(x_160);
lean_dec(x_159);
lean_ctor_set(x_162, 0, x_5);
return x_162;
}
}
else
{
lean_object* x_169; lean_object* x_170; size_t x_171; size_t x_172; uint8_t x_173; 
x_169 = lean_ctor_get(x_162, 0);
x_170 = lean_ctor_get(x_162, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_162);
x_171 = lean_ptr_addr(x_161);
lean_dec(x_161);
x_172 = lean_ptr_addr(x_169);
x_173 = lean_usize_dec_eq(x_171, x_172);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
lean_dec(x_5);
x_174 = l_Lean_Expr_proj___override(x_159, x_160, x_169);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_170);
return x_175;
}
else
{
lean_object* x_176; 
lean_dec(x_169);
lean_dec(x_160);
lean_dec(x_159);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_5);
lean_ctor_set(x_176, 1, x_170);
return x_176;
}
}
}
else
{
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
lean_dec(x_5);
return x_162;
}
}
default: 
{
lean_object* x_177; 
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_6);
lean_dec(x_1);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_5);
lean_ctor_set(x_177, 1, x_69);
return x_177;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
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
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_34; 
x_9 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_34 = l_Lean_Expr_isFVar(x_2);
if (x_34 == 0)
{
x_13 = x_34;
goto block_33;
}
else
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_box(0);
lean_inc(x_3);
x_36 = l_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1336_(x_3, x_35);
x_13 = x_36;
goto block_33;
}
block_33:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_st_mk_ref(x_14, x_11);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_2);
x_18 = l_Lean_Expr_toHeadIndex(x_2);
x_19 = l_Lean_Expr_headNumArgs(x_2);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_18, x_19, x_10, x_20, x_16, x_4, x_5, x_6, x_7, x_17);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_3);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_get(x_16, x_23);
lean_dec(x_16);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
else
{
lean_dec(x_16);
return x_21;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = l_Lean_Meta_kabstract___closed__0;
x_30 = lean_array_push(x_29, x_2);
x_31 = lean_expr_abstract(x_10, x_30);
lean_dec(x_30);
lean_dec(x_10);
if (lean_is_scalar(x_12)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_12;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_11);
return x_32;
}
}
}
}
lean_object* initialize_Lean_HeadIndex(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_HeadIndex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_kabstract___closed__0 = _init_l_Lean_Meta_kabstract___closed__0();
lean_mark_persistent(l_Lean_Meta_kabstract___closed__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
