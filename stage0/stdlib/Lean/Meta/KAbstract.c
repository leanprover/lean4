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
uint8_t l_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1363_(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_mkBVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_kabstract_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_kabstract_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_kabstract_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_kabstract_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_414_(uint8_t, uint8_t);
lean_object* l_Lean_Expr_headNumArgs(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Occurrences_contains(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_93_(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_153; 
x_153 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_153 == 0)
{
lean_object* x_154; uint8_t x_155; 
lean_inc_ref(x_5);
x_154 = l_Lean_Expr_toHeadIndex(x_5);
x_155 = l_Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_93_(x_154, x_3);
lean_dec(x_154);
if (x_155 == 0)
{
x_56 = x_7;
x_57 = x_8;
x_58 = x_9;
x_59 = x_10;
x_60 = x_11;
x_61 = x_12;
goto block_152;
}
else
{
if (x_153 == 0)
{
lean_object* x_156; uint8_t x_157; 
x_156 = l_Lean_Expr_headNumArgs(x_5);
x_157 = lean_nat_dec_eq(x_156, x_4);
lean_dec(x_156);
if (x_157 == 0)
{
x_56 = x_7;
x_57 = x_8;
x_58 = x_9;
x_59 = x_10;
x_60 = x_11;
x_61 = x_12;
goto block_152;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_st_ref_get(x_9, x_12);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec_ref(x_158);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc_ref(x_1);
lean_inc_ref(x_5);
x_161 = l_Lean_Meta_isExprDefEq(x_5, x_1, x_8, x_9, x_10, x_11, x_160);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; uint8_t x_163; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_unbox(x_162);
lean_dec(x_162);
if (x_163 == 0)
{
lean_object* x_164; 
lean_dec(x_159);
x_164 = lean_ctor_get(x_161, 1);
lean_inc(x_164);
lean_dec_ref(x_161);
x_56 = x_7;
x_57 = x_8;
x_58 = x_9;
x_59 = x_10;
x_60 = x_11;
x_61 = x_164;
goto block_152;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_165 = lean_ctor_get(x_161, 1);
lean_inc(x_165);
lean_dec_ref(x_161);
x_166 = lean_st_ref_get(x_7, x_165);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_166, 1);
lean_inc(x_168);
lean_dec_ref(x_166);
x_169 = lean_unsigned_to_nat(1u);
x_170 = lean_nat_add(x_167, x_169);
x_171 = lean_st_ref_set(x_7, x_170, x_168);
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_173 = lean_ctor_get(x_171, 1);
x_174 = lean_ctor_get(x_171, 0);
lean_dec(x_174);
x_175 = l_Lean_Meta_Occurrences_contains(x_2, x_167);
lean_dec(x_167);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_free_object(x_171);
x_176 = lean_st_ref_take(x_9, x_173);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
lean_dec_ref(x_176);
x_179 = lean_ctor_get(x_159, 0);
lean_inc_ref(x_179);
lean_dec(x_159);
x_180 = !lean_is_exclusive(x_177);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_177, 0);
lean_dec(x_181);
lean_ctor_set(x_177, 0, x_179);
x_182 = lean_st_ref_set(x_9, x_177, x_178);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec_ref(x_182);
x_56 = x_7;
x_57 = x_8;
x_58 = x_9;
x_59 = x_10;
x_60 = x_11;
x_61 = x_183;
goto block_152;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_184 = lean_ctor_get(x_177, 1);
x_185 = lean_ctor_get(x_177, 2);
x_186 = lean_ctor_get(x_177, 3);
x_187 = lean_ctor_get(x_177, 4);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_177);
x_188 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_188, 0, x_179);
lean_ctor_set(x_188, 1, x_184);
lean_ctor_set(x_188, 2, x_185);
lean_ctor_set(x_188, 3, x_186);
lean_ctor_set(x_188, 4, x_187);
x_189 = lean_st_ref_set(x_9, x_188, x_178);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec_ref(x_189);
x_56 = x_7;
x_57 = x_8;
x_58 = x_9;
x_59 = x_10;
x_60 = x_11;
x_61 = x_190;
goto block_152;
}
}
else
{
lean_object* x_191; 
lean_dec(x_159);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_191 = l_Lean_mkBVar(x_6);
lean_ctor_set(x_171, 0, x_191);
return x_171;
}
}
else
{
lean_object* x_192; uint8_t x_193; 
x_192 = lean_ctor_get(x_171, 1);
lean_inc(x_192);
lean_dec(x_171);
x_193 = l_Lean_Meta_Occurrences_contains(x_2, x_167);
lean_dec(x_167);
if (x_193 == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_194 = lean_st_ref_take(x_9, x_192);
x_195 = lean_ctor_get(x_194, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_194, 1);
lean_inc(x_196);
lean_dec_ref(x_194);
x_197 = lean_ctor_get(x_159, 0);
lean_inc_ref(x_197);
lean_dec(x_159);
x_198 = lean_ctor_get(x_195, 1);
lean_inc_ref(x_198);
x_199 = lean_ctor_get(x_195, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_195, 3);
lean_inc_ref(x_200);
x_201 = lean_ctor_get(x_195, 4);
lean_inc_ref(x_201);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 lean_ctor_release(x_195, 2);
 lean_ctor_release(x_195, 3);
 lean_ctor_release(x_195, 4);
 x_202 = x_195;
} else {
 lean_dec_ref(x_195);
 x_202 = lean_box(0);
}
if (lean_is_scalar(x_202)) {
 x_203 = lean_alloc_ctor(0, 5, 0);
} else {
 x_203 = x_202;
}
lean_ctor_set(x_203, 0, x_197);
lean_ctor_set(x_203, 1, x_198);
lean_ctor_set(x_203, 2, x_199);
lean_ctor_set(x_203, 3, x_200);
lean_ctor_set(x_203, 4, x_201);
x_204 = lean_st_ref_set(x_9, x_203, x_196);
x_205 = lean_ctor_get(x_204, 1);
lean_inc(x_205);
lean_dec_ref(x_204);
x_56 = x_7;
x_57 = x_8;
x_58 = x_9;
x_59 = x_10;
x_60 = x_11;
x_61 = x_205;
goto block_152;
}
else
{
lean_object* x_206; lean_object* x_207; 
lean_dec(x_159);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_206 = l_Lean_mkBVar(x_6);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_192);
return x_207;
}
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_159);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
x_208 = !lean_is_exclusive(x_161);
if (x_208 == 0)
{
return x_161;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_161, 0);
x_210 = lean_ctor_get(x_161, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_161);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
}
else
{
x_56 = x_7;
x_57 = x_8;
x_58 = x_9;
x_59 = x_10;
x_60 = x_11;
x_61 = x_12;
goto block_152;
}
}
}
else
{
x_56 = x_7;
x_57 = x_8;
x_58 = x_9;
x_59 = x_10;
x_60 = x_11;
x_61 = x_12;
goto block_152;
}
block_25:
{
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_5);
x_19 = l_Lean_Expr_lam___override(x_15, x_13, x_16, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_414_(x_17, x_17);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec_ref(x_5);
x_22 = l_Lean_Expr_lam___override(x_15, x_13, x_16, x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_14);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec_ref(x_16);
lean_dec(x_15);
lean_dec_ref(x_13);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_14);
return x_24;
}
}
}
block_38:
{
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_5);
x_32 = l_Lean_Expr_forallE___override(x_30, x_27, x_28, x_29);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_414_(x_29, x_29);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec_ref(x_5);
x_35 = l_Lean_Expr_forallE___override(x_30, x_27, x_28, x_29);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_26);
return x_36;
}
else
{
lean_object* x_37; 
lean_dec(x_30);
lean_dec_ref(x_28);
lean_dec_ref(x_27);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_26);
return x_37;
}
}
}
block_55:
{
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
lean_dec_ref(x_39);
lean_dec_ref(x_5);
x_47 = l_Lean_Expr_letE___override(x_40, x_41, x_45, x_44, x_43);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_42);
return x_48;
}
else
{
size_t x_49; size_t x_50; uint8_t x_51; 
x_49 = lean_ptr_addr(x_39);
lean_dec_ref(x_39);
x_50 = lean_ptr_addr(x_44);
x_51 = lean_usize_dec_eq(x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec_ref(x_5);
x_52 = l_Lean_Expr_letE___override(x_40, x_41, x_45, x_44, x_43);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_42);
return x_53;
}
else
{
lean_object* x_54; 
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec_ref(x_41);
lean_dec(x_40);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_5);
lean_ctor_set(x_54, 1, x_42);
return x_54;
}
}
}
block_152:
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_63);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_6);
lean_inc_ref(x_1);
x_64 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_62, x_6, x_56, x_57, x_58, x_59, x_60, x_61);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec_ref(x_64);
x_67 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_63, x_6, x_56, x_57, x_58, x_59, x_60, x_66);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(x_5, x_65, x_69);
lean_dec_ref(x_5);
lean_ctor_set(x_67, 0, x_70);
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_67, 0);
x_72 = lean_ctor_get(x_67, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_67);
x_73 = l___private_Lean_Expr_0__Lean_Expr_updateApp_x21Impl(x_5, x_65, x_71);
lean_dec_ref(x_5);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_dec(x_65);
lean_dec_ref(x_5);
return x_67;
}
}
else
{
lean_dec_ref(x_63);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_64;
}
}
case 6:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_75 = lean_ctor_get(x_5, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_76);
x_77 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_77);
x_78 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_6);
lean_inc_ref(x_76);
lean_inc_ref(x_1);
x_79 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_76, x_6, x_56, x_57, x_58, x_59, x_60, x_61);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec_ref(x_79);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_add(x_6, x_82);
lean_dec(x_6);
lean_inc_ref(x_77);
x_84 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_77, x_83, x_56, x_57, x_58, x_59, x_60, x_81);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; size_t x_87; size_t x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec_ref(x_84);
x_87 = lean_ptr_addr(x_76);
lean_dec_ref(x_76);
x_88 = lean_ptr_addr(x_80);
x_89 = lean_usize_dec_eq(x_87, x_88);
if (x_89 == 0)
{
lean_dec_ref(x_77);
x_13 = x_80;
x_14 = x_86;
x_15 = x_75;
x_16 = x_85;
x_17 = x_78;
x_18 = x_89;
goto block_25;
}
else
{
size_t x_90; size_t x_91; uint8_t x_92; 
x_90 = lean_ptr_addr(x_77);
lean_dec_ref(x_77);
x_91 = lean_ptr_addr(x_85);
x_92 = lean_usize_dec_eq(x_90, x_91);
x_13 = x_80;
x_14 = x_86;
x_15 = x_75;
x_16 = x_85;
x_17 = x_78;
x_18 = x_92;
goto block_25;
}
}
else
{
lean_dec(x_80);
lean_dec_ref(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec_ref(x_5);
return x_84;
}
}
else
{
lean_dec_ref(x_77);
lean_dec_ref(x_76);
lean_dec(x_75);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_79;
}
}
case 7:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; 
x_93 = lean_ctor_get(x_5, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_94);
x_95 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_95);
x_96 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_6);
lean_inc_ref(x_94);
lean_inc_ref(x_1);
x_97 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_94, x_6, x_56, x_57, x_58, x_59, x_60, x_61);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec_ref(x_97);
x_100 = lean_unsigned_to_nat(1u);
x_101 = lean_nat_add(x_6, x_100);
lean_dec(x_6);
lean_inc_ref(x_95);
x_102 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_95, x_101, x_56, x_57, x_58, x_59, x_60, x_99);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; size_t x_105; size_t x_106; uint8_t x_107; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec_ref(x_102);
x_105 = lean_ptr_addr(x_94);
lean_dec_ref(x_94);
x_106 = lean_ptr_addr(x_98);
x_107 = lean_usize_dec_eq(x_105, x_106);
if (x_107 == 0)
{
lean_dec_ref(x_95);
x_26 = x_104;
x_27 = x_98;
x_28 = x_103;
x_29 = x_96;
x_30 = x_93;
x_31 = x_107;
goto block_38;
}
else
{
size_t x_108; size_t x_109; uint8_t x_110; 
x_108 = lean_ptr_addr(x_95);
lean_dec_ref(x_95);
x_109 = lean_ptr_addr(x_103);
x_110 = lean_usize_dec_eq(x_108, x_109);
x_26 = x_104;
x_27 = x_98;
x_28 = x_103;
x_29 = x_96;
x_30 = x_93;
x_31 = x_110;
goto block_38;
}
}
else
{
lean_dec(x_98);
lean_dec_ref(x_95);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec_ref(x_5);
return x_102;
}
}
else
{
lean_dec_ref(x_95);
lean_dec_ref(x_94);
lean_dec(x_93);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_97;
}
}
case 8:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_111 = lean_ctor_get(x_5, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_112);
x_113 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_113);
x_114 = lean_ctor_get(x_5, 3);
lean_inc_ref(x_114);
x_115 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_6);
lean_inc_ref(x_112);
lean_inc_ref(x_1);
x_116 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_112, x_6, x_56, x_57, x_58, x_59, x_60, x_61);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec_ref(x_116);
lean_inc(x_60);
lean_inc_ref(x_59);
lean_inc(x_58);
lean_inc_ref(x_57);
lean_inc(x_6);
lean_inc_ref(x_113);
lean_inc_ref(x_1);
x_119 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_113, x_6, x_56, x_57, x_58, x_59, x_60, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec_ref(x_119);
x_122 = lean_unsigned_to_nat(1u);
x_123 = lean_nat_add(x_6, x_122);
lean_dec(x_6);
lean_inc_ref(x_114);
x_124 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_114, x_123, x_56, x_57, x_58, x_59, x_60, x_121);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; size_t x_127; size_t x_128; uint8_t x_129; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec_ref(x_124);
x_127 = lean_ptr_addr(x_112);
lean_dec_ref(x_112);
x_128 = lean_ptr_addr(x_117);
x_129 = lean_usize_dec_eq(x_127, x_128);
if (x_129 == 0)
{
lean_dec_ref(x_113);
x_39 = x_114;
x_40 = x_111;
x_41 = x_117;
x_42 = x_126;
x_43 = x_115;
x_44 = x_125;
x_45 = x_120;
x_46 = x_129;
goto block_55;
}
else
{
size_t x_130; size_t x_131; uint8_t x_132; 
x_130 = lean_ptr_addr(x_113);
lean_dec_ref(x_113);
x_131 = lean_ptr_addr(x_120);
x_132 = lean_usize_dec_eq(x_130, x_131);
x_39 = x_114;
x_40 = x_111;
x_41 = x_117;
x_42 = x_126;
x_43 = x_115;
x_44 = x_125;
x_45 = x_120;
x_46 = x_132;
goto block_55;
}
}
else
{
lean_dec(x_120);
lean_dec(x_117);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec_ref(x_5);
return x_124;
}
}
else
{
lean_dec(x_117);
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_119;
}
}
else
{
lean_dec_ref(x_114);
lean_dec_ref(x_113);
lean_dec_ref(x_112);
lean_dec(x_111);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_116;
}
}
case 10:
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_133);
x_134 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_133, x_6, x_56, x_57, x_58, x_59, x_60, x_61);
if (lean_obj_tag(x_134) == 0)
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_134, 0);
x_137 = l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(x_5, x_136);
lean_ctor_set(x_134, 0, x_137);
return x_134;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_134, 0);
x_139 = lean_ctor_get(x_134, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_134);
x_140 = l___private_Lean_Expr_0__Lean_Expr_updateMData_x21Impl(x_5, x_138);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_140);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
else
{
lean_dec_ref(x_5);
return x_134;
}
}
case 11:
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_5, 2);
lean_inc_ref(x_142);
x_143 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_142, x_6, x_56, x_57, x_58, x_59, x_60, x_61);
if (lean_obj_tag(x_143) == 0)
{
uint8_t x_144; 
x_144 = !lean_is_exclusive(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_143, 0);
x_146 = l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(x_5, x_145);
lean_ctor_set(x_143, 0, x_146);
return x_143;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_ctor_get(x_143, 0);
x_148 = lean_ctor_get(x_143, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_143);
x_149 = l___private_Lean_Expr_0__Lean_Expr_updateProj_x21Impl(x_5, x_147);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_148);
return x_150;
}
}
else
{
lean_dec_ref(x_5);
return x_143;
}
}
default: 
{
lean_object* x_151; 
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_58);
lean_dec_ref(x_57);
lean_dec(x_6);
lean_dec_ref(x_1);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_5);
lean_ctor_set(x_151, 1, x_61);
return x_151;
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_kabstract_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_6 = lean_st_ref_get(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec_ref(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_9);
lean_dec(x_7);
x_10 = l_Lean_instantiateMVarsCore(x_9, x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = lean_st_ref_take(x_2, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
lean_ctor_set(x_14, 0, x_12);
x_18 = lean_st_ref_set(x_2, x_14, x_15);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_11);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_11);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_23 = lean_ctor_get(x_14, 1);
x_24 = lean_ctor_get(x_14, 2);
x_25 = lean_ctor_get(x_14, 3);
x_26 = lean_ctor_get(x_14, 4);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_14);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_st_ref_set(x_2, x_27, x_15);
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_30 = x_28;
} else {
 lean_dec_ref(x_28);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_11);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_kabstract_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___Lean_Meta_kabstract_spec__0___redArg(x_1, x_3, x_6);
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
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_34; 
x_9 = l_Lean_instantiateMVars___at___Lean_Meta_kabstract_spec__0___redArg(x_1, x_5, x_8);
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
x_36 = l_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1363_(x_3, x_35);
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
lean_dec_ref(x_15);
lean_inc_ref(x_2);
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
lean_dec_ref(x_21);
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
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_29 = l_Lean_Meta_kabstract___closed__0;
x_30 = lean_array_push(x_29, x_2);
x_31 = lean_expr_abstract(x_10, x_30);
lean_dec_ref(x_30);
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_kabstract_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___Lean_Meta_kabstract_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Meta_kabstract_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instantiateMVars___at___Lean_Meta_kabstract_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
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
