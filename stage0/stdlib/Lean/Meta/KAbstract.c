// Lean compiler output
// Module: Lean.Meta.KAbstract
// Imports: Init Lean.Data.Occurrences Lean.HeadIndex Lean.Meta.Basic
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
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Occurrences_contains(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(lean_object*, lean_object*);
uint8_t l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_66_(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_32_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_kabstract___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_142; 
x_142 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; 
lean_inc(x_5);
x_143 = l_Lean_Expr_toHeadIndex(x_5);
x_144 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_66_(x_143, x_3);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; 
x_145 = lean_box(0);
x_13 = x_145;
goto block_141;
}
else
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_146 = lean_unsigned_to_nat(0u);
x_147 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_5, x_146);
x_148 = lean_nat_dec_eq(x_147, x_4);
lean_dec(x_147);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_box(0);
x_13 = x_149;
goto block_141;
}
else
{
lean_object* x_150; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_5);
x_150 = l_Lean_Meta_isExprDefEq(x_5, x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; uint8_t x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_unbox(x_151);
lean_dec(x_151);
if (x_152 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
x_154 = lean_ctor_get(x_5, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_5, 1);
lean_inc(x_155);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_156 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_154, x_6, x_7, x_8, x_9, x_10, x_11, x_153);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_155, x_6, x_7, x_8, x_9, x_10, x_11, x_158);
if (lean_obj_tag(x_159) == 0)
{
uint8_t x_160; 
x_160 = !lean_is_exclusive(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_159, 0);
x_162 = lean_expr_update_app(x_5, x_157, x_161);
lean_ctor_set(x_159, 0, x_162);
return x_159;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_163 = lean_ctor_get(x_159, 0);
x_164 = lean_ctor_get(x_159, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_159);
x_165 = lean_expr_update_app(x_5, x_157, x_163);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_164);
return x_166;
}
}
else
{
uint8_t x_167; 
lean_dec(x_157);
lean_dec(x_5);
x_167 = !lean_is_exclusive(x_159);
if (x_167 == 0)
{
return x_159;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_159, 0);
x_169 = lean_ctor_get(x_159, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_159);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_155);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_171 = !lean_is_exclusive(x_156);
if (x_171 == 0)
{
return x_156;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_156, 0);
x_173 = lean_ctor_get(x_156, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_156);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
case 6:
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_179; 
x_175 = lean_ctor_get(x_150, 1);
lean_inc(x_175);
lean_dec(x_150);
x_176 = lean_ctor_get(x_5, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_5, 2);
lean_inc(x_177);
x_178 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_179 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_176, x_6, x_7, x_8, x_9, x_10, x_11, x_175);
if (lean_obj_tag(x_179) == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_unsigned_to_nat(1u);
x_183 = lean_nat_add(x_6, x_182);
lean_dec(x_6);
x_184 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_177, x_183, x_7, x_8, x_9, x_10, x_11, x_181);
if (lean_obj_tag(x_184) == 0)
{
uint8_t x_185; 
x_185 = !lean_is_exclusive(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
x_186 = lean_ctor_get(x_184, 0);
x_187 = lean_expr_update_lambda(x_5, x_178, x_180, x_186);
lean_ctor_set(x_184, 0, x_187);
return x_184;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_188 = lean_ctor_get(x_184, 0);
x_189 = lean_ctor_get(x_184, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_184);
x_190 = lean_expr_update_lambda(x_5, x_178, x_180, x_188);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
else
{
uint8_t x_192; 
lean_dec(x_180);
lean_dec(x_5);
x_192 = !lean_is_exclusive(x_184);
if (x_192 == 0)
{
return x_184;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_184, 0);
x_194 = lean_ctor_get(x_184, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_184);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_177);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_196 = !lean_is_exclusive(x_179);
if (x_196 == 0)
{
return x_179;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_179, 0);
x_198 = lean_ctor_get(x_179, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_179);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
case 7:
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; uint8_t x_203; lean_object* x_204; 
x_200 = lean_ctor_get(x_150, 1);
lean_inc(x_200);
lean_dec(x_150);
x_201 = lean_ctor_get(x_5, 1);
lean_inc(x_201);
x_202 = lean_ctor_get(x_5, 2);
lean_inc(x_202);
x_203 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_204 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_201, x_6, x_7, x_8, x_9, x_10, x_11, x_200);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_unsigned_to_nat(1u);
x_208 = lean_nat_add(x_6, x_207);
lean_dec(x_6);
x_209 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_202, x_208, x_7, x_8, x_9, x_10, x_11, x_206);
if (lean_obj_tag(x_209) == 0)
{
uint8_t x_210; 
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
lean_object* x_211; lean_object* x_212; 
x_211 = lean_ctor_get(x_209, 0);
x_212 = lean_expr_update_forall(x_5, x_203, x_205, x_211);
lean_ctor_set(x_209, 0, x_212);
return x_209;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_213 = lean_ctor_get(x_209, 0);
x_214 = lean_ctor_get(x_209, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_209);
x_215 = lean_expr_update_forall(x_5, x_203, x_205, x_213);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_215);
lean_ctor_set(x_216, 1, x_214);
return x_216;
}
}
else
{
uint8_t x_217; 
lean_dec(x_205);
lean_dec(x_5);
x_217 = !lean_is_exclusive(x_209);
if (x_217 == 0)
{
return x_209;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_209, 0);
x_219 = lean_ctor_get(x_209, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_209);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
}
else
{
uint8_t x_221; 
lean_dec(x_202);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_221 = !lean_is_exclusive(x_204);
if (x_221 == 0)
{
return x_204;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_204, 0);
x_223 = lean_ctor_get(x_204, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_204);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
case 8:
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_225 = lean_ctor_get(x_150, 1);
lean_inc(x_225);
lean_dec(x_150);
x_226 = lean_ctor_get(x_5, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_5, 2);
lean_inc(x_227);
x_228 = lean_ctor_get(x_5, 3);
lean_inc(x_228);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_229 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_226, x_6, x_7, x_8, x_9, x_10, x_11, x_225);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_232 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_227, x_6, x_7, x_8, x_9, x_10, x_11, x_231);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
lean_dec(x_232);
x_235 = lean_unsigned_to_nat(1u);
x_236 = lean_nat_add(x_6, x_235);
lean_dec(x_6);
x_237 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_228, x_236, x_7, x_8, x_9, x_10, x_11, x_234);
if (lean_obj_tag(x_237) == 0)
{
uint8_t x_238; 
x_238 = !lean_is_exclusive(x_237);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_237, 0);
x_240 = lean_expr_update_let(x_5, x_230, x_233, x_239);
lean_ctor_set(x_237, 0, x_240);
return x_237;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_241 = lean_ctor_get(x_237, 0);
x_242 = lean_ctor_get(x_237, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_237);
x_243 = lean_expr_update_let(x_5, x_230, x_233, x_241);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
}
else
{
uint8_t x_245; 
lean_dec(x_233);
lean_dec(x_230);
lean_dec(x_5);
x_245 = !lean_is_exclusive(x_237);
if (x_245 == 0)
{
return x_237;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_237, 0);
x_247 = lean_ctor_get(x_237, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_237);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
else
{
uint8_t x_249; 
lean_dec(x_230);
lean_dec(x_228);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_249 = !lean_is_exclusive(x_232);
if (x_249 == 0)
{
return x_232;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_232, 0);
x_251 = lean_ctor_get(x_232, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_232);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
else
{
uint8_t x_253; 
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_253 = !lean_is_exclusive(x_229);
if (x_253 == 0)
{
return x_229;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_229, 0);
x_255 = lean_ctor_get(x_229, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_229);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
case 10:
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_150, 1);
lean_inc(x_257);
lean_dec(x_150);
x_258 = lean_ctor_get(x_5, 1);
lean_inc(x_258);
x_259 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_258, x_6, x_7, x_8, x_9, x_10, x_11, x_257);
if (lean_obj_tag(x_259) == 0)
{
uint8_t x_260; 
x_260 = !lean_is_exclusive(x_259);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; 
x_261 = lean_ctor_get(x_259, 0);
x_262 = lean_expr_update_mdata(x_5, x_261);
lean_ctor_set(x_259, 0, x_262);
return x_259;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_263 = lean_ctor_get(x_259, 0);
x_264 = lean_ctor_get(x_259, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_259);
x_265 = lean_expr_update_mdata(x_5, x_263);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_265);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
else
{
uint8_t x_267; 
lean_dec(x_5);
x_267 = !lean_is_exclusive(x_259);
if (x_267 == 0)
{
return x_259;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_259, 0);
x_269 = lean_ctor_get(x_259, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_259);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
case 11:
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_150, 1);
lean_inc(x_271);
lean_dec(x_150);
x_272 = lean_ctor_get(x_5, 2);
lean_inc(x_272);
x_273 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_272, x_6, x_7, x_8, x_9, x_10, x_11, x_271);
if (lean_obj_tag(x_273) == 0)
{
uint8_t x_274; 
x_274 = !lean_is_exclusive(x_273);
if (x_274 == 0)
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_273, 0);
x_276 = lean_expr_update_proj(x_5, x_275);
lean_ctor_set(x_273, 0, x_276);
return x_273;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_277 = lean_ctor_get(x_273, 0);
x_278 = lean_ctor_get(x_273, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_273);
x_279 = lean_expr_update_proj(x_5, x_277);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
else
{
uint8_t x_281; 
lean_dec(x_5);
x_281 = !lean_is_exclusive(x_273);
if (x_281 == 0)
{
return x_273;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_273, 0);
x_283 = lean_ctor_get(x_273, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_273);
x_284 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_284, 0, x_282);
lean_ctor_set(x_284, 1, x_283);
return x_284;
}
}
}
default: 
{
uint8_t x_285; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_285 = !lean_is_exclusive(x_150);
if (x_285 == 0)
{
lean_object* x_286; 
x_286 = lean_ctor_get(x_150, 0);
lean_dec(x_286);
lean_ctor_set(x_150, 0, x_5);
return x_150;
}
else
{
lean_object* x_287; lean_object* x_288; 
x_287 = lean_ctor_get(x_150, 1);
lean_inc(x_287);
lean_dec(x_150);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_5);
lean_ctor_set(x_288, 1, x_287);
return x_288;
}
}
}
}
else
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_289 = lean_ctor_get(x_150, 1);
lean_inc(x_289);
lean_dec(x_150);
x_290 = lean_st_ref_get(x_11, x_289);
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
lean_dec(x_290);
x_292 = lean_st_ref_get(x_7, x_291);
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
x_295 = lean_unsigned_to_nat(1u);
x_296 = lean_nat_add(x_293, x_295);
x_297 = lean_st_ref_get(x_11, x_294);
x_298 = lean_ctor_get(x_297, 1);
lean_inc(x_298);
lean_dec(x_297);
x_299 = lean_st_ref_set(x_7, x_296, x_298);
x_300 = !lean_is_exclusive(x_299);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_301 = lean_ctor_get(x_299, 1);
x_302 = lean_ctor_get(x_299, 0);
lean_dec(x_302);
x_303 = l_Lean_Occurrences_contains(x_2, x_293);
lean_dec(x_293);
if (x_303 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_free_object(x_299);
x_304 = lean_ctor_get(x_5, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_5, 1);
lean_inc(x_305);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_306 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_304, x_6, x_7, x_8, x_9, x_10, x_11, x_301);
if (lean_obj_tag(x_306) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
x_308 = lean_ctor_get(x_306, 1);
lean_inc(x_308);
lean_dec(x_306);
x_309 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_305, x_6, x_7, x_8, x_9, x_10, x_11, x_308);
if (lean_obj_tag(x_309) == 0)
{
uint8_t x_310; 
x_310 = !lean_is_exclusive(x_309);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; 
x_311 = lean_ctor_get(x_309, 0);
x_312 = lean_expr_update_app(x_5, x_307, x_311);
lean_ctor_set(x_309, 0, x_312);
return x_309;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_313 = lean_ctor_get(x_309, 0);
x_314 = lean_ctor_get(x_309, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_309);
x_315 = lean_expr_update_app(x_5, x_307, x_313);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_314);
return x_316;
}
}
else
{
uint8_t x_317; 
lean_dec(x_307);
lean_dec(x_5);
x_317 = !lean_is_exclusive(x_309);
if (x_317 == 0)
{
return x_309;
}
else
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_309, 0);
x_319 = lean_ctor_get(x_309, 1);
lean_inc(x_319);
lean_inc(x_318);
lean_dec(x_309);
x_320 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_320, 0, x_318);
lean_ctor_set(x_320, 1, x_319);
return x_320;
}
}
}
else
{
uint8_t x_321; 
lean_dec(x_305);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_321 = !lean_is_exclusive(x_306);
if (x_321 == 0)
{
return x_306;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_306, 0);
x_323 = lean_ctor_get(x_306, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_306);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
return x_324;
}
}
}
case 6:
{
lean_object* x_325; lean_object* x_326; uint8_t x_327; lean_object* x_328; 
lean_free_object(x_299);
x_325 = lean_ctor_get(x_5, 1);
lean_inc(x_325);
x_326 = lean_ctor_get(x_5, 2);
lean_inc(x_326);
x_327 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_328 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_325, x_6, x_7, x_8, x_9, x_10, x_11, x_301);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
x_331 = lean_nat_add(x_6, x_295);
lean_dec(x_6);
x_332 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_326, x_331, x_7, x_8, x_9, x_10, x_11, x_330);
if (lean_obj_tag(x_332) == 0)
{
uint8_t x_333; 
x_333 = !lean_is_exclusive(x_332);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; 
x_334 = lean_ctor_get(x_332, 0);
x_335 = lean_expr_update_lambda(x_5, x_327, x_329, x_334);
lean_ctor_set(x_332, 0, x_335);
return x_332;
}
else
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_336 = lean_ctor_get(x_332, 0);
x_337 = lean_ctor_get(x_332, 1);
lean_inc(x_337);
lean_inc(x_336);
lean_dec(x_332);
x_338 = lean_expr_update_lambda(x_5, x_327, x_329, x_336);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_337);
return x_339;
}
}
else
{
uint8_t x_340; 
lean_dec(x_329);
lean_dec(x_5);
x_340 = !lean_is_exclusive(x_332);
if (x_340 == 0)
{
return x_332;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_332, 0);
x_342 = lean_ctor_get(x_332, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_332);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
}
else
{
uint8_t x_344; 
lean_dec(x_326);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_344 = !lean_is_exclusive(x_328);
if (x_344 == 0)
{
return x_328;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_328, 0);
x_346 = lean_ctor_get(x_328, 1);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_328);
x_347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
return x_347;
}
}
}
case 7:
{
lean_object* x_348; lean_object* x_349; uint8_t x_350; lean_object* x_351; 
lean_free_object(x_299);
x_348 = lean_ctor_get(x_5, 1);
lean_inc(x_348);
x_349 = lean_ctor_get(x_5, 2);
lean_inc(x_349);
x_350 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_351 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_348, x_6, x_7, x_8, x_9, x_10, x_11, x_301);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = lean_nat_add(x_6, x_295);
lean_dec(x_6);
x_355 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_349, x_354, x_7, x_8, x_9, x_10, x_11, x_353);
if (lean_obj_tag(x_355) == 0)
{
uint8_t x_356; 
x_356 = !lean_is_exclusive(x_355);
if (x_356 == 0)
{
lean_object* x_357; lean_object* x_358; 
x_357 = lean_ctor_get(x_355, 0);
x_358 = lean_expr_update_forall(x_5, x_350, x_352, x_357);
lean_ctor_set(x_355, 0, x_358);
return x_355;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_359 = lean_ctor_get(x_355, 0);
x_360 = lean_ctor_get(x_355, 1);
lean_inc(x_360);
lean_inc(x_359);
lean_dec(x_355);
x_361 = lean_expr_update_forall(x_5, x_350, x_352, x_359);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_360);
return x_362;
}
}
else
{
uint8_t x_363; 
lean_dec(x_352);
lean_dec(x_5);
x_363 = !lean_is_exclusive(x_355);
if (x_363 == 0)
{
return x_355;
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_364 = lean_ctor_get(x_355, 0);
x_365 = lean_ctor_get(x_355, 1);
lean_inc(x_365);
lean_inc(x_364);
lean_dec(x_355);
x_366 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_366, 0, x_364);
lean_ctor_set(x_366, 1, x_365);
return x_366;
}
}
}
else
{
uint8_t x_367; 
lean_dec(x_349);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_367 = !lean_is_exclusive(x_351);
if (x_367 == 0)
{
return x_351;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_351, 0);
x_369 = lean_ctor_get(x_351, 1);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_351);
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
return x_370;
}
}
}
case 8:
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_free_object(x_299);
x_371 = lean_ctor_get(x_5, 1);
lean_inc(x_371);
x_372 = lean_ctor_get(x_5, 2);
lean_inc(x_372);
x_373 = lean_ctor_get(x_5, 3);
lean_inc(x_373);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_374 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_371, x_6, x_7, x_8, x_9, x_10, x_11, x_301);
if (lean_obj_tag(x_374) == 0)
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_375 = lean_ctor_get(x_374, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_374, 1);
lean_inc(x_376);
lean_dec(x_374);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_377 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_372, x_6, x_7, x_8, x_9, x_10, x_11, x_376);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
x_380 = lean_nat_add(x_6, x_295);
lean_dec(x_6);
x_381 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_373, x_380, x_7, x_8, x_9, x_10, x_11, x_379);
if (lean_obj_tag(x_381) == 0)
{
uint8_t x_382; 
x_382 = !lean_is_exclusive(x_381);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; 
x_383 = lean_ctor_get(x_381, 0);
x_384 = lean_expr_update_let(x_5, x_375, x_378, x_383);
lean_ctor_set(x_381, 0, x_384);
return x_381;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_385 = lean_ctor_get(x_381, 0);
x_386 = lean_ctor_get(x_381, 1);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_381);
x_387 = lean_expr_update_let(x_5, x_375, x_378, x_385);
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_386);
return x_388;
}
}
else
{
uint8_t x_389; 
lean_dec(x_378);
lean_dec(x_375);
lean_dec(x_5);
x_389 = !lean_is_exclusive(x_381);
if (x_389 == 0)
{
return x_381;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_381, 0);
x_391 = lean_ctor_get(x_381, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_381);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
return x_392;
}
}
}
else
{
uint8_t x_393; 
lean_dec(x_375);
lean_dec(x_373);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_393 = !lean_is_exclusive(x_377);
if (x_393 == 0)
{
return x_377;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_377, 0);
x_395 = lean_ctor_get(x_377, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_377);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
}
else
{
uint8_t x_397; 
lean_dec(x_373);
lean_dec(x_372);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_397 = !lean_is_exclusive(x_374);
if (x_397 == 0)
{
return x_374;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_374, 0);
x_399 = lean_ctor_get(x_374, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_374);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
}
case 10:
{
lean_object* x_401; lean_object* x_402; 
lean_free_object(x_299);
x_401 = lean_ctor_get(x_5, 1);
lean_inc(x_401);
x_402 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_401, x_6, x_7, x_8, x_9, x_10, x_11, x_301);
if (lean_obj_tag(x_402) == 0)
{
uint8_t x_403; 
x_403 = !lean_is_exclusive(x_402);
if (x_403 == 0)
{
lean_object* x_404; lean_object* x_405; 
x_404 = lean_ctor_get(x_402, 0);
x_405 = lean_expr_update_mdata(x_5, x_404);
lean_ctor_set(x_402, 0, x_405);
return x_402;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_406 = lean_ctor_get(x_402, 0);
x_407 = lean_ctor_get(x_402, 1);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_402);
x_408 = lean_expr_update_mdata(x_5, x_406);
x_409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_407);
return x_409;
}
}
else
{
uint8_t x_410; 
lean_dec(x_5);
x_410 = !lean_is_exclusive(x_402);
if (x_410 == 0)
{
return x_402;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_411 = lean_ctor_get(x_402, 0);
x_412 = lean_ctor_get(x_402, 1);
lean_inc(x_412);
lean_inc(x_411);
lean_dec(x_402);
x_413 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
return x_413;
}
}
}
case 11:
{
lean_object* x_414; lean_object* x_415; 
lean_free_object(x_299);
x_414 = lean_ctor_get(x_5, 2);
lean_inc(x_414);
x_415 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_414, x_6, x_7, x_8, x_9, x_10, x_11, x_301);
if (lean_obj_tag(x_415) == 0)
{
uint8_t x_416; 
x_416 = !lean_is_exclusive(x_415);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; 
x_417 = lean_ctor_get(x_415, 0);
x_418 = lean_expr_update_proj(x_5, x_417);
lean_ctor_set(x_415, 0, x_418);
return x_415;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_419 = lean_ctor_get(x_415, 0);
x_420 = lean_ctor_get(x_415, 1);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_415);
x_421 = lean_expr_update_proj(x_5, x_419);
x_422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_420);
return x_422;
}
}
else
{
uint8_t x_423; 
lean_dec(x_5);
x_423 = !lean_is_exclusive(x_415);
if (x_423 == 0)
{
return x_415;
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; 
x_424 = lean_ctor_get(x_415, 0);
x_425 = lean_ctor_get(x_415, 1);
lean_inc(x_425);
lean_inc(x_424);
lean_dec(x_415);
x_426 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_426, 0, x_424);
lean_ctor_set(x_426, 1, x_425);
return x_426;
}
}
}
default: 
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
lean_ctor_set(x_299, 0, x_5);
return x_299;
}
}
}
else
{
lean_object* x_427; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_427 = l_Lean_Expr_bvar___override(x_6);
lean_ctor_set(x_299, 0, x_427);
return x_299;
}
}
else
{
lean_object* x_428; uint8_t x_429; 
x_428 = lean_ctor_get(x_299, 1);
lean_inc(x_428);
lean_dec(x_299);
x_429 = l_Lean_Occurrences_contains(x_2, x_293);
lean_dec(x_293);
if (x_429 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_430; lean_object* x_431; lean_object* x_432; 
x_430 = lean_ctor_get(x_5, 0);
lean_inc(x_430);
x_431 = lean_ctor_get(x_5, 1);
lean_inc(x_431);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_432 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_430, x_6, x_7, x_8, x_9, x_10, x_11, x_428);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; 
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
lean_dec(x_432);
x_435 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_431, x_6, x_7, x_8, x_9, x_10, x_11, x_434);
if (lean_obj_tag(x_435) == 0)
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_436 = lean_ctor_get(x_435, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_435, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_438 = x_435;
} else {
 lean_dec_ref(x_435);
 x_438 = lean_box(0);
}
x_439 = lean_expr_update_app(x_5, x_433, x_436);
if (lean_is_scalar(x_438)) {
 x_440 = lean_alloc_ctor(0, 2, 0);
} else {
 x_440 = x_438;
}
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_437);
return x_440;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; 
lean_dec(x_433);
lean_dec(x_5);
x_441 = lean_ctor_get(x_435, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_435, 1);
lean_inc(x_442);
if (lean_is_exclusive(x_435)) {
 lean_ctor_release(x_435, 0);
 lean_ctor_release(x_435, 1);
 x_443 = x_435;
} else {
 lean_dec_ref(x_435);
 x_443 = lean_box(0);
}
if (lean_is_scalar(x_443)) {
 x_444 = lean_alloc_ctor(1, 2, 0);
} else {
 x_444 = x_443;
}
lean_ctor_set(x_444, 0, x_441);
lean_ctor_set(x_444, 1, x_442);
return x_444;
}
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_431);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_445 = lean_ctor_get(x_432, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_432, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_447 = x_432;
} else {
 lean_dec_ref(x_432);
 x_447 = lean_box(0);
}
if (lean_is_scalar(x_447)) {
 x_448 = lean_alloc_ctor(1, 2, 0);
} else {
 x_448 = x_447;
}
lean_ctor_set(x_448, 0, x_445);
lean_ctor_set(x_448, 1, x_446);
return x_448;
}
}
case 6:
{
lean_object* x_449; lean_object* x_450; uint8_t x_451; lean_object* x_452; 
x_449 = lean_ctor_get(x_5, 1);
lean_inc(x_449);
x_450 = lean_ctor_get(x_5, 2);
lean_inc(x_450);
x_451 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_452 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_449, x_6, x_7, x_8, x_9, x_10, x_11, x_428);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
lean_dec(x_452);
x_455 = lean_nat_add(x_6, x_295);
lean_dec(x_6);
x_456 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_450, x_455, x_7, x_8, x_9, x_10, x_11, x_454);
if (lean_obj_tag(x_456) == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_457 = lean_ctor_get(x_456, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_456, 1);
lean_inc(x_458);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 lean_ctor_release(x_456, 1);
 x_459 = x_456;
} else {
 lean_dec_ref(x_456);
 x_459 = lean_box(0);
}
x_460 = lean_expr_update_lambda(x_5, x_451, x_453, x_457);
if (lean_is_scalar(x_459)) {
 x_461 = lean_alloc_ctor(0, 2, 0);
} else {
 x_461 = x_459;
}
lean_ctor_set(x_461, 0, x_460);
lean_ctor_set(x_461, 1, x_458);
return x_461;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_453);
lean_dec(x_5);
x_462 = lean_ctor_get(x_456, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_456, 1);
lean_inc(x_463);
if (lean_is_exclusive(x_456)) {
 lean_ctor_release(x_456, 0);
 lean_ctor_release(x_456, 1);
 x_464 = x_456;
} else {
 lean_dec_ref(x_456);
 x_464 = lean_box(0);
}
if (lean_is_scalar(x_464)) {
 x_465 = lean_alloc_ctor(1, 2, 0);
} else {
 x_465 = x_464;
}
lean_ctor_set(x_465, 0, x_462);
lean_ctor_set(x_465, 1, x_463);
return x_465;
}
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
lean_dec(x_450);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_466 = lean_ctor_get(x_452, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_452, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_452)) {
 lean_ctor_release(x_452, 0);
 lean_ctor_release(x_452, 1);
 x_468 = x_452;
} else {
 lean_dec_ref(x_452);
 x_468 = lean_box(0);
}
if (lean_is_scalar(x_468)) {
 x_469 = lean_alloc_ctor(1, 2, 0);
} else {
 x_469 = x_468;
}
lean_ctor_set(x_469, 0, x_466);
lean_ctor_set(x_469, 1, x_467);
return x_469;
}
}
case 7:
{
lean_object* x_470; lean_object* x_471; uint8_t x_472; lean_object* x_473; 
x_470 = lean_ctor_get(x_5, 1);
lean_inc(x_470);
x_471 = lean_ctor_get(x_5, 2);
lean_inc(x_471);
x_472 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_473 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_470, x_6, x_7, x_8, x_9, x_10, x_11, x_428);
if (lean_obj_tag(x_473) == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_474 = lean_ctor_get(x_473, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_473, 1);
lean_inc(x_475);
lean_dec(x_473);
x_476 = lean_nat_add(x_6, x_295);
lean_dec(x_6);
x_477 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_471, x_476, x_7, x_8, x_9, x_10, x_11, x_475);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
x_479 = lean_ctor_get(x_477, 1);
lean_inc(x_479);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 x_480 = x_477;
} else {
 lean_dec_ref(x_477);
 x_480 = lean_box(0);
}
x_481 = lean_expr_update_forall(x_5, x_472, x_474, x_478);
if (lean_is_scalar(x_480)) {
 x_482 = lean_alloc_ctor(0, 2, 0);
} else {
 x_482 = x_480;
}
lean_ctor_set(x_482, 0, x_481);
lean_ctor_set(x_482, 1, x_479);
return x_482;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec(x_474);
lean_dec(x_5);
x_483 = lean_ctor_get(x_477, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_477, 1);
lean_inc(x_484);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 x_485 = x_477;
} else {
 lean_dec_ref(x_477);
 x_485 = lean_box(0);
}
if (lean_is_scalar(x_485)) {
 x_486 = lean_alloc_ctor(1, 2, 0);
} else {
 x_486 = x_485;
}
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_484);
return x_486;
}
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
lean_dec(x_471);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_487 = lean_ctor_get(x_473, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_473, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_473)) {
 lean_ctor_release(x_473, 0);
 lean_ctor_release(x_473, 1);
 x_489 = x_473;
} else {
 lean_dec_ref(x_473);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(1, 2, 0);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_488);
return x_490;
}
}
case 8:
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_491 = lean_ctor_get(x_5, 1);
lean_inc(x_491);
x_492 = lean_ctor_get(x_5, 2);
lean_inc(x_492);
x_493 = lean_ctor_get(x_5, 3);
lean_inc(x_493);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_494 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_491, x_6, x_7, x_8, x_9, x_10, x_11, x_428);
if (lean_obj_tag(x_494) == 0)
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; 
x_495 = lean_ctor_get(x_494, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_494, 1);
lean_inc(x_496);
lean_dec(x_494);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_497 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_492, x_6, x_7, x_8, x_9, x_10, x_11, x_496);
if (lean_obj_tag(x_497) == 0)
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_498 = lean_ctor_get(x_497, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_497, 1);
lean_inc(x_499);
lean_dec(x_497);
x_500 = lean_nat_add(x_6, x_295);
lean_dec(x_6);
x_501 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_493, x_500, x_7, x_8, x_9, x_10, x_11, x_499);
if (lean_obj_tag(x_501) == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
x_503 = lean_ctor_get(x_501, 1);
lean_inc(x_503);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 x_504 = x_501;
} else {
 lean_dec_ref(x_501);
 x_504 = lean_box(0);
}
x_505 = lean_expr_update_let(x_5, x_495, x_498, x_502);
if (lean_is_scalar(x_504)) {
 x_506 = lean_alloc_ctor(0, 2, 0);
} else {
 x_506 = x_504;
}
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_503);
return x_506;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_dec(x_498);
lean_dec(x_495);
lean_dec(x_5);
x_507 = lean_ctor_get(x_501, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_501, 1);
lean_inc(x_508);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 x_509 = x_501;
} else {
 lean_dec_ref(x_501);
 x_509 = lean_box(0);
}
if (lean_is_scalar(x_509)) {
 x_510 = lean_alloc_ctor(1, 2, 0);
} else {
 x_510 = x_509;
}
lean_ctor_set(x_510, 0, x_507);
lean_ctor_set(x_510, 1, x_508);
return x_510;
}
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; 
lean_dec(x_495);
lean_dec(x_493);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_511 = lean_ctor_get(x_497, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_497, 1);
lean_inc(x_512);
if (lean_is_exclusive(x_497)) {
 lean_ctor_release(x_497, 0);
 lean_ctor_release(x_497, 1);
 x_513 = x_497;
} else {
 lean_dec_ref(x_497);
 x_513 = lean_box(0);
}
if (lean_is_scalar(x_513)) {
 x_514 = lean_alloc_ctor(1, 2, 0);
} else {
 x_514 = x_513;
}
lean_ctor_set(x_514, 0, x_511);
lean_ctor_set(x_514, 1, x_512);
return x_514;
}
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; 
lean_dec(x_493);
lean_dec(x_492);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_515 = lean_ctor_get(x_494, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_494, 1);
lean_inc(x_516);
if (lean_is_exclusive(x_494)) {
 lean_ctor_release(x_494, 0);
 lean_ctor_release(x_494, 1);
 x_517 = x_494;
} else {
 lean_dec_ref(x_494);
 x_517 = lean_box(0);
}
if (lean_is_scalar(x_517)) {
 x_518 = lean_alloc_ctor(1, 2, 0);
} else {
 x_518 = x_517;
}
lean_ctor_set(x_518, 0, x_515);
lean_ctor_set(x_518, 1, x_516);
return x_518;
}
}
case 10:
{
lean_object* x_519; lean_object* x_520; 
x_519 = lean_ctor_get(x_5, 1);
lean_inc(x_519);
x_520 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_519, x_6, x_7, x_8, x_9, x_10, x_11, x_428);
if (lean_obj_tag(x_520) == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_520, 1);
lean_inc(x_522);
if (lean_is_exclusive(x_520)) {
 lean_ctor_release(x_520, 0);
 lean_ctor_release(x_520, 1);
 x_523 = x_520;
} else {
 lean_dec_ref(x_520);
 x_523 = lean_box(0);
}
x_524 = lean_expr_update_mdata(x_5, x_521);
if (lean_is_scalar(x_523)) {
 x_525 = lean_alloc_ctor(0, 2, 0);
} else {
 x_525 = x_523;
}
lean_ctor_set(x_525, 0, x_524);
lean_ctor_set(x_525, 1, x_522);
return x_525;
}
else
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
lean_dec(x_5);
x_526 = lean_ctor_get(x_520, 0);
lean_inc(x_526);
x_527 = lean_ctor_get(x_520, 1);
lean_inc(x_527);
if (lean_is_exclusive(x_520)) {
 lean_ctor_release(x_520, 0);
 lean_ctor_release(x_520, 1);
 x_528 = x_520;
} else {
 lean_dec_ref(x_520);
 x_528 = lean_box(0);
}
if (lean_is_scalar(x_528)) {
 x_529 = lean_alloc_ctor(1, 2, 0);
} else {
 x_529 = x_528;
}
lean_ctor_set(x_529, 0, x_526);
lean_ctor_set(x_529, 1, x_527);
return x_529;
}
}
case 11:
{
lean_object* x_530; lean_object* x_531; 
x_530 = lean_ctor_get(x_5, 2);
lean_inc(x_530);
x_531 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_530, x_6, x_7, x_8, x_9, x_10, x_11, x_428);
if (lean_obj_tag(x_531) == 0)
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_532 = lean_ctor_get(x_531, 0);
lean_inc(x_532);
x_533 = lean_ctor_get(x_531, 1);
lean_inc(x_533);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 lean_ctor_release(x_531, 1);
 x_534 = x_531;
} else {
 lean_dec_ref(x_531);
 x_534 = lean_box(0);
}
x_535 = lean_expr_update_proj(x_5, x_532);
if (lean_is_scalar(x_534)) {
 x_536 = lean_alloc_ctor(0, 2, 0);
} else {
 x_536 = x_534;
}
lean_ctor_set(x_536, 0, x_535);
lean_ctor_set(x_536, 1, x_533);
return x_536;
}
else
{
lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; 
lean_dec(x_5);
x_537 = lean_ctor_get(x_531, 0);
lean_inc(x_537);
x_538 = lean_ctor_get(x_531, 1);
lean_inc(x_538);
if (lean_is_exclusive(x_531)) {
 lean_ctor_release(x_531, 0);
 lean_ctor_release(x_531, 1);
 x_539 = x_531;
} else {
 lean_dec_ref(x_531);
 x_539 = lean_box(0);
}
if (lean_is_scalar(x_539)) {
 x_540 = lean_alloc_ctor(1, 2, 0);
} else {
 x_540 = x_539;
}
lean_ctor_set(x_540, 0, x_537);
lean_ctor_set(x_540, 1, x_538);
return x_540;
}
}
default: 
{
lean_object* x_541; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_541 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_541, 0, x_5);
lean_ctor_set(x_541, 1, x_428);
return x_541;
}
}
}
else
{
lean_object* x_542; lean_object* x_543; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_542 = l_Lean_Expr_bvar___override(x_6);
x_543 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_428);
return x_543;
}
}
}
}
else
{
uint8_t x_544; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_544 = !lean_is_exclusive(x_150);
if (x_544 == 0)
{
return x_150;
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_545 = lean_ctor_get(x_150, 0);
x_546 = lean_ctor_get(x_150, 1);
lean_inc(x_546);
lean_inc(x_545);
lean_dec(x_150);
x_547 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_547, 0, x_545);
lean_ctor_set(x_547, 1, x_546);
return x_547;
}
}
}
}
}
else
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_548 = lean_ctor_get(x_5, 0);
lean_inc(x_548);
x_549 = lean_ctor_get(x_5, 1);
lean_inc(x_549);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_550 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_548, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_550) == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; 
x_551 = lean_ctor_get(x_550, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_550, 1);
lean_inc(x_552);
lean_dec(x_550);
x_553 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_549, x_6, x_7, x_8, x_9, x_10, x_11, x_552);
if (lean_obj_tag(x_553) == 0)
{
uint8_t x_554; 
x_554 = !lean_is_exclusive(x_553);
if (x_554 == 0)
{
lean_object* x_555; lean_object* x_556; 
x_555 = lean_ctor_get(x_553, 0);
x_556 = lean_expr_update_app(x_5, x_551, x_555);
lean_ctor_set(x_553, 0, x_556);
return x_553;
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
x_557 = lean_ctor_get(x_553, 0);
x_558 = lean_ctor_get(x_553, 1);
lean_inc(x_558);
lean_inc(x_557);
lean_dec(x_553);
x_559 = lean_expr_update_app(x_5, x_551, x_557);
x_560 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_560, 0, x_559);
lean_ctor_set(x_560, 1, x_558);
return x_560;
}
}
else
{
uint8_t x_561; 
lean_dec(x_551);
lean_dec(x_5);
x_561 = !lean_is_exclusive(x_553);
if (x_561 == 0)
{
return x_553;
}
else
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_562 = lean_ctor_get(x_553, 0);
x_563 = lean_ctor_get(x_553, 1);
lean_inc(x_563);
lean_inc(x_562);
lean_dec(x_553);
x_564 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_564, 0, x_562);
lean_ctor_set(x_564, 1, x_563);
return x_564;
}
}
}
else
{
uint8_t x_565; 
lean_dec(x_549);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_565 = !lean_is_exclusive(x_550);
if (x_565 == 0)
{
return x_550;
}
else
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; 
x_566 = lean_ctor_get(x_550, 0);
x_567 = lean_ctor_get(x_550, 1);
lean_inc(x_567);
lean_inc(x_566);
lean_dec(x_550);
x_568 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_568, 0, x_566);
lean_ctor_set(x_568, 1, x_567);
return x_568;
}
}
}
case 6:
{
lean_object* x_569; lean_object* x_570; uint8_t x_571; lean_object* x_572; 
x_569 = lean_ctor_get(x_5, 1);
lean_inc(x_569);
x_570 = lean_ctor_get(x_5, 2);
lean_inc(x_570);
x_571 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_572 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_569, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_572) == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_573 = lean_ctor_get(x_572, 0);
lean_inc(x_573);
x_574 = lean_ctor_get(x_572, 1);
lean_inc(x_574);
lean_dec(x_572);
x_575 = lean_unsigned_to_nat(1u);
x_576 = lean_nat_add(x_6, x_575);
lean_dec(x_6);
x_577 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_570, x_576, x_7, x_8, x_9, x_10, x_11, x_574);
if (lean_obj_tag(x_577) == 0)
{
uint8_t x_578; 
x_578 = !lean_is_exclusive(x_577);
if (x_578 == 0)
{
lean_object* x_579; lean_object* x_580; 
x_579 = lean_ctor_get(x_577, 0);
x_580 = lean_expr_update_lambda(x_5, x_571, x_573, x_579);
lean_ctor_set(x_577, 0, x_580);
return x_577;
}
else
{
lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_581 = lean_ctor_get(x_577, 0);
x_582 = lean_ctor_get(x_577, 1);
lean_inc(x_582);
lean_inc(x_581);
lean_dec(x_577);
x_583 = lean_expr_update_lambda(x_5, x_571, x_573, x_581);
x_584 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_584, 0, x_583);
lean_ctor_set(x_584, 1, x_582);
return x_584;
}
}
else
{
uint8_t x_585; 
lean_dec(x_573);
lean_dec(x_5);
x_585 = !lean_is_exclusive(x_577);
if (x_585 == 0)
{
return x_577;
}
else
{
lean_object* x_586; lean_object* x_587; lean_object* x_588; 
x_586 = lean_ctor_get(x_577, 0);
x_587 = lean_ctor_get(x_577, 1);
lean_inc(x_587);
lean_inc(x_586);
lean_dec(x_577);
x_588 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_588, 0, x_586);
lean_ctor_set(x_588, 1, x_587);
return x_588;
}
}
}
else
{
uint8_t x_589; 
lean_dec(x_570);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_589 = !lean_is_exclusive(x_572);
if (x_589 == 0)
{
return x_572;
}
else
{
lean_object* x_590; lean_object* x_591; lean_object* x_592; 
x_590 = lean_ctor_get(x_572, 0);
x_591 = lean_ctor_get(x_572, 1);
lean_inc(x_591);
lean_inc(x_590);
lean_dec(x_572);
x_592 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_592, 0, x_590);
lean_ctor_set(x_592, 1, x_591);
return x_592;
}
}
}
case 7:
{
lean_object* x_593; lean_object* x_594; uint8_t x_595; lean_object* x_596; 
x_593 = lean_ctor_get(x_5, 1);
lean_inc(x_593);
x_594 = lean_ctor_get(x_5, 2);
lean_inc(x_594);
x_595 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_596 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_593, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_596) == 0)
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; 
x_597 = lean_ctor_get(x_596, 0);
lean_inc(x_597);
x_598 = lean_ctor_get(x_596, 1);
lean_inc(x_598);
lean_dec(x_596);
x_599 = lean_unsigned_to_nat(1u);
x_600 = lean_nat_add(x_6, x_599);
lean_dec(x_6);
x_601 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_594, x_600, x_7, x_8, x_9, x_10, x_11, x_598);
if (lean_obj_tag(x_601) == 0)
{
uint8_t x_602; 
x_602 = !lean_is_exclusive(x_601);
if (x_602 == 0)
{
lean_object* x_603; lean_object* x_604; 
x_603 = lean_ctor_get(x_601, 0);
x_604 = lean_expr_update_forall(x_5, x_595, x_597, x_603);
lean_ctor_set(x_601, 0, x_604);
return x_601;
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_605 = lean_ctor_get(x_601, 0);
x_606 = lean_ctor_get(x_601, 1);
lean_inc(x_606);
lean_inc(x_605);
lean_dec(x_601);
x_607 = lean_expr_update_forall(x_5, x_595, x_597, x_605);
x_608 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_608, 0, x_607);
lean_ctor_set(x_608, 1, x_606);
return x_608;
}
}
else
{
uint8_t x_609; 
lean_dec(x_597);
lean_dec(x_5);
x_609 = !lean_is_exclusive(x_601);
if (x_609 == 0)
{
return x_601;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_610 = lean_ctor_get(x_601, 0);
x_611 = lean_ctor_get(x_601, 1);
lean_inc(x_611);
lean_inc(x_610);
lean_dec(x_601);
x_612 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_612, 0, x_610);
lean_ctor_set(x_612, 1, x_611);
return x_612;
}
}
}
else
{
uint8_t x_613; 
lean_dec(x_594);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_613 = !lean_is_exclusive(x_596);
if (x_613 == 0)
{
return x_596;
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; 
x_614 = lean_ctor_get(x_596, 0);
x_615 = lean_ctor_get(x_596, 1);
lean_inc(x_615);
lean_inc(x_614);
lean_dec(x_596);
x_616 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_616, 0, x_614);
lean_ctor_set(x_616, 1, x_615);
return x_616;
}
}
}
case 8:
{
lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
x_617 = lean_ctor_get(x_5, 1);
lean_inc(x_617);
x_618 = lean_ctor_get(x_5, 2);
lean_inc(x_618);
x_619 = lean_ctor_get(x_5, 3);
lean_inc(x_619);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_620 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_617, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_620) == 0)
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; 
x_621 = lean_ctor_get(x_620, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_620, 1);
lean_inc(x_622);
lean_dec(x_620);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_623 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_618, x_6, x_7, x_8, x_9, x_10, x_11, x_622);
if (lean_obj_tag(x_623) == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_624 = lean_ctor_get(x_623, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_623, 1);
lean_inc(x_625);
lean_dec(x_623);
x_626 = lean_unsigned_to_nat(1u);
x_627 = lean_nat_add(x_6, x_626);
lean_dec(x_6);
x_628 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_619, x_627, x_7, x_8, x_9, x_10, x_11, x_625);
if (lean_obj_tag(x_628) == 0)
{
uint8_t x_629; 
x_629 = !lean_is_exclusive(x_628);
if (x_629 == 0)
{
lean_object* x_630; lean_object* x_631; 
x_630 = lean_ctor_get(x_628, 0);
x_631 = lean_expr_update_let(x_5, x_621, x_624, x_630);
lean_ctor_set(x_628, 0, x_631);
return x_628;
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; 
x_632 = lean_ctor_get(x_628, 0);
x_633 = lean_ctor_get(x_628, 1);
lean_inc(x_633);
lean_inc(x_632);
lean_dec(x_628);
x_634 = lean_expr_update_let(x_5, x_621, x_624, x_632);
x_635 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_635, 0, x_634);
lean_ctor_set(x_635, 1, x_633);
return x_635;
}
}
else
{
uint8_t x_636; 
lean_dec(x_624);
lean_dec(x_621);
lean_dec(x_5);
x_636 = !lean_is_exclusive(x_628);
if (x_636 == 0)
{
return x_628;
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; 
x_637 = lean_ctor_get(x_628, 0);
x_638 = lean_ctor_get(x_628, 1);
lean_inc(x_638);
lean_inc(x_637);
lean_dec(x_628);
x_639 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_639, 0, x_637);
lean_ctor_set(x_639, 1, x_638);
return x_639;
}
}
}
else
{
uint8_t x_640; 
lean_dec(x_621);
lean_dec(x_619);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_640 = !lean_is_exclusive(x_623);
if (x_640 == 0)
{
return x_623;
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_641 = lean_ctor_get(x_623, 0);
x_642 = lean_ctor_get(x_623, 1);
lean_inc(x_642);
lean_inc(x_641);
lean_dec(x_623);
x_643 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_643, 0, x_641);
lean_ctor_set(x_643, 1, x_642);
return x_643;
}
}
}
else
{
uint8_t x_644; 
lean_dec(x_619);
lean_dec(x_618);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_644 = !lean_is_exclusive(x_620);
if (x_644 == 0)
{
return x_620;
}
else
{
lean_object* x_645; lean_object* x_646; lean_object* x_647; 
x_645 = lean_ctor_get(x_620, 0);
x_646 = lean_ctor_get(x_620, 1);
lean_inc(x_646);
lean_inc(x_645);
lean_dec(x_620);
x_647 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_647, 0, x_645);
lean_ctor_set(x_647, 1, x_646);
return x_647;
}
}
}
case 10:
{
lean_object* x_648; lean_object* x_649; 
x_648 = lean_ctor_get(x_5, 1);
lean_inc(x_648);
x_649 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_648, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_649) == 0)
{
uint8_t x_650; 
x_650 = !lean_is_exclusive(x_649);
if (x_650 == 0)
{
lean_object* x_651; lean_object* x_652; 
x_651 = lean_ctor_get(x_649, 0);
x_652 = lean_expr_update_mdata(x_5, x_651);
lean_ctor_set(x_649, 0, x_652);
return x_649;
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_653 = lean_ctor_get(x_649, 0);
x_654 = lean_ctor_get(x_649, 1);
lean_inc(x_654);
lean_inc(x_653);
lean_dec(x_649);
x_655 = lean_expr_update_mdata(x_5, x_653);
x_656 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_656, 0, x_655);
lean_ctor_set(x_656, 1, x_654);
return x_656;
}
}
else
{
uint8_t x_657; 
lean_dec(x_5);
x_657 = !lean_is_exclusive(x_649);
if (x_657 == 0)
{
return x_649;
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_658 = lean_ctor_get(x_649, 0);
x_659 = lean_ctor_get(x_649, 1);
lean_inc(x_659);
lean_inc(x_658);
lean_dec(x_649);
x_660 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_660, 0, x_658);
lean_ctor_set(x_660, 1, x_659);
return x_660;
}
}
}
case 11:
{
lean_object* x_661; lean_object* x_662; 
x_661 = lean_ctor_get(x_5, 2);
lean_inc(x_661);
x_662 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_661, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_662) == 0)
{
uint8_t x_663; 
x_663 = !lean_is_exclusive(x_662);
if (x_663 == 0)
{
lean_object* x_664; lean_object* x_665; 
x_664 = lean_ctor_get(x_662, 0);
x_665 = lean_expr_update_proj(x_5, x_664);
lean_ctor_set(x_662, 0, x_665);
return x_662;
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_666 = lean_ctor_get(x_662, 0);
x_667 = lean_ctor_get(x_662, 1);
lean_inc(x_667);
lean_inc(x_666);
lean_dec(x_662);
x_668 = lean_expr_update_proj(x_5, x_666);
x_669 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_669, 0, x_668);
lean_ctor_set(x_669, 1, x_667);
return x_669;
}
}
else
{
uint8_t x_670; 
lean_dec(x_5);
x_670 = !lean_is_exclusive(x_662);
if (x_670 == 0)
{
return x_662;
}
else
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; 
x_671 = lean_ctor_get(x_662, 0);
x_672 = lean_ctor_get(x_662, 1);
lean_inc(x_672);
lean_inc(x_671);
lean_dec(x_662);
x_673 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_673, 0, x_671);
lean_ctor_set(x_673, 1, x_672);
return x_673;
}
}
}
default: 
{
lean_object* x_674; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_674 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_674, 0, x_5);
lean_ctor_set(x_674, 1, x_12);
return x_674;
}
}
}
block_141:
{
lean_dec(x_13);
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_16 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_expr_update_app(x_5, x_17, x_21);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_expr_update_app(x_5, x_17, x_23);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_17);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_19);
if (x_27 == 0)
{
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 0);
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_19);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
case 6:
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_5, 2);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_38 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_35, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_6, x_41);
lean_dec(x_6);
x_43 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_36, x_42, x_7, x_8, x_9, x_10, x_11, x_40);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_expr_update_lambda(x_5, x_37, x_39, x_45);
lean_ctor_set(x_43, 0, x_46);
return x_43;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_43, 0);
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_43);
x_49 = lean_expr_update_lambda(x_5, x_37, x_39, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_39);
lean_dec(x_5);
x_51 = !lean_is_exclusive(x_43);
if (x_51 == 0)
{
return x_43;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_43, 0);
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_43);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_36);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_38);
if (x_55 == 0)
{
return x_38;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_38, 0);
x_57 = lean_ctor_get(x_38, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_38);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
case 7:
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_5, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_5, 2);
lean_inc(x_60);
x_61 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_62 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_59, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_nat_add(x_6, x_65);
lean_dec(x_6);
x_67 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_60, x_66, x_7, x_8, x_9, x_10, x_11, x_64);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_expr_update_forall(x_5, x_61, x_63, x_69);
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
x_73 = lean_expr_update_forall(x_5, x_61, x_63, x_71);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_63);
lean_dec(x_5);
x_75 = !lean_is_exclusive(x_67);
if (x_75 == 0)
{
return x_67;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_67, 0);
x_77 = lean_ctor_get(x_67, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_67);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_60);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_62);
if (x_79 == 0)
{
return x_62;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_62, 0);
x_81 = lean_ctor_get(x_62, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_62);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
case 8:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_5, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_5, 2);
lean_inc(x_84);
x_85 = lean_ctor_get(x_5, 3);
lean_inc(x_85);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_86 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_83, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_89 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_84, x_6, x_7, x_8, x_9, x_10, x_11, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_unsigned_to_nat(1u);
x_93 = lean_nat_add(x_6, x_92);
lean_dec(x_6);
x_94 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_85, x_93, x_7, x_8, x_9, x_10, x_11, x_91);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_expr_update_let(x_5, x_87, x_90, x_96);
lean_ctor_set(x_94, 0, x_97);
return x_94;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_98 = lean_ctor_get(x_94, 0);
x_99 = lean_ctor_get(x_94, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_94);
x_100 = lean_expr_update_let(x_5, x_87, x_90, x_98);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
else
{
uint8_t x_102; 
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_5);
x_102 = !lean_is_exclusive(x_94);
if (x_102 == 0)
{
return x_94;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_94, 0);
x_104 = lean_ctor_get(x_94, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_94);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_89);
if (x_106 == 0)
{
return x_89;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_89, 0);
x_108 = lean_ctor_get(x_89, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_89);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_86);
if (x_110 == 0)
{
return x_86;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_86, 0);
x_112 = lean_ctor_get(x_86, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_86);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
case 10:
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_5, 1);
lean_inc(x_114);
x_115 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_114, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_115) == 0)
{
uint8_t x_116; 
x_116 = !lean_is_exclusive(x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_ctor_get(x_115, 0);
x_118 = lean_expr_update_mdata(x_5, x_117);
lean_ctor_set(x_115, 0, x_118);
return x_115;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_119 = lean_ctor_get(x_115, 0);
x_120 = lean_ctor_get(x_115, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_115);
x_121 = lean_expr_update_mdata(x_5, x_119);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_120);
return x_122;
}
}
else
{
uint8_t x_123; 
lean_dec(x_5);
x_123 = !lean_is_exclusive(x_115);
if (x_123 == 0)
{
return x_115;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_115, 0);
x_125 = lean_ctor_get(x_115, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_115);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
case 11:
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_5, 2);
lean_inc(x_127);
x_128 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_127, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_128, 0);
x_131 = lean_expr_update_proj(x_5, x_130);
lean_ctor_set(x_128, 0, x_131);
return x_128;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_132 = lean_ctor_get(x_128, 0);
x_133 = lean_ctor_get(x_128, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_128);
x_134 = lean_expr_update_proj(x_5, x_132);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
uint8_t x_136; 
lean_dec(x_5);
x_136 = !lean_is_exclusive(x_128);
if (x_136 == 0)
{
return x_128;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_128, 0);
x_138 = lean_ctor_get(x_128, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_128);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
default: 
{
lean_object* x_140; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_5);
lean_ctor_set(x_140, 1, x_12);
return x_140;
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
static lean_object* _init_l_Lean_Meta_kabstract___closed__1() {
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
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_Expr_isFVar(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_9);
lean_inc(x_2);
x_14 = l_Lean_Expr_toHeadIndex(x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_15);
x_17 = lean_st_ref_get(x_7, x_12);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_st_mk_ref(x_19, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_7);
x_23 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_14, x_16, x_11, x_15, x_21, x_4, x_5, x_6, x_7, x_22);
lean_dec(x_16);
lean_dec(x_14);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_st_ref_get(x_7, x_25);
lean_dec(x_7);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_st_ref_get(x_21, x_27);
lean_dec(x_21);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
lean_ctor_set(x_28, 0, x_24);
return x_28;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_21);
lean_dec(x_7);
x_33 = !lean_is_exclusive(x_23);
if (x_33 == 0)
{
return x_23;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_23, 0);
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_23);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_box(0);
x_38 = l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_32_(x_3, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_9);
lean_inc(x_2);
x_39 = l_Lean_Expr_toHeadIndex(x_2);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_40);
x_42 = lean_st_ref_get(x_7, x_12);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_st_mk_ref(x_44, x_43);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_7);
x_48 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_39, x_41, x_11, x_40, x_46, x_4, x_5, x_6, x_7, x_47);
lean_dec(x_41);
lean_dec(x_39);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_st_ref_get(x_7, x_50);
lean_dec(x_7);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_53 = lean_st_ref_get(x_46, x_52);
lean_dec(x_46);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
lean_ctor_set(x_53, 0, x_49);
return x_53;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
else
{
uint8_t x_58; 
lean_dec(x_46);
lean_dec(x_7);
x_58 = !lean_is_exclusive(x_48);
if (x_58 == 0)
{
return x_48;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_48, 0);
x_60 = lean_ctor_get(x_48, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_48);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_62 = l_Lean_Meta_kabstract___closed__1;
x_63 = lean_array_push(x_62, x_2);
x_64 = lean_expr_abstract(x_11, x_63);
lean_dec(x_63);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_64);
return x_9;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_65 = lean_ctor_get(x_9, 0);
x_66 = lean_ctor_get(x_9, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_9);
x_67 = l_Lean_Expr_isFVar(x_2);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_inc(x_2);
x_68 = l_Lean_Expr_toHeadIndex(x_2);
x_69 = lean_unsigned_to_nat(0u);
x_70 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_69);
x_71 = lean_st_ref_get(x_7, x_66);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_st_mk_ref(x_73, x_72);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
lean_inc(x_7);
x_77 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_68, x_70, x_65, x_69, x_75, x_4, x_5, x_6, x_7, x_76);
lean_dec(x_70);
lean_dec(x_68);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = lean_st_ref_get(x_7, x_79);
lean_dec(x_7);
x_81 = lean_ctor_get(x_80, 1);
lean_inc(x_81);
lean_dec(x_80);
x_82 = lean_st_ref_get(x_75, x_81);
lean_dec(x_75);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_84 = x_82;
} else {
 lean_dec_ref(x_82);
 x_84 = lean_box(0);
}
if (lean_is_scalar(x_84)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_84;
}
lean_ctor_set(x_85, 0, x_78);
lean_ctor_set(x_85, 1, x_83);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_75);
lean_dec(x_7);
x_86 = lean_ctor_get(x_77, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_77, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_88 = x_77;
} else {
 lean_dec_ref(x_77);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_box(0);
x_91 = l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_32_(x_3, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_inc(x_2);
x_92 = l_Lean_Expr_toHeadIndex(x_2);
x_93 = lean_unsigned_to_nat(0u);
x_94 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_2, x_93);
x_95 = lean_st_ref_get(x_7, x_66);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_st_mk_ref(x_97, x_96);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
lean_inc(x_7);
x_101 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_92, x_94, x_65, x_93, x_99, x_4, x_5, x_6, x_7, x_100);
lean_dec(x_94);
lean_dec(x_92);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = lean_st_ref_get(x_7, x_103);
lean_dec(x_7);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_st_ref_get(x_99, x_105);
lean_dec(x_99);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_108 = x_106;
} else {
 lean_dec_ref(x_106);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_102);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_99);
lean_dec(x_7);
x_110 = lean_ctor_get(x_101, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_101, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_112 = x_101;
} else {
 lean_dec_ref(x_101);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_114 = l_Lean_Meta_kabstract___closed__1;
x_115 = lean_array_push(x_114, x_2);
x_116 = lean_expr_abstract(x_65, x_115);
lean_dec(x_115);
lean_dec(x_65);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_66);
return x_117;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_kabstract(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Occurrences(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_HeadIndex(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Occurrences(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_HeadIndex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_kabstract___closed__1 = _init_l_Lean_Meta_kabstract___closed__1();
lean_mark_persistent(l_Lean_Meta_kabstract___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
