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
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
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
lean_object* l_Lean_mkBVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_kabstract___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_146; 
x_146 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_146 == 0)
{
lean_object* x_147; uint8_t x_148; 
lean_inc(x_5);
x_147 = l_Lean_Expr_toHeadIndex(x_5);
x_148 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_66_(x_147, x_3);
lean_dec(x_147);
if (x_148 == 0)
{
lean_object* x_149; 
x_149 = lean_box(0);
x_13 = x_149;
goto block_145;
}
else
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_150 = lean_unsigned_to_nat(0u);
x_151 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_5, x_150);
x_152 = lean_nat_dec_eq(x_151, x_4);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; 
x_153 = lean_box(0);
x_13 = x_153;
goto block_145;
}
else
{
lean_object* x_154; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_5);
x_154 = l_Lean_Meta_isExprDefEq(x_5, x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; uint8_t x_156; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_unbox(x_155);
lean_dec(x_155);
if (x_156 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec(x_154);
x_158 = lean_ctor_get(x_5, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_5, 1);
lean_inc(x_159);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_160 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_158, x_6, x_7, x_8, x_9, x_10, x_11, x_157);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_159, x_6, x_7, x_8, x_9, x_10, x_11, x_162);
if (lean_obj_tag(x_163) == 0)
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_163, 0);
x_166 = lean_expr_update_app(x_5, x_161, x_165);
lean_ctor_set(x_163, 0, x_166);
return x_163;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_163, 0);
x_168 = lean_ctor_get(x_163, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_163);
x_169 = lean_expr_update_app(x_5, x_161, x_167);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
else
{
uint8_t x_171; 
lean_dec(x_161);
lean_dec(x_5);
x_171 = !lean_is_exclusive(x_163);
if (x_171 == 0)
{
return x_163;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_163, 0);
x_173 = lean_ctor_get(x_163, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_163);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_159);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_175 = !lean_is_exclusive(x_160);
if (x_175 == 0)
{
return x_160;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_160, 0);
x_177 = lean_ctor_get(x_160, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_160);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
case 6:
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; uint64_t x_182; lean_object* x_183; 
x_179 = lean_ctor_get(x_154, 1);
lean_inc(x_179);
lean_dec(x_154);
x_180 = lean_ctor_get(x_5, 1);
lean_inc(x_180);
x_181 = lean_ctor_get(x_5, 2);
lean_inc(x_181);
x_182 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_183 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_180, x_6, x_7, x_8, x_9, x_10, x_11, x_179);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
lean_dec(x_183);
x_186 = lean_unsigned_to_nat(1u);
x_187 = lean_nat_add(x_6, x_186);
lean_dec(x_6);
x_188 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_181, x_187, x_7, x_8, x_9, x_10, x_11, x_185);
if (lean_obj_tag(x_188) == 0)
{
uint8_t x_189; 
x_189 = !lean_is_exclusive(x_188);
if (x_189 == 0)
{
lean_object* x_190; uint8_t x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_188, 0);
x_191 = (uint8_t)((x_182 << 24) >> 61);
x_192 = lean_expr_update_lambda(x_5, x_191, x_184, x_190);
lean_ctor_set(x_188, 0, x_192);
return x_188;
}
else
{
lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; lean_object* x_197; 
x_193 = lean_ctor_get(x_188, 0);
x_194 = lean_ctor_get(x_188, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_188);
x_195 = (uint8_t)((x_182 << 24) >> 61);
x_196 = lean_expr_update_lambda(x_5, x_195, x_184, x_193);
x_197 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_194);
return x_197;
}
}
else
{
uint8_t x_198; 
lean_dec(x_184);
lean_dec(x_5);
x_198 = !lean_is_exclusive(x_188);
if (x_198 == 0)
{
return x_188;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_188, 0);
x_200 = lean_ctor_get(x_188, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_188);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
uint8_t x_202; 
lean_dec(x_181);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_202 = !lean_is_exclusive(x_183);
if (x_202 == 0)
{
return x_183;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_203 = lean_ctor_get(x_183, 0);
x_204 = lean_ctor_get(x_183, 1);
lean_inc(x_204);
lean_inc(x_203);
lean_dec(x_183);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
}
}
case 7:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; uint64_t x_209; lean_object* x_210; 
x_206 = lean_ctor_get(x_154, 1);
lean_inc(x_206);
lean_dec(x_154);
x_207 = lean_ctor_get(x_5, 1);
lean_inc(x_207);
x_208 = lean_ctor_get(x_5, 2);
lean_inc(x_208);
x_209 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_210 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_207, x_6, x_7, x_8, x_9, x_10, x_11, x_206);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_210, 1);
lean_inc(x_212);
lean_dec(x_210);
x_213 = lean_unsigned_to_nat(1u);
x_214 = lean_nat_add(x_6, x_213);
lean_dec(x_6);
x_215 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_208, x_214, x_7, x_8, x_9, x_10, x_11, x_212);
if (lean_obj_tag(x_215) == 0)
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_215);
if (x_216 == 0)
{
lean_object* x_217; uint8_t x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_215, 0);
x_218 = (uint8_t)((x_209 << 24) >> 61);
x_219 = lean_expr_update_forall(x_5, x_218, x_211, x_217);
lean_ctor_set(x_215, 0, x_219);
return x_215;
}
else
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; 
x_220 = lean_ctor_get(x_215, 0);
x_221 = lean_ctor_get(x_215, 1);
lean_inc(x_221);
lean_inc(x_220);
lean_dec(x_215);
x_222 = (uint8_t)((x_209 << 24) >> 61);
x_223 = lean_expr_update_forall(x_5, x_222, x_211, x_220);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_221);
return x_224;
}
}
else
{
uint8_t x_225; 
lean_dec(x_211);
lean_dec(x_5);
x_225 = !lean_is_exclusive(x_215);
if (x_225 == 0)
{
return x_215;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_ctor_get(x_215, 0);
x_227 = lean_ctor_get(x_215, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_215);
x_228 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_227);
return x_228;
}
}
}
else
{
uint8_t x_229; 
lean_dec(x_208);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_229 = !lean_is_exclusive(x_210);
if (x_229 == 0)
{
return x_210;
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_210, 0);
x_231 = lean_ctor_get(x_210, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_210);
x_232 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
return x_232;
}
}
}
case 8:
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_233 = lean_ctor_get(x_154, 1);
lean_inc(x_233);
lean_dec(x_154);
x_234 = lean_ctor_get(x_5, 1);
lean_inc(x_234);
x_235 = lean_ctor_get(x_5, 2);
lean_inc(x_235);
x_236 = lean_ctor_get(x_5, 3);
lean_inc(x_236);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_237 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_234, x_6, x_7, x_8, x_9, x_10, x_11, x_233);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_240 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_235, x_6, x_7, x_8, x_9, x_10, x_11, x_239);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = lean_unsigned_to_nat(1u);
x_244 = lean_nat_add(x_6, x_243);
lean_dec(x_6);
x_245 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_236, x_244, x_7, x_8, x_9, x_10, x_11, x_242);
if (lean_obj_tag(x_245) == 0)
{
uint8_t x_246; 
x_246 = !lean_is_exclusive(x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_245, 0);
x_248 = lean_expr_update_let(x_5, x_238, x_241, x_247);
lean_ctor_set(x_245, 0, x_248);
return x_245;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_245, 0);
x_250 = lean_ctor_get(x_245, 1);
lean_inc(x_250);
lean_inc(x_249);
lean_dec(x_245);
x_251 = lean_expr_update_let(x_5, x_238, x_241, x_249);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_250);
return x_252;
}
}
else
{
uint8_t x_253; 
lean_dec(x_241);
lean_dec(x_238);
lean_dec(x_5);
x_253 = !lean_is_exclusive(x_245);
if (x_253 == 0)
{
return x_245;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_245, 0);
x_255 = lean_ctor_get(x_245, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_245);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
else
{
uint8_t x_257; 
lean_dec(x_238);
lean_dec(x_236);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_257 = !lean_is_exclusive(x_240);
if (x_257 == 0)
{
return x_240;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_240, 0);
x_259 = lean_ctor_get(x_240, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_240);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
else
{
uint8_t x_261; 
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_261 = !lean_is_exclusive(x_237);
if (x_261 == 0)
{
return x_237;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_237, 0);
x_263 = lean_ctor_get(x_237, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_237);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
case 10:
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_154, 1);
lean_inc(x_265);
lean_dec(x_154);
x_266 = lean_ctor_get(x_5, 1);
lean_inc(x_266);
x_267 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_266, x_6, x_7, x_8, x_9, x_10, x_11, x_265);
if (lean_obj_tag(x_267) == 0)
{
uint8_t x_268; 
x_268 = !lean_is_exclusive(x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; 
x_269 = lean_ctor_get(x_267, 0);
x_270 = lean_expr_update_mdata(x_5, x_269);
lean_ctor_set(x_267, 0, x_270);
return x_267;
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_271 = lean_ctor_get(x_267, 0);
x_272 = lean_ctor_get(x_267, 1);
lean_inc(x_272);
lean_inc(x_271);
lean_dec(x_267);
x_273 = lean_expr_update_mdata(x_5, x_271);
x_274 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_274, 0, x_273);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
}
else
{
uint8_t x_275; 
lean_dec(x_5);
x_275 = !lean_is_exclusive(x_267);
if (x_275 == 0)
{
return x_267;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_267, 0);
x_277 = lean_ctor_get(x_267, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_267);
x_278 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_278, 0, x_276);
lean_ctor_set(x_278, 1, x_277);
return x_278;
}
}
}
case 11:
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_154, 1);
lean_inc(x_279);
lean_dec(x_154);
x_280 = lean_ctor_get(x_5, 2);
lean_inc(x_280);
x_281 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_280, x_6, x_7, x_8, x_9, x_10, x_11, x_279);
if (lean_obj_tag(x_281) == 0)
{
uint8_t x_282; 
x_282 = !lean_is_exclusive(x_281);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; 
x_283 = lean_ctor_get(x_281, 0);
x_284 = lean_expr_update_proj(x_5, x_283);
lean_ctor_set(x_281, 0, x_284);
return x_281;
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_285 = lean_ctor_get(x_281, 0);
x_286 = lean_ctor_get(x_281, 1);
lean_inc(x_286);
lean_inc(x_285);
lean_dec(x_281);
x_287 = lean_expr_update_proj(x_5, x_285);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
else
{
uint8_t x_289; 
lean_dec(x_5);
x_289 = !lean_is_exclusive(x_281);
if (x_289 == 0)
{
return x_281;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_281, 0);
x_291 = lean_ctor_get(x_281, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_281);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
default: 
{
uint8_t x_293; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_293 = !lean_is_exclusive(x_154);
if (x_293 == 0)
{
lean_object* x_294; 
x_294 = lean_ctor_get(x_154, 0);
lean_dec(x_294);
lean_ctor_set(x_154, 0, x_5);
return x_154;
}
else
{
lean_object* x_295; lean_object* x_296; 
x_295 = lean_ctor_get(x_154, 1);
lean_inc(x_295);
lean_dec(x_154);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_5);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; 
x_297 = lean_ctor_get(x_154, 1);
lean_inc(x_297);
lean_dec(x_154);
x_298 = lean_st_ref_get(x_11, x_297);
x_299 = lean_ctor_get(x_298, 1);
lean_inc(x_299);
lean_dec(x_298);
x_300 = lean_st_ref_get(x_7, x_299);
x_301 = lean_ctor_get(x_300, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_300, 1);
lean_inc(x_302);
lean_dec(x_300);
x_303 = lean_unsigned_to_nat(1u);
x_304 = lean_nat_add(x_301, x_303);
x_305 = lean_st_ref_get(x_11, x_302);
x_306 = lean_ctor_get(x_305, 1);
lean_inc(x_306);
lean_dec(x_305);
x_307 = lean_st_ref_set(x_7, x_304, x_306);
x_308 = !lean_is_exclusive(x_307);
if (x_308 == 0)
{
lean_object* x_309; lean_object* x_310; uint8_t x_311; 
x_309 = lean_ctor_get(x_307, 1);
x_310 = lean_ctor_get(x_307, 0);
lean_dec(x_310);
x_311 = l_Lean_Occurrences_contains(x_2, x_301);
lean_dec(x_301);
if (x_311 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_free_object(x_307);
x_312 = lean_ctor_get(x_5, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_5, 1);
lean_inc(x_313);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_314 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_312, x_6, x_7, x_8, x_9, x_10, x_11, x_309);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
x_317 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_313, x_6, x_7, x_8, x_9, x_10, x_11, x_316);
if (lean_obj_tag(x_317) == 0)
{
uint8_t x_318; 
x_318 = !lean_is_exclusive(x_317);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; 
x_319 = lean_ctor_get(x_317, 0);
x_320 = lean_expr_update_app(x_5, x_315, x_319);
lean_ctor_set(x_317, 0, x_320);
return x_317;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_321 = lean_ctor_get(x_317, 0);
x_322 = lean_ctor_get(x_317, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_317);
x_323 = lean_expr_update_app(x_5, x_315, x_321);
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_323);
lean_ctor_set(x_324, 1, x_322);
return x_324;
}
}
else
{
uint8_t x_325; 
lean_dec(x_315);
lean_dec(x_5);
x_325 = !lean_is_exclusive(x_317);
if (x_325 == 0)
{
return x_317;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_317, 0);
x_327 = lean_ctor_get(x_317, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_317);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
}
else
{
uint8_t x_329; 
lean_dec(x_313);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_329 = !lean_is_exclusive(x_314);
if (x_329 == 0)
{
return x_314;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_314, 0);
x_331 = lean_ctor_get(x_314, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_314);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
return x_332;
}
}
}
case 6:
{
lean_object* x_333; lean_object* x_334; uint64_t x_335; lean_object* x_336; 
lean_free_object(x_307);
x_333 = lean_ctor_get(x_5, 1);
lean_inc(x_333);
x_334 = lean_ctor_get(x_5, 2);
lean_inc(x_334);
x_335 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_336 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_333, x_6, x_7, x_8, x_9, x_10, x_11, x_309);
if (lean_obj_tag(x_336) == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_337 = lean_ctor_get(x_336, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_336, 1);
lean_inc(x_338);
lean_dec(x_336);
x_339 = lean_nat_add(x_6, x_303);
lean_dec(x_6);
x_340 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_334, x_339, x_7, x_8, x_9, x_10, x_11, x_338);
if (lean_obj_tag(x_340) == 0)
{
uint8_t x_341; 
x_341 = !lean_is_exclusive(x_340);
if (x_341 == 0)
{
lean_object* x_342; uint8_t x_343; lean_object* x_344; 
x_342 = lean_ctor_get(x_340, 0);
x_343 = (uint8_t)((x_335 << 24) >> 61);
x_344 = lean_expr_update_lambda(x_5, x_343, x_337, x_342);
lean_ctor_set(x_340, 0, x_344);
return x_340;
}
else
{
lean_object* x_345; lean_object* x_346; uint8_t x_347; lean_object* x_348; lean_object* x_349; 
x_345 = lean_ctor_get(x_340, 0);
x_346 = lean_ctor_get(x_340, 1);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_340);
x_347 = (uint8_t)((x_335 << 24) >> 61);
x_348 = lean_expr_update_lambda(x_5, x_347, x_337, x_345);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_346);
return x_349;
}
}
else
{
uint8_t x_350; 
lean_dec(x_337);
lean_dec(x_5);
x_350 = !lean_is_exclusive(x_340);
if (x_350 == 0)
{
return x_340;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_340, 0);
x_352 = lean_ctor_get(x_340, 1);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_340);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
return x_353;
}
}
}
else
{
uint8_t x_354; 
lean_dec(x_334);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_354 = !lean_is_exclusive(x_336);
if (x_354 == 0)
{
return x_336;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_336, 0);
x_356 = lean_ctor_get(x_336, 1);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_336);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
return x_357;
}
}
}
case 7:
{
lean_object* x_358; lean_object* x_359; uint64_t x_360; lean_object* x_361; 
lean_free_object(x_307);
x_358 = lean_ctor_get(x_5, 1);
lean_inc(x_358);
x_359 = lean_ctor_get(x_5, 2);
lean_inc(x_359);
x_360 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_361 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_358, x_6, x_7, x_8, x_9, x_10, x_11, x_309);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec(x_361);
x_364 = lean_nat_add(x_6, x_303);
lean_dec(x_6);
x_365 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_359, x_364, x_7, x_8, x_9, x_10, x_11, x_363);
if (lean_obj_tag(x_365) == 0)
{
uint8_t x_366; 
x_366 = !lean_is_exclusive(x_365);
if (x_366 == 0)
{
lean_object* x_367; uint8_t x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_365, 0);
x_368 = (uint8_t)((x_360 << 24) >> 61);
x_369 = lean_expr_update_forall(x_5, x_368, x_362, x_367);
lean_ctor_set(x_365, 0, x_369);
return x_365;
}
else
{
lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; 
x_370 = lean_ctor_get(x_365, 0);
x_371 = lean_ctor_get(x_365, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_365);
x_372 = (uint8_t)((x_360 << 24) >> 61);
x_373 = lean_expr_update_forall(x_5, x_372, x_362, x_370);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_371);
return x_374;
}
}
else
{
uint8_t x_375; 
lean_dec(x_362);
lean_dec(x_5);
x_375 = !lean_is_exclusive(x_365);
if (x_375 == 0)
{
return x_365;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_365, 0);
x_377 = lean_ctor_get(x_365, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_365);
x_378 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_378, 0, x_376);
lean_ctor_set(x_378, 1, x_377);
return x_378;
}
}
}
else
{
uint8_t x_379; 
lean_dec(x_359);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_379 = !lean_is_exclusive(x_361);
if (x_379 == 0)
{
return x_361;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_361, 0);
x_381 = lean_ctor_get(x_361, 1);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_361);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
return x_382;
}
}
}
case 8:
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; 
lean_free_object(x_307);
x_383 = lean_ctor_get(x_5, 1);
lean_inc(x_383);
x_384 = lean_ctor_get(x_5, 2);
lean_inc(x_384);
x_385 = lean_ctor_get(x_5, 3);
lean_inc(x_385);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_386 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_383, x_6, x_7, x_8, x_9, x_10, x_11, x_309);
if (lean_obj_tag(x_386) == 0)
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_386, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_386, 1);
lean_inc(x_388);
lean_dec(x_386);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_389 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_384, x_6, x_7, x_8, x_9, x_10, x_11, x_388);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
lean_dec(x_389);
x_392 = lean_nat_add(x_6, x_303);
lean_dec(x_6);
x_393 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_385, x_392, x_7, x_8, x_9, x_10, x_11, x_391);
if (lean_obj_tag(x_393) == 0)
{
uint8_t x_394; 
x_394 = !lean_is_exclusive(x_393);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; 
x_395 = lean_ctor_get(x_393, 0);
x_396 = lean_expr_update_let(x_5, x_387, x_390, x_395);
lean_ctor_set(x_393, 0, x_396);
return x_393;
}
else
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_397 = lean_ctor_get(x_393, 0);
x_398 = lean_ctor_get(x_393, 1);
lean_inc(x_398);
lean_inc(x_397);
lean_dec(x_393);
x_399 = lean_expr_update_let(x_5, x_387, x_390, x_397);
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_399);
lean_ctor_set(x_400, 1, x_398);
return x_400;
}
}
else
{
uint8_t x_401; 
lean_dec(x_390);
lean_dec(x_387);
lean_dec(x_5);
x_401 = !lean_is_exclusive(x_393);
if (x_401 == 0)
{
return x_393;
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_402 = lean_ctor_get(x_393, 0);
x_403 = lean_ctor_get(x_393, 1);
lean_inc(x_403);
lean_inc(x_402);
lean_dec(x_393);
x_404 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_404, 0, x_402);
lean_ctor_set(x_404, 1, x_403);
return x_404;
}
}
}
else
{
uint8_t x_405; 
lean_dec(x_387);
lean_dec(x_385);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_405 = !lean_is_exclusive(x_389);
if (x_405 == 0)
{
return x_389;
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_406 = lean_ctor_get(x_389, 0);
x_407 = lean_ctor_get(x_389, 1);
lean_inc(x_407);
lean_inc(x_406);
lean_dec(x_389);
x_408 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
return x_408;
}
}
}
else
{
uint8_t x_409; 
lean_dec(x_385);
lean_dec(x_384);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_409 = !lean_is_exclusive(x_386);
if (x_409 == 0)
{
return x_386;
}
else
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = lean_ctor_get(x_386, 0);
x_411 = lean_ctor_get(x_386, 1);
lean_inc(x_411);
lean_inc(x_410);
lean_dec(x_386);
x_412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
return x_412;
}
}
}
case 10:
{
lean_object* x_413; lean_object* x_414; 
lean_free_object(x_307);
x_413 = lean_ctor_get(x_5, 1);
lean_inc(x_413);
x_414 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_413, x_6, x_7, x_8, x_9, x_10, x_11, x_309);
if (lean_obj_tag(x_414) == 0)
{
uint8_t x_415; 
x_415 = !lean_is_exclusive(x_414);
if (x_415 == 0)
{
lean_object* x_416; lean_object* x_417; 
x_416 = lean_ctor_get(x_414, 0);
x_417 = lean_expr_update_mdata(x_5, x_416);
lean_ctor_set(x_414, 0, x_417);
return x_414;
}
else
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_418 = lean_ctor_get(x_414, 0);
x_419 = lean_ctor_get(x_414, 1);
lean_inc(x_419);
lean_inc(x_418);
lean_dec(x_414);
x_420 = lean_expr_update_mdata(x_5, x_418);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_419);
return x_421;
}
}
else
{
uint8_t x_422; 
lean_dec(x_5);
x_422 = !lean_is_exclusive(x_414);
if (x_422 == 0)
{
return x_414;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_414, 0);
x_424 = lean_ctor_get(x_414, 1);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_414);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
return x_425;
}
}
}
case 11:
{
lean_object* x_426; lean_object* x_427; 
lean_free_object(x_307);
x_426 = lean_ctor_get(x_5, 2);
lean_inc(x_426);
x_427 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_426, x_6, x_7, x_8, x_9, x_10, x_11, x_309);
if (lean_obj_tag(x_427) == 0)
{
uint8_t x_428; 
x_428 = !lean_is_exclusive(x_427);
if (x_428 == 0)
{
lean_object* x_429; lean_object* x_430; 
x_429 = lean_ctor_get(x_427, 0);
x_430 = lean_expr_update_proj(x_5, x_429);
lean_ctor_set(x_427, 0, x_430);
return x_427;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_431 = lean_ctor_get(x_427, 0);
x_432 = lean_ctor_get(x_427, 1);
lean_inc(x_432);
lean_inc(x_431);
lean_dec(x_427);
x_433 = lean_expr_update_proj(x_5, x_431);
x_434 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_432);
return x_434;
}
}
else
{
uint8_t x_435; 
lean_dec(x_5);
x_435 = !lean_is_exclusive(x_427);
if (x_435 == 0)
{
return x_427;
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_436 = lean_ctor_get(x_427, 0);
x_437 = lean_ctor_get(x_427, 1);
lean_inc(x_437);
lean_inc(x_436);
lean_dec(x_427);
x_438 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_437);
return x_438;
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
lean_ctor_set(x_307, 0, x_5);
return x_307;
}
}
}
else
{
lean_object* x_439; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_439 = l_Lean_mkBVar(x_6);
lean_ctor_set(x_307, 0, x_439);
return x_307;
}
}
else
{
lean_object* x_440; uint8_t x_441; 
x_440 = lean_ctor_get(x_307, 1);
lean_inc(x_440);
lean_dec(x_307);
x_441 = l_Lean_Occurrences_contains(x_2, x_301);
lean_dec(x_301);
if (x_441 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; 
x_442 = lean_ctor_get(x_5, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_5, 1);
lean_inc(x_443);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_444 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_442, x_6, x_7, x_8, x_9, x_10, x_11, x_440);
if (lean_obj_tag(x_444) == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_444, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_444, 1);
lean_inc(x_446);
lean_dec(x_444);
x_447 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_443, x_6, x_7, x_8, x_9, x_10, x_11, x_446);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_447, 1);
lean_inc(x_449);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_450 = x_447;
} else {
 lean_dec_ref(x_447);
 x_450 = lean_box(0);
}
x_451 = lean_expr_update_app(x_5, x_445, x_448);
if (lean_is_scalar(x_450)) {
 x_452 = lean_alloc_ctor(0, 2, 0);
} else {
 x_452 = x_450;
}
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_449);
return x_452;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; 
lean_dec(x_445);
lean_dec(x_5);
x_453 = lean_ctor_get(x_447, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_447, 1);
lean_inc(x_454);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_455 = x_447;
} else {
 lean_dec_ref(x_447);
 x_455 = lean_box(0);
}
if (lean_is_scalar(x_455)) {
 x_456 = lean_alloc_ctor(1, 2, 0);
} else {
 x_456 = x_455;
}
lean_ctor_set(x_456, 0, x_453);
lean_ctor_set(x_456, 1, x_454);
return x_456;
}
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_443);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_457 = lean_ctor_get(x_444, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_444, 1);
lean_inc(x_458);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_459 = x_444;
} else {
 lean_dec_ref(x_444);
 x_459 = lean_box(0);
}
if (lean_is_scalar(x_459)) {
 x_460 = lean_alloc_ctor(1, 2, 0);
} else {
 x_460 = x_459;
}
lean_ctor_set(x_460, 0, x_457);
lean_ctor_set(x_460, 1, x_458);
return x_460;
}
}
case 6:
{
lean_object* x_461; lean_object* x_462; uint64_t x_463; lean_object* x_464; 
x_461 = lean_ctor_get(x_5, 1);
lean_inc(x_461);
x_462 = lean_ctor_get(x_5, 2);
lean_inc(x_462);
x_463 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_464 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_461, x_6, x_7, x_8, x_9, x_10, x_11, x_440);
if (lean_obj_tag(x_464) == 0)
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_465 = lean_ctor_get(x_464, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_464, 1);
lean_inc(x_466);
lean_dec(x_464);
x_467 = lean_nat_add(x_6, x_303);
lean_dec(x_6);
x_468 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_462, x_467, x_7, x_8, x_9, x_10, x_11, x_466);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; uint8_t x_472; lean_object* x_473; lean_object* x_474; 
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_468, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 x_471 = x_468;
} else {
 lean_dec_ref(x_468);
 x_471 = lean_box(0);
}
x_472 = (uint8_t)((x_463 << 24) >> 61);
x_473 = lean_expr_update_lambda(x_5, x_472, x_465, x_469);
if (lean_is_scalar(x_471)) {
 x_474 = lean_alloc_ctor(0, 2, 0);
} else {
 x_474 = x_471;
}
lean_ctor_set(x_474, 0, x_473);
lean_ctor_set(x_474, 1, x_470);
return x_474;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; 
lean_dec(x_465);
lean_dec(x_5);
x_475 = lean_ctor_get(x_468, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_468, 1);
lean_inc(x_476);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 x_477 = x_468;
} else {
 lean_dec_ref(x_468);
 x_477 = lean_box(0);
}
if (lean_is_scalar(x_477)) {
 x_478 = lean_alloc_ctor(1, 2, 0);
} else {
 x_478 = x_477;
}
lean_ctor_set(x_478, 0, x_475);
lean_ctor_set(x_478, 1, x_476);
return x_478;
}
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_462);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_479 = lean_ctor_get(x_464, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_464, 1);
lean_inc(x_480);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 x_481 = x_464;
} else {
 lean_dec_ref(x_464);
 x_481 = lean_box(0);
}
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(1, 2, 0);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_479);
lean_ctor_set(x_482, 1, x_480);
return x_482;
}
}
case 7:
{
lean_object* x_483; lean_object* x_484; uint64_t x_485; lean_object* x_486; 
x_483 = lean_ctor_get(x_5, 1);
lean_inc(x_483);
x_484 = lean_ctor_get(x_5, 2);
lean_inc(x_484);
x_485 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_486 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_483, x_6, x_7, x_8, x_9, x_10, x_11, x_440);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_486, 1);
lean_inc(x_488);
lean_dec(x_486);
x_489 = lean_nat_add(x_6, x_303);
lean_dec(x_6);
x_490 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_484, x_489, x_7, x_8, x_9, x_10, x_11, x_488);
if (lean_obj_tag(x_490) == 0)
{
lean_object* x_491; lean_object* x_492; lean_object* x_493; uint8_t x_494; lean_object* x_495; lean_object* x_496; 
x_491 = lean_ctor_get(x_490, 0);
lean_inc(x_491);
x_492 = lean_ctor_get(x_490, 1);
lean_inc(x_492);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 lean_ctor_release(x_490, 1);
 x_493 = x_490;
} else {
 lean_dec_ref(x_490);
 x_493 = lean_box(0);
}
x_494 = (uint8_t)((x_485 << 24) >> 61);
x_495 = lean_expr_update_forall(x_5, x_494, x_487, x_491);
if (lean_is_scalar(x_493)) {
 x_496 = lean_alloc_ctor(0, 2, 0);
} else {
 x_496 = x_493;
}
lean_ctor_set(x_496, 0, x_495);
lean_ctor_set(x_496, 1, x_492);
return x_496;
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_487);
lean_dec(x_5);
x_497 = lean_ctor_get(x_490, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_490, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_490)) {
 lean_ctor_release(x_490, 0);
 lean_ctor_release(x_490, 1);
 x_499 = x_490;
} else {
 lean_dec_ref(x_490);
 x_499 = lean_box(0);
}
if (lean_is_scalar(x_499)) {
 x_500 = lean_alloc_ctor(1, 2, 0);
} else {
 x_500 = x_499;
}
lean_ctor_set(x_500, 0, x_497);
lean_ctor_set(x_500, 1, x_498);
return x_500;
}
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
lean_dec(x_484);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_501 = lean_ctor_get(x_486, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_486, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_486)) {
 lean_ctor_release(x_486, 0);
 lean_ctor_release(x_486, 1);
 x_503 = x_486;
} else {
 lean_dec_ref(x_486);
 x_503 = lean_box(0);
}
if (lean_is_scalar(x_503)) {
 x_504 = lean_alloc_ctor(1, 2, 0);
} else {
 x_504 = x_503;
}
lean_ctor_set(x_504, 0, x_501);
lean_ctor_set(x_504, 1, x_502);
return x_504;
}
}
case 8:
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_505 = lean_ctor_get(x_5, 1);
lean_inc(x_505);
x_506 = lean_ctor_get(x_5, 2);
lean_inc(x_506);
x_507 = lean_ctor_get(x_5, 3);
lean_inc(x_507);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_508 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_505, x_6, x_7, x_8, x_9, x_10, x_11, x_440);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec(x_508);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_511 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_506, x_6, x_7, x_8, x_9, x_10, x_11, x_510);
if (lean_obj_tag(x_511) == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_512 = lean_ctor_get(x_511, 0);
lean_inc(x_512);
x_513 = lean_ctor_get(x_511, 1);
lean_inc(x_513);
lean_dec(x_511);
x_514 = lean_nat_add(x_6, x_303);
lean_dec(x_6);
x_515 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_507, x_514, x_7, x_8, x_9, x_10, x_11, x_513);
if (lean_obj_tag(x_515) == 0)
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_516 = lean_ctor_get(x_515, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_515, 1);
lean_inc(x_517);
if (lean_is_exclusive(x_515)) {
 lean_ctor_release(x_515, 0);
 lean_ctor_release(x_515, 1);
 x_518 = x_515;
} else {
 lean_dec_ref(x_515);
 x_518 = lean_box(0);
}
x_519 = lean_expr_update_let(x_5, x_509, x_512, x_516);
if (lean_is_scalar(x_518)) {
 x_520 = lean_alloc_ctor(0, 2, 0);
} else {
 x_520 = x_518;
}
lean_ctor_set(x_520, 0, x_519);
lean_ctor_set(x_520, 1, x_517);
return x_520;
}
else
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_512);
lean_dec(x_509);
lean_dec(x_5);
x_521 = lean_ctor_get(x_515, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_515, 1);
lean_inc(x_522);
if (lean_is_exclusive(x_515)) {
 lean_ctor_release(x_515, 0);
 lean_ctor_release(x_515, 1);
 x_523 = x_515;
} else {
 lean_dec_ref(x_515);
 x_523 = lean_box(0);
}
if (lean_is_scalar(x_523)) {
 x_524 = lean_alloc_ctor(1, 2, 0);
} else {
 x_524 = x_523;
}
lean_ctor_set(x_524, 0, x_521);
lean_ctor_set(x_524, 1, x_522);
return x_524;
}
}
else
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; 
lean_dec(x_509);
lean_dec(x_507);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_525 = lean_ctor_get(x_511, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_511, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_511)) {
 lean_ctor_release(x_511, 0);
 lean_ctor_release(x_511, 1);
 x_527 = x_511;
} else {
 lean_dec_ref(x_511);
 x_527 = lean_box(0);
}
if (lean_is_scalar(x_527)) {
 x_528 = lean_alloc_ctor(1, 2, 0);
} else {
 x_528 = x_527;
}
lean_ctor_set(x_528, 0, x_525);
lean_ctor_set(x_528, 1, x_526);
return x_528;
}
}
else
{
lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; 
lean_dec(x_507);
lean_dec(x_506);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_529 = lean_ctor_get(x_508, 0);
lean_inc(x_529);
x_530 = lean_ctor_get(x_508, 1);
lean_inc(x_530);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_531 = x_508;
} else {
 lean_dec_ref(x_508);
 x_531 = lean_box(0);
}
if (lean_is_scalar(x_531)) {
 x_532 = lean_alloc_ctor(1, 2, 0);
} else {
 x_532 = x_531;
}
lean_ctor_set(x_532, 0, x_529);
lean_ctor_set(x_532, 1, x_530);
return x_532;
}
}
case 10:
{
lean_object* x_533; lean_object* x_534; 
x_533 = lean_ctor_get(x_5, 1);
lean_inc(x_533);
x_534 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_533, x_6, x_7, x_8, x_9, x_10, x_11, x_440);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
x_535 = lean_ctor_get(x_534, 0);
lean_inc(x_535);
x_536 = lean_ctor_get(x_534, 1);
lean_inc(x_536);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 lean_ctor_release(x_534, 1);
 x_537 = x_534;
} else {
 lean_dec_ref(x_534);
 x_537 = lean_box(0);
}
x_538 = lean_expr_update_mdata(x_5, x_535);
if (lean_is_scalar(x_537)) {
 x_539 = lean_alloc_ctor(0, 2, 0);
} else {
 x_539 = x_537;
}
lean_ctor_set(x_539, 0, x_538);
lean_ctor_set(x_539, 1, x_536);
return x_539;
}
else
{
lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; 
lean_dec(x_5);
x_540 = lean_ctor_get(x_534, 0);
lean_inc(x_540);
x_541 = lean_ctor_get(x_534, 1);
lean_inc(x_541);
if (lean_is_exclusive(x_534)) {
 lean_ctor_release(x_534, 0);
 lean_ctor_release(x_534, 1);
 x_542 = x_534;
} else {
 lean_dec_ref(x_534);
 x_542 = lean_box(0);
}
if (lean_is_scalar(x_542)) {
 x_543 = lean_alloc_ctor(1, 2, 0);
} else {
 x_543 = x_542;
}
lean_ctor_set(x_543, 0, x_540);
lean_ctor_set(x_543, 1, x_541);
return x_543;
}
}
case 11:
{
lean_object* x_544; lean_object* x_545; 
x_544 = lean_ctor_get(x_5, 2);
lean_inc(x_544);
x_545 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_544, x_6, x_7, x_8, x_9, x_10, x_11, x_440);
if (lean_obj_tag(x_545) == 0)
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_546 = lean_ctor_get(x_545, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_545, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 lean_ctor_release(x_545, 1);
 x_548 = x_545;
} else {
 lean_dec_ref(x_545);
 x_548 = lean_box(0);
}
x_549 = lean_expr_update_proj(x_5, x_546);
if (lean_is_scalar(x_548)) {
 x_550 = lean_alloc_ctor(0, 2, 0);
} else {
 x_550 = x_548;
}
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_547);
return x_550;
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
lean_dec(x_5);
x_551 = lean_ctor_get(x_545, 0);
lean_inc(x_551);
x_552 = lean_ctor_get(x_545, 1);
lean_inc(x_552);
if (lean_is_exclusive(x_545)) {
 lean_ctor_release(x_545, 0);
 lean_ctor_release(x_545, 1);
 x_553 = x_545;
} else {
 lean_dec_ref(x_545);
 x_553 = lean_box(0);
}
if (lean_is_scalar(x_553)) {
 x_554 = lean_alloc_ctor(1, 2, 0);
} else {
 x_554 = x_553;
}
lean_ctor_set(x_554, 0, x_551);
lean_ctor_set(x_554, 1, x_552);
return x_554;
}
}
default: 
{
lean_object* x_555; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_555 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_555, 0, x_5);
lean_ctor_set(x_555, 1, x_440);
return x_555;
}
}
}
else
{
lean_object* x_556; lean_object* x_557; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_556 = l_Lean_mkBVar(x_6);
x_557 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_557, 0, x_556);
lean_ctor_set(x_557, 1, x_440);
return x_557;
}
}
}
}
else
{
uint8_t x_558; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_558 = !lean_is_exclusive(x_154);
if (x_558 == 0)
{
return x_154;
}
else
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_559 = lean_ctor_get(x_154, 0);
x_560 = lean_ctor_get(x_154, 1);
lean_inc(x_560);
lean_inc(x_559);
lean_dec(x_154);
x_561 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_561, 0, x_559);
lean_ctor_set(x_561, 1, x_560);
return x_561;
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
lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_562 = lean_ctor_get(x_5, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_5, 1);
lean_inc(x_563);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_564 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_562, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_564, 1);
lean_inc(x_566);
lean_dec(x_564);
x_567 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_563, x_6, x_7, x_8, x_9, x_10, x_11, x_566);
if (lean_obj_tag(x_567) == 0)
{
uint8_t x_568; 
x_568 = !lean_is_exclusive(x_567);
if (x_568 == 0)
{
lean_object* x_569; lean_object* x_570; 
x_569 = lean_ctor_get(x_567, 0);
x_570 = lean_expr_update_app(x_5, x_565, x_569);
lean_ctor_set(x_567, 0, x_570);
return x_567;
}
else
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_571 = lean_ctor_get(x_567, 0);
x_572 = lean_ctor_get(x_567, 1);
lean_inc(x_572);
lean_inc(x_571);
lean_dec(x_567);
x_573 = lean_expr_update_app(x_5, x_565, x_571);
x_574 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_574, 0, x_573);
lean_ctor_set(x_574, 1, x_572);
return x_574;
}
}
else
{
uint8_t x_575; 
lean_dec(x_565);
lean_dec(x_5);
x_575 = !lean_is_exclusive(x_567);
if (x_575 == 0)
{
return x_567;
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; 
x_576 = lean_ctor_get(x_567, 0);
x_577 = lean_ctor_get(x_567, 1);
lean_inc(x_577);
lean_inc(x_576);
lean_dec(x_567);
x_578 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_578, 0, x_576);
lean_ctor_set(x_578, 1, x_577);
return x_578;
}
}
}
else
{
uint8_t x_579; 
lean_dec(x_563);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_579 = !lean_is_exclusive(x_564);
if (x_579 == 0)
{
return x_564;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_580 = lean_ctor_get(x_564, 0);
x_581 = lean_ctor_get(x_564, 1);
lean_inc(x_581);
lean_inc(x_580);
lean_dec(x_564);
x_582 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_582, 0, x_580);
lean_ctor_set(x_582, 1, x_581);
return x_582;
}
}
}
case 6:
{
lean_object* x_583; lean_object* x_584; uint64_t x_585; lean_object* x_586; 
x_583 = lean_ctor_get(x_5, 1);
lean_inc(x_583);
x_584 = lean_ctor_get(x_5, 2);
lean_inc(x_584);
x_585 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_586 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_583, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_586) == 0)
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_587 = lean_ctor_get(x_586, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_586, 1);
lean_inc(x_588);
lean_dec(x_586);
x_589 = lean_unsigned_to_nat(1u);
x_590 = lean_nat_add(x_6, x_589);
lean_dec(x_6);
x_591 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_584, x_590, x_7, x_8, x_9, x_10, x_11, x_588);
if (lean_obj_tag(x_591) == 0)
{
uint8_t x_592; 
x_592 = !lean_is_exclusive(x_591);
if (x_592 == 0)
{
lean_object* x_593; uint8_t x_594; lean_object* x_595; 
x_593 = lean_ctor_get(x_591, 0);
x_594 = (uint8_t)((x_585 << 24) >> 61);
x_595 = lean_expr_update_lambda(x_5, x_594, x_587, x_593);
lean_ctor_set(x_591, 0, x_595);
return x_591;
}
else
{
lean_object* x_596; lean_object* x_597; uint8_t x_598; lean_object* x_599; lean_object* x_600; 
x_596 = lean_ctor_get(x_591, 0);
x_597 = lean_ctor_get(x_591, 1);
lean_inc(x_597);
lean_inc(x_596);
lean_dec(x_591);
x_598 = (uint8_t)((x_585 << 24) >> 61);
x_599 = lean_expr_update_lambda(x_5, x_598, x_587, x_596);
x_600 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_600, 0, x_599);
lean_ctor_set(x_600, 1, x_597);
return x_600;
}
}
else
{
uint8_t x_601; 
lean_dec(x_587);
lean_dec(x_5);
x_601 = !lean_is_exclusive(x_591);
if (x_601 == 0)
{
return x_591;
}
else
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; 
x_602 = lean_ctor_get(x_591, 0);
x_603 = lean_ctor_get(x_591, 1);
lean_inc(x_603);
lean_inc(x_602);
lean_dec(x_591);
x_604 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_604, 0, x_602);
lean_ctor_set(x_604, 1, x_603);
return x_604;
}
}
}
else
{
uint8_t x_605; 
lean_dec(x_584);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_605 = !lean_is_exclusive(x_586);
if (x_605 == 0)
{
return x_586;
}
else
{
lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_606 = lean_ctor_get(x_586, 0);
x_607 = lean_ctor_get(x_586, 1);
lean_inc(x_607);
lean_inc(x_606);
lean_dec(x_586);
x_608 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_608, 0, x_606);
lean_ctor_set(x_608, 1, x_607);
return x_608;
}
}
}
case 7:
{
lean_object* x_609; lean_object* x_610; uint64_t x_611; lean_object* x_612; 
x_609 = lean_ctor_get(x_5, 1);
lean_inc(x_609);
x_610 = lean_ctor_get(x_5, 2);
lean_inc(x_610);
x_611 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_612 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_609, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_612) == 0)
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_613 = lean_ctor_get(x_612, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_612, 1);
lean_inc(x_614);
lean_dec(x_612);
x_615 = lean_unsigned_to_nat(1u);
x_616 = lean_nat_add(x_6, x_615);
lean_dec(x_6);
x_617 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_610, x_616, x_7, x_8, x_9, x_10, x_11, x_614);
if (lean_obj_tag(x_617) == 0)
{
uint8_t x_618; 
x_618 = !lean_is_exclusive(x_617);
if (x_618 == 0)
{
lean_object* x_619; uint8_t x_620; lean_object* x_621; 
x_619 = lean_ctor_get(x_617, 0);
x_620 = (uint8_t)((x_611 << 24) >> 61);
x_621 = lean_expr_update_forall(x_5, x_620, x_613, x_619);
lean_ctor_set(x_617, 0, x_621);
return x_617;
}
else
{
lean_object* x_622; lean_object* x_623; uint8_t x_624; lean_object* x_625; lean_object* x_626; 
x_622 = lean_ctor_get(x_617, 0);
x_623 = lean_ctor_get(x_617, 1);
lean_inc(x_623);
lean_inc(x_622);
lean_dec(x_617);
x_624 = (uint8_t)((x_611 << 24) >> 61);
x_625 = lean_expr_update_forall(x_5, x_624, x_613, x_622);
x_626 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_626, 0, x_625);
lean_ctor_set(x_626, 1, x_623);
return x_626;
}
}
else
{
uint8_t x_627; 
lean_dec(x_613);
lean_dec(x_5);
x_627 = !lean_is_exclusive(x_617);
if (x_627 == 0)
{
return x_617;
}
else
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_628 = lean_ctor_get(x_617, 0);
x_629 = lean_ctor_get(x_617, 1);
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_617);
x_630 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set(x_630, 1, x_629);
return x_630;
}
}
}
else
{
uint8_t x_631; 
lean_dec(x_610);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_631 = !lean_is_exclusive(x_612);
if (x_631 == 0)
{
return x_612;
}
else
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_632 = lean_ctor_get(x_612, 0);
x_633 = lean_ctor_get(x_612, 1);
lean_inc(x_633);
lean_inc(x_632);
lean_dec(x_612);
x_634 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_634, 0, x_632);
lean_ctor_set(x_634, 1, x_633);
return x_634;
}
}
}
case 8:
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
x_635 = lean_ctor_get(x_5, 1);
lean_inc(x_635);
x_636 = lean_ctor_get(x_5, 2);
lean_inc(x_636);
x_637 = lean_ctor_get(x_5, 3);
lean_inc(x_637);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_638 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_635, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_638, 1);
lean_inc(x_640);
lean_dec(x_638);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_641 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_636, x_6, x_7, x_8, x_9, x_10, x_11, x_640);
if (lean_obj_tag(x_641) == 0)
{
lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_642 = lean_ctor_get(x_641, 0);
lean_inc(x_642);
x_643 = lean_ctor_get(x_641, 1);
lean_inc(x_643);
lean_dec(x_641);
x_644 = lean_unsigned_to_nat(1u);
x_645 = lean_nat_add(x_6, x_644);
lean_dec(x_6);
x_646 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_637, x_645, x_7, x_8, x_9, x_10, x_11, x_643);
if (lean_obj_tag(x_646) == 0)
{
uint8_t x_647; 
x_647 = !lean_is_exclusive(x_646);
if (x_647 == 0)
{
lean_object* x_648; lean_object* x_649; 
x_648 = lean_ctor_get(x_646, 0);
x_649 = lean_expr_update_let(x_5, x_639, x_642, x_648);
lean_ctor_set(x_646, 0, x_649);
return x_646;
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
x_650 = lean_ctor_get(x_646, 0);
x_651 = lean_ctor_get(x_646, 1);
lean_inc(x_651);
lean_inc(x_650);
lean_dec(x_646);
x_652 = lean_expr_update_let(x_5, x_639, x_642, x_650);
x_653 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_653, 0, x_652);
lean_ctor_set(x_653, 1, x_651);
return x_653;
}
}
else
{
uint8_t x_654; 
lean_dec(x_642);
lean_dec(x_639);
lean_dec(x_5);
x_654 = !lean_is_exclusive(x_646);
if (x_654 == 0)
{
return x_646;
}
else
{
lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_655 = lean_ctor_get(x_646, 0);
x_656 = lean_ctor_get(x_646, 1);
lean_inc(x_656);
lean_inc(x_655);
lean_dec(x_646);
x_657 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_657, 0, x_655);
lean_ctor_set(x_657, 1, x_656);
return x_657;
}
}
}
else
{
uint8_t x_658; 
lean_dec(x_639);
lean_dec(x_637);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_658 = !lean_is_exclusive(x_641);
if (x_658 == 0)
{
return x_641;
}
else
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; 
x_659 = lean_ctor_get(x_641, 0);
x_660 = lean_ctor_get(x_641, 1);
lean_inc(x_660);
lean_inc(x_659);
lean_dec(x_641);
x_661 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_661, 0, x_659);
lean_ctor_set(x_661, 1, x_660);
return x_661;
}
}
}
else
{
uint8_t x_662; 
lean_dec(x_637);
lean_dec(x_636);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_662 = !lean_is_exclusive(x_638);
if (x_662 == 0)
{
return x_638;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_663 = lean_ctor_get(x_638, 0);
x_664 = lean_ctor_get(x_638, 1);
lean_inc(x_664);
lean_inc(x_663);
lean_dec(x_638);
x_665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_665, 0, x_663);
lean_ctor_set(x_665, 1, x_664);
return x_665;
}
}
}
case 10:
{
lean_object* x_666; lean_object* x_667; 
x_666 = lean_ctor_get(x_5, 1);
lean_inc(x_666);
x_667 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_666, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_667) == 0)
{
uint8_t x_668; 
x_668 = !lean_is_exclusive(x_667);
if (x_668 == 0)
{
lean_object* x_669; lean_object* x_670; 
x_669 = lean_ctor_get(x_667, 0);
x_670 = lean_expr_update_mdata(x_5, x_669);
lean_ctor_set(x_667, 0, x_670);
return x_667;
}
else
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
x_671 = lean_ctor_get(x_667, 0);
x_672 = lean_ctor_get(x_667, 1);
lean_inc(x_672);
lean_inc(x_671);
lean_dec(x_667);
x_673 = lean_expr_update_mdata(x_5, x_671);
x_674 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_674, 0, x_673);
lean_ctor_set(x_674, 1, x_672);
return x_674;
}
}
else
{
uint8_t x_675; 
lean_dec(x_5);
x_675 = !lean_is_exclusive(x_667);
if (x_675 == 0)
{
return x_667;
}
else
{
lean_object* x_676; lean_object* x_677; lean_object* x_678; 
x_676 = lean_ctor_get(x_667, 0);
x_677 = lean_ctor_get(x_667, 1);
lean_inc(x_677);
lean_inc(x_676);
lean_dec(x_667);
x_678 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_678, 0, x_676);
lean_ctor_set(x_678, 1, x_677);
return x_678;
}
}
}
case 11:
{
lean_object* x_679; lean_object* x_680; 
x_679 = lean_ctor_get(x_5, 2);
lean_inc(x_679);
x_680 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_679, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_680) == 0)
{
uint8_t x_681; 
x_681 = !lean_is_exclusive(x_680);
if (x_681 == 0)
{
lean_object* x_682; lean_object* x_683; 
x_682 = lean_ctor_get(x_680, 0);
x_683 = lean_expr_update_proj(x_5, x_682);
lean_ctor_set(x_680, 0, x_683);
return x_680;
}
else
{
lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_684 = lean_ctor_get(x_680, 0);
x_685 = lean_ctor_get(x_680, 1);
lean_inc(x_685);
lean_inc(x_684);
lean_dec(x_680);
x_686 = lean_expr_update_proj(x_5, x_684);
x_687 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_687, 0, x_686);
lean_ctor_set(x_687, 1, x_685);
return x_687;
}
}
else
{
uint8_t x_688; 
lean_dec(x_5);
x_688 = !lean_is_exclusive(x_680);
if (x_688 == 0)
{
return x_680;
}
else
{
lean_object* x_689; lean_object* x_690; lean_object* x_691; 
x_689 = lean_ctor_get(x_680, 0);
x_690 = lean_ctor_get(x_680, 1);
lean_inc(x_690);
lean_inc(x_689);
lean_dec(x_680);
x_691 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_691, 0, x_689);
lean_ctor_set(x_691, 1, x_690);
return x_691;
}
}
}
default: 
{
lean_object* x_692; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_692 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_692, 0, x_5);
lean_ctor_set(x_692, 1, x_12);
return x_692;
}
}
}
block_145:
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
lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_5, 2);
lean_inc(x_36);
x_37 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
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
lean_object* x_45; uint8_t x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = (uint8_t)((x_37 << 24) >> 61);
x_47 = lean_expr_update_lambda(x_5, x_46, x_39, x_45);
lean_ctor_set(x_43, 0, x_47);
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_ctor_get(x_43, 0);
x_49 = lean_ctor_get(x_43, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_43);
x_50 = (uint8_t)((x_37 << 24) >> 61);
x_51 = lean_expr_update_lambda(x_5, x_50, x_39, x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_49);
return x_52;
}
}
else
{
uint8_t x_53; 
lean_dec(x_39);
lean_dec(x_5);
x_53 = !lean_is_exclusive(x_43);
if (x_53 == 0)
{
return x_43;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_43, 0);
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_43);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_36);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_57 = !lean_is_exclusive(x_38);
if (x_57 == 0)
{
return x_38;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_38, 0);
x_59 = lean_ctor_get(x_38, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_38);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
case 7:
{
lean_object* x_61; lean_object* x_62; uint64_t x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_5, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_5, 2);
lean_inc(x_62);
x_63 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_64 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_61, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_add(x_6, x_67);
lean_dec(x_6);
x_69 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_62, x_68, x_7, x_8, x_9, x_10, x_11, x_66);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = (uint8_t)((x_63 << 24) >> 61);
x_73 = lean_expr_update_forall(x_5, x_72, x_65, x_71);
lean_ctor_set(x_69, 0, x_73);
return x_69;
}
else
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; lean_object* x_77; lean_object* x_78; 
x_74 = lean_ctor_get(x_69, 0);
x_75 = lean_ctor_get(x_69, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_69);
x_76 = (uint8_t)((x_63 << 24) >> 61);
x_77 = lean_expr_update_forall(x_5, x_76, x_65, x_74);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
}
else
{
uint8_t x_79; 
lean_dec(x_65);
lean_dec(x_5);
x_79 = !lean_is_exclusive(x_69);
if (x_79 == 0)
{
return x_69;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_69, 0);
x_81 = lean_ctor_get(x_69, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_69);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_62);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_64);
if (x_83 == 0)
{
return x_64;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_64, 0);
x_85 = lean_ctor_get(x_64, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_64);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
case 8:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_5, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_5, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_5, 3);
lean_inc(x_89);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_90 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_87, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1);
x_93 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_88, x_6, x_7, x_8, x_9, x_10, x_11, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_add(x_6, x_96);
lean_dec(x_6);
x_98 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_89, x_97, x_7, x_8, x_9, x_10, x_11, x_95);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_expr_update_let(x_5, x_91, x_94, x_100);
lean_ctor_set(x_98, 0, x_101);
return x_98;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_98, 0);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_98);
x_104 = lean_expr_update_let(x_5, x_91, x_94, x_102);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
uint8_t x_106; 
lean_dec(x_94);
lean_dec(x_91);
lean_dec(x_5);
x_106 = !lean_is_exclusive(x_98);
if (x_106 == 0)
{
return x_98;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_98, 0);
x_108 = lean_ctor_get(x_98, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_98);
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
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_93);
if (x_110 == 0)
{
return x_93;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_93, 0);
x_112 = lean_ctor_get(x_93, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_93);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_90);
if (x_114 == 0)
{
return x_90;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_90, 0);
x_116 = lean_ctor_get(x_90, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_90);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
case 10:
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_5, 1);
lean_inc(x_118);
x_119 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_118, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_119) == 0)
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_ctor_get(x_119, 0);
x_122 = lean_expr_update_mdata(x_5, x_121);
lean_ctor_set(x_119, 0, x_122);
return x_119;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_119, 0);
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_119);
x_125 = lean_expr_update_mdata(x_5, x_123);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
uint8_t x_127; 
lean_dec(x_5);
x_127 = !lean_is_exclusive(x_119);
if (x_127 == 0)
{
return x_119;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_119, 0);
x_129 = lean_ctor_get(x_119, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_119);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
case 11:
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_5, 2);
lean_inc(x_131);
x_132 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_131, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_132) == 0)
{
uint8_t x_133; 
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_132, 0);
x_135 = lean_expr_update_proj(x_5, x_134);
lean_ctor_set(x_132, 0, x_135);
return x_132;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_ctor_get(x_132, 0);
x_137 = lean_ctor_get(x_132, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_132);
x_138 = lean_expr_update_proj(x_5, x_136);
x_139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
else
{
uint8_t x_140; 
lean_dec(x_5);
x_140 = !lean_is_exclusive(x_132);
if (x_140 == 0)
{
return x_132;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_132, 0);
x_142 = lean_ctor_get(x_132, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_132);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
default: 
{
lean_object* x_144; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_5);
lean_ctor_set(x_144, 1, x_12);
return x_144;
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
