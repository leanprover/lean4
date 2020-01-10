// Lean compiler output
// Module: Init.Lean.Meta.KAbstract
// Imports: Init.Lean.Data.Occurrences Init.Lean.HeadIndex Init.Lean.Meta.ExprDefEq
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
lean_object* lean_expr_update_forall(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_HeadIndex_HeadIndex_beq(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex___main(lean_object*);
uint8_t l_Lean_Occurrences_contains(lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* l___private_Init_Lean_HeadIndex_1__headNumArgsAux___main(lean_object*, lean_object*);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_KAbstract_1__kabstractAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_216; 
x_216 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_216 == 0)
{
lean_object* x_217; uint8_t x_218; 
x_217 = l_Lean_Expr_toHeadIndex___main(x_5);
x_218 = l_Lean_HeadIndex_HeadIndex_beq(x_217, x_3);
lean_dec(x_217);
if (x_218 == 0)
{
lean_object* x_219; 
x_219 = lean_box(0);
x_10 = x_219;
goto block_215;
}
else
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_220 = lean_unsigned_to_nat(0u);
x_221 = l___private_Init_Lean_HeadIndex_1__headNumArgsAux___main(x_5, x_220);
x_222 = lean_nat_dec_eq(x_221, x_4);
lean_dec(x_221);
if (x_222 == 0)
{
lean_object* x_223; 
x_223 = lean_box(0);
x_10 = x_223;
goto block_215;
}
else
{
lean_object* x_224; 
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_5);
x_224 = l_Lean_Meta_isExprDefEq(x_5, x_2, x_8, x_9);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; uint8_t x_226; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_unbox(x_225);
lean_dec(x_225);
if (x_226 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_227 = lean_ctor_get(x_224, 1);
lean_inc(x_227);
lean_dec(x_224);
x_228 = lean_ctor_get(x_5, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_5, 1);
lean_inc(x_229);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_230 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_228, x_6, x_7, x_8, x_227);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = lean_ctor_get(x_231, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_231, 1);
lean_inc(x_234);
lean_dec(x_231);
x_235 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_229, x_6, x_234, x_8, x_232);
if (lean_obj_tag(x_235) == 0)
{
uint8_t x_236; 
x_236 = !lean_is_exclusive(x_235);
if (x_236 == 0)
{
lean_object* x_237; uint8_t x_238; 
x_237 = lean_ctor_get(x_235, 0);
x_238 = !lean_is_exclusive(x_237);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = lean_ctor_get(x_237, 0);
x_240 = lean_expr_update_app(x_5, x_233, x_239);
lean_ctor_set(x_237, 0, x_240);
return x_235;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_241 = lean_ctor_get(x_237, 0);
x_242 = lean_ctor_get(x_237, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_237);
x_243 = lean_expr_update_app(x_5, x_233, x_241);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_242);
lean_ctor_set(x_235, 0, x_244);
return x_235;
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_245 = lean_ctor_get(x_235, 0);
x_246 = lean_ctor_get(x_235, 1);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_235);
x_247 = lean_ctor_get(x_245, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_245, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_249 = x_245;
} else {
 lean_dec_ref(x_245);
 x_249 = lean_box(0);
}
x_250 = lean_expr_update_app(x_5, x_233, x_247);
if (lean_is_scalar(x_249)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_249;
}
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set(x_251, 1, x_248);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_246);
return x_252;
}
}
else
{
uint8_t x_253; 
lean_dec(x_233);
lean_dec(x_5);
x_253 = !lean_is_exclusive(x_235);
if (x_253 == 0)
{
return x_235;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_235, 0);
x_255 = lean_ctor_get(x_235, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_235);
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
lean_dec(x_229);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_257 = !lean_is_exclusive(x_230);
if (x_257 == 0)
{
return x_230;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_230, 0);
x_259 = lean_ctor_get(x_230, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_230);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
}
}
case 6:
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; uint64_t x_264; lean_object* x_265; 
x_261 = lean_ctor_get(x_224, 1);
lean_inc(x_261);
lean_dec(x_224);
x_262 = lean_ctor_get(x_5, 1);
lean_inc(x_262);
x_263 = lean_ctor_get(x_5, 2);
lean_inc(x_263);
x_264 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_265 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_262, x_6, x_7, x_8, x_261);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_268 = lean_ctor_get(x_266, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_266, 1);
lean_inc(x_269);
lean_dec(x_266);
x_270 = lean_unsigned_to_nat(1u);
x_271 = lean_nat_add(x_6, x_270);
lean_dec(x_6);
x_272 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_263, x_271, x_269, x_8, x_267);
if (lean_obj_tag(x_272) == 0)
{
uint8_t x_273; 
x_273 = !lean_is_exclusive(x_272);
if (x_273 == 0)
{
lean_object* x_274; uint8_t x_275; 
x_274 = lean_ctor_get(x_272, 0);
x_275 = !lean_is_exclusive(x_274);
if (x_275 == 0)
{
lean_object* x_276; uint8_t x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_274, 0);
x_277 = (uint8_t)((x_264 << 24) >> 61);
x_278 = lean_expr_update_lambda(x_5, x_277, x_268, x_276);
lean_ctor_set(x_274, 0, x_278);
return x_272;
}
else
{
lean_object* x_279; lean_object* x_280; uint8_t x_281; lean_object* x_282; lean_object* x_283; 
x_279 = lean_ctor_get(x_274, 0);
x_280 = lean_ctor_get(x_274, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_274);
x_281 = (uint8_t)((x_264 << 24) >> 61);
x_282 = lean_expr_update_lambda(x_5, x_281, x_268, x_279);
x_283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_280);
lean_ctor_set(x_272, 0, x_283);
return x_272;
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_284 = lean_ctor_get(x_272, 0);
x_285 = lean_ctor_get(x_272, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_272);
x_286 = lean_ctor_get(x_284, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_284, 1);
lean_inc(x_287);
if (lean_is_exclusive(x_284)) {
 lean_ctor_release(x_284, 0);
 lean_ctor_release(x_284, 1);
 x_288 = x_284;
} else {
 lean_dec_ref(x_284);
 x_288 = lean_box(0);
}
x_289 = (uint8_t)((x_264 << 24) >> 61);
x_290 = lean_expr_update_lambda(x_5, x_289, x_268, x_286);
if (lean_is_scalar(x_288)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_288;
}
lean_ctor_set(x_291, 0, x_290);
lean_ctor_set(x_291, 1, x_287);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_285);
return x_292;
}
}
else
{
uint8_t x_293; 
lean_dec(x_268);
lean_dec(x_5);
x_293 = !lean_is_exclusive(x_272);
if (x_293 == 0)
{
return x_272;
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_294 = lean_ctor_get(x_272, 0);
x_295 = lean_ctor_get(x_272, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_272);
x_296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_296, 0, x_294);
lean_ctor_set(x_296, 1, x_295);
return x_296;
}
}
}
else
{
uint8_t x_297; 
lean_dec(x_263);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_297 = !lean_is_exclusive(x_265);
if (x_297 == 0)
{
return x_265;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_265, 0);
x_299 = lean_ctor_get(x_265, 1);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_265);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
return x_300;
}
}
}
case 7:
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; uint64_t x_304; lean_object* x_305; 
x_301 = lean_ctor_get(x_224, 1);
lean_inc(x_301);
lean_dec(x_224);
x_302 = lean_ctor_get(x_5, 1);
lean_inc(x_302);
x_303 = lean_ctor_get(x_5, 2);
lean_inc(x_303);
x_304 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_305 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_302, x_6, x_7, x_8, x_301);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
x_308 = lean_ctor_get(x_306, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_306, 1);
lean_inc(x_309);
lean_dec(x_306);
x_310 = lean_unsigned_to_nat(1u);
x_311 = lean_nat_add(x_6, x_310);
lean_dec(x_6);
x_312 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_303, x_311, x_309, x_8, x_307);
if (lean_obj_tag(x_312) == 0)
{
uint8_t x_313; 
x_313 = !lean_is_exclusive(x_312);
if (x_313 == 0)
{
lean_object* x_314; uint8_t x_315; 
x_314 = lean_ctor_get(x_312, 0);
x_315 = !lean_is_exclusive(x_314);
if (x_315 == 0)
{
lean_object* x_316; uint8_t x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_314, 0);
x_317 = (uint8_t)((x_304 << 24) >> 61);
x_318 = lean_expr_update_forall(x_5, x_317, x_308, x_316);
lean_ctor_set(x_314, 0, x_318);
return x_312;
}
else
{
lean_object* x_319; lean_object* x_320; uint8_t x_321; lean_object* x_322; lean_object* x_323; 
x_319 = lean_ctor_get(x_314, 0);
x_320 = lean_ctor_get(x_314, 1);
lean_inc(x_320);
lean_inc(x_319);
lean_dec(x_314);
x_321 = (uint8_t)((x_304 << 24) >> 61);
x_322 = lean_expr_update_forall(x_5, x_321, x_308, x_319);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_322);
lean_ctor_set(x_323, 1, x_320);
lean_ctor_set(x_312, 0, x_323);
return x_312;
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_324 = lean_ctor_get(x_312, 0);
x_325 = lean_ctor_get(x_312, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_312);
x_326 = lean_ctor_get(x_324, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_324, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_324)) {
 lean_ctor_release(x_324, 0);
 lean_ctor_release(x_324, 1);
 x_328 = x_324;
} else {
 lean_dec_ref(x_324);
 x_328 = lean_box(0);
}
x_329 = (uint8_t)((x_304 << 24) >> 61);
x_330 = lean_expr_update_forall(x_5, x_329, x_308, x_326);
if (lean_is_scalar(x_328)) {
 x_331 = lean_alloc_ctor(0, 2, 0);
} else {
 x_331 = x_328;
}
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_327);
x_332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_332, 0, x_331);
lean_ctor_set(x_332, 1, x_325);
return x_332;
}
}
else
{
uint8_t x_333; 
lean_dec(x_308);
lean_dec(x_5);
x_333 = !lean_is_exclusive(x_312);
if (x_333 == 0)
{
return x_312;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_312, 0);
x_335 = lean_ctor_get(x_312, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_312);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
}
else
{
uint8_t x_337; 
lean_dec(x_303);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_337 = !lean_is_exclusive(x_305);
if (x_337 == 0)
{
return x_305;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_305, 0);
x_339 = lean_ctor_get(x_305, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_305);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
return x_340;
}
}
}
case 8:
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_341 = lean_ctor_get(x_224, 1);
lean_inc(x_341);
lean_dec(x_224);
x_342 = lean_ctor_get(x_5, 1);
lean_inc(x_342);
x_343 = lean_ctor_get(x_5, 2);
lean_inc(x_343);
x_344 = lean_ctor_get(x_5, 3);
lean_inc(x_344);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_345 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_342, x_6, x_7, x_8, x_341);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
x_348 = lean_ctor_get(x_346, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_346, 1);
lean_inc(x_349);
lean_dec(x_346);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_350 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_343, x_6, x_349, x_8, x_347);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_350, 1);
lean_inc(x_352);
lean_dec(x_350);
x_353 = lean_ctor_get(x_351, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_351, 1);
lean_inc(x_354);
lean_dec(x_351);
x_355 = lean_unsigned_to_nat(1u);
x_356 = lean_nat_add(x_6, x_355);
lean_dec(x_6);
x_357 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_344, x_356, x_354, x_8, x_352);
if (lean_obj_tag(x_357) == 0)
{
uint8_t x_358; 
x_358 = !lean_is_exclusive(x_357);
if (x_358 == 0)
{
lean_object* x_359; uint8_t x_360; 
x_359 = lean_ctor_get(x_357, 0);
x_360 = !lean_is_exclusive(x_359);
if (x_360 == 0)
{
lean_object* x_361; lean_object* x_362; 
x_361 = lean_ctor_get(x_359, 0);
x_362 = lean_expr_update_let(x_5, x_348, x_353, x_361);
lean_ctor_set(x_359, 0, x_362);
return x_357;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_363 = lean_ctor_get(x_359, 0);
x_364 = lean_ctor_get(x_359, 1);
lean_inc(x_364);
lean_inc(x_363);
lean_dec(x_359);
x_365 = lean_expr_update_let(x_5, x_348, x_353, x_363);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_364);
lean_ctor_set(x_357, 0, x_366);
return x_357;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
x_367 = lean_ctor_get(x_357, 0);
x_368 = lean_ctor_get(x_357, 1);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_357);
x_369 = lean_ctor_get(x_367, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_367, 1);
lean_inc(x_370);
if (lean_is_exclusive(x_367)) {
 lean_ctor_release(x_367, 0);
 lean_ctor_release(x_367, 1);
 x_371 = x_367;
} else {
 lean_dec_ref(x_367);
 x_371 = lean_box(0);
}
x_372 = lean_expr_update_let(x_5, x_348, x_353, x_369);
if (lean_is_scalar(x_371)) {
 x_373 = lean_alloc_ctor(0, 2, 0);
} else {
 x_373 = x_371;
}
lean_ctor_set(x_373, 0, x_372);
lean_ctor_set(x_373, 1, x_370);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_368);
return x_374;
}
}
else
{
uint8_t x_375; 
lean_dec(x_353);
lean_dec(x_348);
lean_dec(x_5);
x_375 = !lean_is_exclusive(x_357);
if (x_375 == 0)
{
return x_357;
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_376 = lean_ctor_get(x_357, 0);
x_377 = lean_ctor_get(x_357, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_357);
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
lean_dec(x_348);
lean_dec(x_344);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_379 = !lean_is_exclusive(x_350);
if (x_379 == 0)
{
return x_350;
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
x_380 = lean_ctor_get(x_350, 0);
x_381 = lean_ctor_get(x_350, 1);
lean_inc(x_381);
lean_inc(x_380);
lean_dec(x_350);
x_382 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_382, 0, x_380);
lean_ctor_set(x_382, 1, x_381);
return x_382;
}
}
}
else
{
uint8_t x_383; 
lean_dec(x_344);
lean_dec(x_343);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_383 = !lean_is_exclusive(x_345);
if (x_383 == 0)
{
return x_345;
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; 
x_384 = lean_ctor_get(x_345, 0);
x_385 = lean_ctor_get(x_345, 1);
lean_inc(x_385);
lean_inc(x_384);
lean_dec(x_345);
x_386 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_386, 0, x_384);
lean_ctor_set(x_386, 1, x_385);
return x_386;
}
}
}
case 10:
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_224, 1);
lean_inc(x_387);
lean_dec(x_224);
x_388 = lean_ctor_get(x_5, 1);
lean_inc(x_388);
x_389 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_388, x_6, x_7, x_8, x_387);
if (lean_obj_tag(x_389) == 0)
{
uint8_t x_390; 
x_390 = !lean_is_exclusive(x_389);
if (x_390 == 0)
{
lean_object* x_391; uint8_t x_392; 
x_391 = lean_ctor_get(x_389, 0);
x_392 = !lean_is_exclusive(x_391);
if (x_392 == 0)
{
lean_object* x_393; lean_object* x_394; 
x_393 = lean_ctor_get(x_391, 0);
x_394 = lean_expr_update_mdata(x_5, x_393);
lean_ctor_set(x_391, 0, x_394);
return x_389;
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_395 = lean_ctor_get(x_391, 0);
x_396 = lean_ctor_get(x_391, 1);
lean_inc(x_396);
lean_inc(x_395);
lean_dec(x_391);
x_397 = lean_expr_update_mdata(x_5, x_395);
x_398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_396);
lean_ctor_set(x_389, 0, x_398);
return x_389;
}
}
else
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_399 = lean_ctor_get(x_389, 0);
x_400 = lean_ctor_get(x_389, 1);
lean_inc(x_400);
lean_inc(x_399);
lean_dec(x_389);
x_401 = lean_ctor_get(x_399, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_399, 1);
lean_inc(x_402);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_403 = x_399;
} else {
 lean_dec_ref(x_399);
 x_403 = lean_box(0);
}
x_404 = lean_expr_update_mdata(x_5, x_401);
if (lean_is_scalar(x_403)) {
 x_405 = lean_alloc_ctor(0, 2, 0);
} else {
 x_405 = x_403;
}
lean_ctor_set(x_405, 0, x_404);
lean_ctor_set(x_405, 1, x_402);
x_406 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_400);
return x_406;
}
}
else
{
uint8_t x_407; 
lean_dec(x_5);
x_407 = !lean_is_exclusive(x_389);
if (x_407 == 0)
{
return x_389;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_389, 0);
x_409 = lean_ctor_get(x_389, 1);
lean_inc(x_409);
lean_inc(x_408);
lean_dec(x_389);
x_410 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_410, 0, x_408);
lean_ctor_set(x_410, 1, x_409);
return x_410;
}
}
}
case 11:
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_411 = lean_ctor_get(x_224, 1);
lean_inc(x_411);
lean_dec(x_224);
x_412 = lean_ctor_get(x_5, 2);
lean_inc(x_412);
x_413 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_412, x_6, x_7, x_8, x_411);
if (lean_obj_tag(x_413) == 0)
{
uint8_t x_414; 
x_414 = !lean_is_exclusive(x_413);
if (x_414 == 0)
{
lean_object* x_415; uint8_t x_416; 
x_415 = lean_ctor_get(x_413, 0);
x_416 = !lean_is_exclusive(x_415);
if (x_416 == 0)
{
lean_object* x_417; lean_object* x_418; 
x_417 = lean_ctor_get(x_415, 0);
x_418 = lean_expr_update_proj(x_5, x_417);
lean_ctor_set(x_415, 0, x_418);
return x_413;
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
lean_ctor_set(x_413, 0, x_422);
return x_413;
}
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_423 = lean_ctor_get(x_413, 0);
x_424 = lean_ctor_get(x_413, 1);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_413);
x_425 = lean_ctor_get(x_423, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_423, 1);
lean_inc(x_426);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_427 = x_423;
} else {
 lean_dec_ref(x_423);
 x_427 = lean_box(0);
}
x_428 = lean_expr_update_proj(x_5, x_425);
if (lean_is_scalar(x_427)) {
 x_429 = lean_alloc_ctor(0, 2, 0);
} else {
 x_429 = x_427;
}
lean_ctor_set(x_429, 0, x_428);
lean_ctor_set(x_429, 1, x_426);
x_430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_424);
return x_430;
}
}
else
{
uint8_t x_431; 
lean_dec(x_5);
x_431 = !lean_is_exclusive(x_413);
if (x_431 == 0)
{
return x_413;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
x_432 = lean_ctor_get(x_413, 0);
x_433 = lean_ctor_get(x_413, 1);
lean_inc(x_433);
lean_inc(x_432);
lean_dec(x_413);
x_434 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_434, 0, x_432);
lean_ctor_set(x_434, 1, x_433);
return x_434;
}
}
}
default: 
{
uint8_t x_435; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_435 = !lean_is_exclusive(x_224);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; 
x_436 = lean_ctor_get(x_224, 0);
lean_dec(x_436);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_5);
lean_ctor_set(x_437, 1, x_7);
lean_ctor_set(x_224, 0, x_437);
return x_224;
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_438 = lean_ctor_get(x_224, 1);
lean_inc(x_438);
lean_dec(x_224);
x_439 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_439, 0, x_5);
lean_ctor_set(x_439, 1, x_7);
x_440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_438);
return x_440;
}
}
}
}
else
{
uint8_t x_441; 
x_441 = !lean_is_exclusive(x_224);
if (x_441 == 0)
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; uint8_t x_446; 
x_442 = lean_ctor_get(x_224, 1);
x_443 = lean_ctor_get(x_224, 0);
lean_dec(x_443);
x_444 = lean_unsigned_to_nat(1u);
x_445 = lean_nat_add(x_7, x_444);
x_446 = l_Lean_Occurrences_contains(x_1, x_7);
lean_dec(x_7);
if (x_446 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_free_object(x_224);
x_447 = lean_ctor_get(x_5, 0);
lean_inc(x_447);
x_448 = lean_ctor_get(x_5, 1);
lean_inc(x_448);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_449 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_447, x_6, x_445, x_8, x_442);
if (lean_obj_tag(x_449) == 0)
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_450 = lean_ctor_get(x_449, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_449, 1);
lean_inc(x_451);
lean_dec(x_449);
x_452 = lean_ctor_get(x_450, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_450, 1);
lean_inc(x_453);
lean_dec(x_450);
x_454 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_448, x_6, x_453, x_8, x_451);
if (lean_obj_tag(x_454) == 0)
{
uint8_t x_455; 
x_455 = !lean_is_exclusive(x_454);
if (x_455 == 0)
{
lean_object* x_456; uint8_t x_457; 
x_456 = lean_ctor_get(x_454, 0);
x_457 = !lean_is_exclusive(x_456);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; 
x_458 = lean_ctor_get(x_456, 0);
x_459 = lean_expr_update_app(x_5, x_452, x_458);
lean_ctor_set(x_456, 0, x_459);
return x_454;
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_460 = lean_ctor_get(x_456, 0);
x_461 = lean_ctor_get(x_456, 1);
lean_inc(x_461);
lean_inc(x_460);
lean_dec(x_456);
x_462 = lean_expr_update_app(x_5, x_452, x_460);
x_463 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_463, 0, x_462);
lean_ctor_set(x_463, 1, x_461);
lean_ctor_set(x_454, 0, x_463);
return x_454;
}
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; 
x_464 = lean_ctor_get(x_454, 0);
x_465 = lean_ctor_get(x_454, 1);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_454);
x_466 = lean_ctor_get(x_464, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_464, 1);
lean_inc(x_467);
if (lean_is_exclusive(x_464)) {
 lean_ctor_release(x_464, 0);
 lean_ctor_release(x_464, 1);
 x_468 = x_464;
} else {
 lean_dec_ref(x_464);
 x_468 = lean_box(0);
}
x_469 = lean_expr_update_app(x_5, x_452, x_466);
if (lean_is_scalar(x_468)) {
 x_470 = lean_alloc_ctor(0, 2, 0);
} else {
 x_470 = x_468;
}
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set(x_470, 1, x_467);
x_471 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_471, 0, x_470);
lean_ctor_set(x_471, 1, x_465);
return x_471;
}
}
else
{
uint8_t x_472; 
lean_dec(x_452);
lean_dec(x_5);
x_472 = !lean_is_exclusive(x_454);
if (x_472 == 0)
{
return x_454;
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_473 = lean_ctor_get(x_454, 0);
x_474 = lean_ctor_get(x_454, 1);
lean_inc(x_474);
lean_inc(x_473);
lean_dec(x_454);
x_475 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_475, 0, x_473);
lean_ctor_set(x_475, 1, x_474);
return x_475;
}
}
}
else
{
uint8_t x_476; 
lean_dec(x_448);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_476 = !lean_is_exclusive(x_449);
if (x_476 == 0)
{
return x_449;
}
else
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; 
x_477 = lean_ctor_get(x_449, 0);
x_478 = lean_ctor_get(x_449, 1);
lean_inc(x_478);
lean_inc(x_477);
lean_dec(x_449);
x_479 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_479, 0, x_477);
lean_ctor_set(x_479, 1, x_478);
return x_479;
}
}
}
case 6:
{
lean_object* x_480; lean_object* x_481; uint64_t x_482; lean_object* x_483; 
lean_free_object(x_224);
x_480 = lean_ctor_get(x_5, 1);
lean_inc(x_480);
x_481 = lean_ctor_get(x_5, 2);
lean_inc(x_481);
x_482 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_483 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_480, x_6, x_445, x_8, x_442);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; 
x_484 = lean_ctor_get(x_483, 0);
lean_inc(x_484);
x_485 = lean_ctor_get(x_483, 1);
lean_inc(x_485);
lean_dec(x_483);
x_486 = lean_ctor_get(x_484, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_484, 1);
lean_inc(x_487);
lean_dec(x_484);
x_488 = lean_nat_add(x_6, x_444);
lean_dec(x_6);
x_489 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_481, x_488, x_487, x_8, x_485);
if (lean_obj_tag(x_489) == 0)
{
uint8_t x_490; 
x_490 = !lean_is_exclusive(x_489);
if (x_490 == 0)
{
lean_object* x_491; uint8_t x_492; 
x_491 = lean_ctor_get(x_489, 0);
x_492 = !lean_is_exclusive(x_491);
if (x_492 == 0)
{
lean_object* x_493; uint8_t x_494; lean_object* x_495; 
x_493 = lean_ctor_get(x_491, 0);
x_494 = (uint8_t)((x_482 << 24) >> 61);
x_495 = lean_expr_update_lambda(x_5, x_494, x_486, x_493);
lean_ctor_set(x_491, 0, x_495);
return x_489;
}
else
{
lean_object* x_496; lean_object* x_497; uint8_t x_498; lean_object* x_499; lean_object* x_500; 
x_496 = lean_ctor_get(x_491, 0);
x_497 = lean_ctor_get(x_491, 1);
lean_inc(x_497);
lean_inc(x_496);
lean_dec(x_491);
x_498 = (uint8_t)((x_482 << 24) >> 61);
x_499 = lean_expr_update_lambda(x_5, x_498, x_486, x_496);
x_500 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_497);
lean_ctor_set(x_489, 0, x_500);
return x_489;
}
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; 
x_501 = lean_ctor_get(x_489, 0);
x_502 = lean_ctor_get(x_489, 1);
lean_inc(x_502);
lean_inc(x_501);
lean_dec(x_489);
x_503 = lean_ctor_get(x_501, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_501, 1);
lean_inc(x_504);
if (lean_is_exclusive(x_501)) {
 lean_ctor_release(x_501, 0);
 lean_ctor_release(x_501, 1);
 x_505 = x_501;
} else {
 lean_dec_ref(x_501);
 x_505 = lean_box(0);
}
x_506 = (uint8_t)((x_482 << 24) >> 61);
x_507 = lean_expr_update_lambda(x_5, x_506, x_486, x_503);
if (lean_is_scalar(x_505)) {
 x_508 = lean_alloc_ctor(0, 2, 0);
} else {
 x_508 = x_505;
}
lean_ctor_set(x_508, 0, x_507);
lean_ctor_set(x_508, 1, x_504);
x_509 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_509, 0, x_508);
lean_ctor_set(x_509, 1, x_502);
return x_509;
}
}
else
{
uint8_t x_510; 
lean_dec(x_486);
lean_dec(x_5);
x_510 = !lean_is_exclusive(x_489);
if (x_510 == 0)
{
return x_489;
}
else
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; 
x_511 = lean_ctor_get(x_489, 0);
x_512 = lean_ctor_get(x_489, 1);
lean_inc(x_512);
lean_inc(x_511);
lean_dec(x_489);
x_513 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_513, 0, x_511);
lean_ctor_set(x_513, 1, x_512);
return x_513;
}
}
}
else
{
uint8_t x_514; 
lean_dec(x_481);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_514 = !lean_is_exclusive(x_483);
if (x_514 == 0)
{
return x_483;
}
else
{
lean_object* x_515; lean_object* x_516; lean_object* x_517; 
x_515 = lean_ctor_get(x_483, 0);
x_516 = lean_ctor_get(x_483, 1);
lean_inc(x_516);
lean_inc(x_515);
lean_dec(x_483);
x_517 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_517, 0, x_515);
lean_ctor_set(x_517, 1, x_516);
return x_517;
}
}
}
case 7:
{
lean_object* x_518; lean_object* x_519; uint64_t x_520; lean_object* x_521; 
lean_free_object(x_224);
x_518 = lean_ctor_get(x_5, 1);
lean_inc(x_518);
x_519 = lean_ctor_get(x_5, 2);
lean_inc(x_519);
x_520 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_521 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_518, x_6, x_445, x_8, x_442);
if (lean_obj_tag(x_521) == 0)
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; 
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_521, 1);
lean_inc(x_523);
lean_dec(x_521);
x_524 = lean_ctor_get(x_522, 0);
lean_inc(x_524);
x_525 = lean_ctor_get(x_522, 1);
lean_inc(x_525);
lean_dec(x_522);
x_526 = lean_nat_add(x_6, x_444);
lean_dec(x_6);
x_527 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_519, x_526, x_525, x_8, x_523);
if (lean_obj_tag(x_527) == 0)
{
uint8_t x_528; 
x_528 = !lean_is_exclusive(x_527);
if (x_528 == 0)
{
lean_object* x_529; uint8_t x_530; 
x_529 = lean_ctor_get(x_527, 0);
x_530 = !lean_is_exclusive(x_529);
if (x_530 == 0)
{
lean_object* x_531; uint8_t x_532; lean_object* x_533; 
x_531 = lean_ctor_get(x_529, 0);
x_532 = (uint8_t)((x_520 << 24) >> 61);
x_533 = lean_expr_update_forall(x_5, x_532, x_524, x_531);
lean_ctor_set(x_529, 0, x_533);
return x_527;
}
else
{
lean_object* x_534; lean_object* x_535; uint8_t x_536; lean_object* x_537; lean_object* x_538; 
x_534 = lean_ctor_get(x_529, 0);
x_535 = lean_ctor_get(x_529, 1);
lean_inc(x_535);
lean_inc(x_534);
lean_dec(x_529);
x_536 = (uint8_t)((x_520 << 24) >> 61);
x_537 = lean_expr_update_forall(x_5, x_536, x_524, x_534);
x_538 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_538, 0, x_537);
lean_ctor_set(x_538, 1, x_535);
lean_ctor_set(x_527, 0, x_538);
return x_527;
}
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; uint8_t x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
x_539 = lean_ctor_get(x_527, 0);
x_540 = lean_ctor_get(x_527, 1);
lean_inc(x_540);
lean_inc(x_539);
lean_dec(x_527);
x_541 = lean_ctor_get(x_539, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_539, 1);
lean_inc(x_542);
if (lean_is_exclusive(x_539)) {
 lean_ctor_release(x_539, 0);
 lean_ctor_release(x_539, 1);
 x_543 = x_539;
} else {
 lean_dec_ref(x_539);
 x_543 = lean_box(0);
}
x_544 = (uint8_t)((x_520 << 24) >> 61);
x_545 = lean_expr_update_forall(x_5, x_544, x_524, x_541);
if (lean_is_scalar(x_543)) {
 x_546 = lean_alloc_ctor(0, 2, 0);
} else {
 x_546 = x_543;
}
lean_ctor_set(x_546, 0, x_545);
lean_ctor_set(x_546, 1, x_542);
x_547 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_547, 0, x_546);
lean_ctor_set(x_547, 1, x_540);
return x_547;
}
}
else
{
uint8_t x_548; 
lean_dec(x_524);
lean_dec(x_5);
x_548 = !lean_is_exclusive(x_527);
if (x_548 == 0)
{
return x_527;
}
else
{
lean_object* x_549; lean_object* x_550; lean_object* x_551; 
x_549 = lean_ctor_get(x_527, 0);
x_550 = lean_ctor_get(x_527, 1);
lean_inc(x_550);
lean_inc(x_549);
lean_dec(x_527);
x_551 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_551, 0, x_549);
lean_ctor_set(x_551, 1, x_550);
return x_551;
}
}
}
else
{
uint8_t x_552; 
lean_dec(x_519);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_552 = !lean_is_exclusive(x_521);
if (x_552 == 0)
{
return x_521;
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_521, 0);
x_554 = lean_ctor_get(x_521, 1);
lean_inc(x_554);
lean_inc(x_553);
lean_dec(x_521);
x_555 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_555, 0, x_553);
lean_ctor_set(x_555, 1, x_554);
return x_555;
}
}
}
case 8:
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; 
lean_free_object(x_224);
x_556 = lean_ctor_get(x_5, 1);
lean_inc(x_556);
x_557 = lean_ctor_get(x_5, 2);
lean_inc(x_557);
x_558 = lean_ctor_get(x_5, 3);
lean_inc(x_558);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_559 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_556, x_6, x_445, x_8, x_442);
if (lean_obj_tag(x_559) == 0)
{
lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
x_560 = lean_ctor_get(x_559, 0);
lean_inc(x_560);
x_561 = lean_ctor_get(x_559, 1);
lean_inc(x_561);
lean_dec(x_559);
x_562 = lean_ctor_get(x_560, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_560, 1);
lean_inc(x_563);
lean_dec(x_560);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_564 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_557, x_6, x_563, x_8, x_561);
if (lean_obj_tag(x_564) == 0)
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; 
x_565 = lean_ctor_get(x_564, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_564, 1);
lean_inc(x_566);
lean_dec(x_564);
x_567 = lean_ctor_get(x_565, 0);
lean_inc(x_567);
x_568 = lean_ctor_get(x_565, 1);
lean_inc(x_568);
lean_dec(x_565);
x_569 = lean_nat_add(x_6, x_444);
lean_dec(x_6);
x_570 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_558, x_569, x_568, x_8, x_566);
if (lean_obj_tag(x_570) == 0)
{
uint8_t x_571; 
x_571 = !lean_is_exclusive(x_570);
if (x_571 == 0)
{
lean_object* x_572; uint8_t x_573; 
x_572 = lean_ctor_get(x_570, 0);
x_573 = !lean_is_exclusive(x_572);
if (x_573 == 0)
{
lean_object* x_574; lean_object* x_575; 
x_574 = lean_ctor_get(x_572, 0);
x_575 = lean_expr_update_let(x_5, x_562, x_567, x_574);
lean_ctor_set(x_572, 0, x_575);
return x_570;
}
else
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; 
x_576 = lean_ctor_get(x_572, 0);
x_577 = lean_ctor_get(x_572, 1);
lean_inc(x_577);
lean_inc(x_576);
lean_dec(x_572);
x_578 = lean_expr_update_let(x_5, x_562, x_567, x_576);
x_579 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_579, 0, x_578);
lean_ctor_set(x_579, 1, x_577);
lean_ctor_set(x_570, 0, x_579);
return x_570;
}
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; 
x_580 = lean_ctor_get(x_570, 0);
x_581 = lean_ctor_get(x_570, 1);
lean_inc(x_581);
lean_inc(x_580);
lean_dec(x_570);
x_582 = lean_ctor_get(x_580, 0);
lean_inc(x_582);
x_583 = lean_ctor_get(x_580, 1);
lean_inc(x_583);
if (lean_is_exclusive(x_580)) {
 lean_ctor_release(x_580, 0);
 lean_ctor_release(x_580, 1);
 x_584 = x_580;
} else {
 lean_dec_ref(x_580);
 x_584 = lean_box(0);
}
x_585 = lean_expr_update_let(x_5, x_562, x_567, x_582);
if (lean_is_scalar(x_584)) {
 x_586 = lean_alloc_ctor(0, 2, 0);
} else {
 x_586 = x_584;
}
lean_ctor_set(x_586, 0, x_585);
lean_ctor_set(x_586, 1, x_583);
x_587 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_587, 0, x_586);
lean_ctor_set(x_587, 1, x_581);
return x_587;
}
}
else
{
uint8_t x_588; 
lean_dec(x_567);
lean_dec(x_562);
lean_dec(x_5);
x_588 = !lean_is_exclusive(x_570);
if (x_588 == 0)
{
return x_570;
}
else
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; 
x_589 = lean_ctor_get(x_570, 0);
x_590 = lean_ctor_get(x_570, 1);
lean_inc(x_590);
lean_inc(x_589);
lean_dec(x_570);
x_591 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_591, 0, x_589);
lean_ctor_set(x_591, 1, x_590);
return x_591;
}
}
}
else
{
uint8_t x_592; 
lean_dec(x_562);
lean_dec(x_558);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_592 = !lean_is_exclusive(x_564);
if (x_592 == 0)
{
return x_564;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_593 = lean_ctor_get(x_564, 0);
x_594 = lean_ctor_get(x_564, 1);
lean_inc(x_594);
lean_inc(x_593);
lean_dec(x_564);
x_595 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_595, 0, x_593);
lean_ctor_set(x_595, 1, x_594);
return x_595;
}
}
}
else
{
uint8_t x_596; 
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_596 = !lean_is_exclusive(x_559);
if (x_596 == 0)
{
return x_559;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_597 = lean_ctor_get(x_559, 0);
x_598 = lean_ctor_get(x_559, 1);
lean_inc(x_598);
lean_inc(x_597);
lean_dec(x_559);
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_597);
lean_ctor_set(x_599, 1, x_598);
return x_599;
}
}
}
case 10:
{
lean_object* x_600; lean_object* x_601; 
lean_free_object(x_224);
x_600 = lean_ctor_get(x_5, 1);
lean_inc(x_600);
x_601 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_600, x_6, x_445, x_8, x_442);
if (lean_obj_tag(x_601) == 0)
{
uint8_t x_602; 
x_602 = !lean_is_exclusive(x_601);
if (x_602 == 0)
{
lean_object* x_603; uint8_t x_604; 
x_603 = lean_ctor_get(x_601, 0);
x_604 = !lean_is_exclusive(x_603);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; 
x_605 = lean_ctor_get(x_603, 0);
x_606 = lean_expr_update_mdata(x_5, x_605);
lean_ctor_set(x_603, 0, x_606);
return x_601;
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; 
x_607 = lean_ctor_get(x_603, 0);
x_608 = lean_ctor_get(x_603, 1);
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_603);
x_609 = lean_expr_update_mdata(x_5, x_607);
x_610 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_610, 0, x_609);
lean_ctor_set(x_610, 1, x_608);
lean_ctor_set(x_601, 0, x_610);
return x_601;
}
}
else
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; 
x_611 = lean_ctor_get(x_601, 0);
x_612 = lean_ctor_get(x_601, 1);
lean_inc(x_612);
lean_inc(x_611);
lean_dec(x_601);
x_613 = lean_ctor_get(x_611, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_611, 1);
lean_inc(x_614);
if (lean_is_exclusive(x_611)) {
 lean_ctor_release(x_611, 0);
 lean_ctor_release(x_611, 1);
 x_615 = x_611;
} else {
 lean_dec_ref(x_611);
 x_615 = lean_box(0);
}
x_616 = lean_expr_update_mdata(x_5, x_613);
if (lean_is_scalar(x_615)) {
 x_617 = lean_alloc_ctor(0, 2, 0);
} else {
 x_617 = x_615;
}
lean_ctor_set(x_617, 0, x_616);
lean_ctor_set(x_617, 1, x_614);
x_618 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_618, 0, x_617);
lean_ctor_set(x_618, 1, x_612);
return x_618;
}
}
else
{
uint8_t x_619; 
lean_dec(x_5);
x_619 = !lean_is_exclusive(x_601);
if (x_619 == 0)
{
return x_601;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_620 = lean_ctor_get(x_601, 0);
x_621 = lean_ctor_get(x_601, 1);
lean_inc(x_621);
lean_inc(x_620);
lean_dec(x_601);
x_622 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_622, 0, x_620);
lean_ctor_set(x_622, 1, x_621);
return x_622;
}
}
}
case 11:
{
lean_object* x_623; lean_object* x_624; 
lean_free_object(x_224);
x_623 = lean_ctor_get(x_5, 2);
lean_inc(x_623);
x_624 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_623, x_6, x_445, x_8, x_442);
if (lean_obj_tag(x_624) == 0)
{
uint8_t x_625; 
x_625 = !lean_is_exclusive(x_624);
if (x_625 == 0)
{
lean_object* x_626; uint8_t x_627; 
x_626 = lean_ctor_get(x_624, 0);
x_627 = !lean_is_exclusive(x_626);
if (x_627 == 0)
{
lean_object* x_628; lean_object* x_629; 
x_628 = lean_ctor_get(x_626, 0);
x_629 = lean_expr_update_proj(x_5, x_628);
lean_ctor_set(x_626, 0, x_629);
return x_624;
}
else
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_630 = lean_ctor_get(x_626, 0);
x_631 = lean_ctor_get(x_626, 1);
lean_inc(x_631);
lean_inc(x_630);
lean_dec(x_626);
x_632 = lean_expr_update_proj(x_5, x_630);
x_633 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_633, 0, x_632);
lean_ctor_set(x_633, 1, x_631);
lean_ctor_set(x_624, 0, x_633);
return x_624;
}
}
else
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; 
x_634 = lean_ctor_get(x_624, 0);
x_635 = lean_ctor_get(x_624, 1);
lean_inc(x_635);
lean_inc(x_634);
lean_dec(x_624);
x_636 = lean_ctor_get(x_634, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_634, 1);
lean_inc(x_637);
if (lean_is_exclusive(x_634)) {
 lean_ctor_release(x_634, 0);
 lean_ctor_release(x_634, 1);
 x_638 = x_634;
} else {
 lean_dec_ref(x_634);
 x_638 = lean_box(0);
}
x_639 = lean_expr_update_proj(x_5, x_636);
if (lean_is_scalar(x_638)) {
 x_640 = lean_alloc_ctor(0, 2, 0);
} else {
 x_640 = x_638;
}
lean_ctor_set(x_640, 0, x_639);
lean_ctor_set(x_640, 1, x_637);
x_641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_641, 0, x_640);
lean_ctor_set(x_641, 1, x_635);
return x_641;
}
}
else
{
uint8_t x_642; 
lean_dec(x_5);
x_642 = !lean_is_exclusive(x_624);
if (x_642 == 0)
{
return x_624;
}
else
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; 
x_643 = lean_ctor_get(x_624, 0);
x_644 = lean_ctor_get(x_624, 1);
lean_inc(x_644);
lean_inc(x_643);
lean_dec(x_624);
x_645 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_645, 0, x_643);
lean_ctor_set(x_645, 1, x_644);
return x_645;
}
}
}
default: 
{
lean_object* x_646; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_646 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_646, 0, x_5);
lean_ctor_set(x_646, 1, x_445);
lean_ctor_set(x_224, 0, x_646);
return x_224;
}
}
}
else
{
lean_object* x_647; lean_object* x_648; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_647 = l_Lean_mkBVar(x_6);
x_648 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_648, 0, x_647);
lean_ctor_set(x_648, 1, x_445);
lean_ctor_set(x_224, 0, x_648);
return x_224;
}
}
else
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; uint8_t x_652; 
x_649 = lean_ctor_get(x_224, 1);
lean_inc(x_649);
lean_dec(x_224);
x_650 = lean_unsigned_to_nat(1u);
x_651 = lean_nat_add(x_7, x_650);
x_652 = l_Lean_Occurrences_contains(x_1, x_7);
lean_dec(x_7);
if (x_652 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_653 = lean_ctor_get(x_5, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_5, 1);
lean_inc(x_654);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_655 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_653, x_6, x_651, x_8, x_649);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; 
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_655, 1);
lean_inc(x_657);
lean_dec(x_655);
x_658 = lean_ctor_get(x_656, 0);
lean_inc(x_658);
x_659 = lean_ctor_get(x_656, 1);
lean_inc(x_659);
lean_dec(x_656);
x_660 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_654, x_6, x_659, x_8, x_657);
if (lean_obj_tag(x_660) == 0)
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_661 = lean_ctor_get(x_660, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_660, 1);
lean_inc(x_662);
if (lean_is_exclusive(x_660)) {
 lean_ctor_release(x_660, 0);
 lean_ctor_release(x_660, 1);
 x_663 = x_660;
} else {
 lean_dec_ref(x_660);
 x_663 = lean_box(0);
}
x_664 = lean_ctor_get(x_661, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_661, 1);
lean_inc(x_665);
if (lean_is_exclusive(x_661)) {
 lean_ctor_release(x_661, 0);
 lean_ctor_release(x_661, 1);
 x_666 = x_661;
} else {
 lean_dec_ref(x_661);
 x_666 = lean_box(0);
}
x_667 = lean_expr_update_app(x_5, x_658, x_664);
if (lean_is_scalar(x_666)) {
 x_668 = lean_alloc_ctor(0, 2, 0);
} else {
 x_668 = x_666;
}
lean_ctor_set(x_668, 0, x_667);
lean_ctor_set(x_668, 1, x_665);
if (lean_is_scalar(x_663)) {
 x_669 = lean_alloc_ctor(0, 2, 0);
} else {
 x_669 = x_663;
}
lean_ctor_set(x_669, 0, x_668);
lean_ctor_set(x_669, 1, x_662);
return x_669;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; 
lean_dec(x_658);
lean_dec(x_5);
x_670 = lean_ctor_get(x_660, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_660, 1);
lean_inc(x_671);
if (lean_is_exclusive(x_660)) {
 lean_ctor_release(x_660, 0);
 lean_ctor_release(x_660, 1);
 x_672 = x_660;
} else {
 lean_dec_ref(x_660);
 x_672 = lean_box(0);
}
if (lean_is_scalar(x_672)) {
 x_673 = lean_alloc_ctor(1, 2, 0);
} else {
 x_673 = x_672;
}
lean_ctor_set(x_673, 0, x_670);
lean_ctor_set(x_673, 1, x_671);
return x_673;
}
}
else
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; 
lean_dec(x_654);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_674 = lean_ctor_get(x_655, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_655, 1);
lean_inc(x_675);
if (lean_is_exclusive(x_655)) {
 lean_ctor_release(x_655, 0);
 lean_ctor_release(x_655, 1);
 x_676 = x_655;
} else {
 lean_dec_ref(x_655);
 x_676 = lean_box(0);
}
if (lean_is_scalar(x_676)) {
 x_677 = lean_alloc_ctor(1, 2, 0);
} else {
 x_677 = x_676;
}
lean_ctor_set(x_677, 0, x_674);
lean_ctor_set(x_677, 1, x_675);
return x_677;
}
}
case 6:
{
lean_object* x_678; lean_object* x_679; uint64_t x_680; lean_object* x_681; 
x_678 = lean_ctor_get(x_5, 1);
lean_inc(x_678);
x_679 = lean_ctor_get(x_5, 2);
lean_inc(x_679);
x_680 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_681 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_678, x_6, x_651, x_8, x_649);
if (lean_obj_tag(x_681) == 0)
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; 
x_682 = lean_ctor_get(x_681, 0);
lean_inc(x_682);
x_683 = lean_ctor_get(x_681, 1);
lean_inc(x_683);
lean_dec(x_681);
x_684 = lean_ctor_get(x_682, 0);
lean_inc(x_684);
x_685 = lean_ctor_get(x_682, 1);
lean_inc(x_685);
lean_dec(x_682);
x_686 = lean_nat_add(x_6, x_650);
lean_dec(x_6);
x_687 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_679, x_686, x_685, x_8, x_683);
if (lean_obj_tag(x_687) == 0)
{
lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; uint8_t x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_688 = lean_ctor_get(x_687, 0);
lean_inc(x_688);
x_689 = lean_ctor_get(x_687, 1);
lean_inc(x_689);
if (lean_is_exclusive(x_687)) {
 lean_ctor_release(x_687, 0);
 lean_ctor_release(x_687, 1);
 x_690 = x_687;
} else {
 lean_dec_ref(x_687);
 x_690 = lean_box(0);
}
x_691 = lean_ctor_get(x_688, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_688, 1);
lean_inc(x_692);
if (lean_is_exclusive(x_688)) {
 lean_ctor_release(x_688, 0);
 lean_ctor_release(x_688, 1);
 x_693 = x_688;
} else {
 lean_dec_ref(x_688);
 x_693 = lean_box(0);
}
x_694 = (uint8_t)((x_680 << 24) >> 61);
x_695 = lean_expr_update_lambda(x_5, x_694, x_684, x_691);
if (lean_is_scalar(x_693)) {
 x_696 = lean_alloc_ctor(0, 2, 0);
} else {
 x_696 = x_693;
}
lean_ctor_set(x_696, 0, x_695);
lean_ctor_set(x_696, 1, x_692);
if (lean_is_scalar(x_690)) {
 x_697 = lean_alloc_ctor(0, 2, 0);
} else {
 x_697 = x_690;
}
lean_ctor_set(x_697, 0, x_696);
lean_ctor_set(x_697, 1, x_689);
return x_697;
}
else
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; 
lean_dec(x_684);
lean_dec(x_5);
x_698 = lean_ctor_get(x_687, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_687, 1);
lean_inc(x_699);
if (lean_is_exclusive(x_687)) {
 lean_ctor_release(x_687, 0);
 lean_ctor_release(x_687, 1);
 x_700 = x_687;
} else {
 lean_dec_ref(x_687);
 x_700 = lean_box(0);
}
if (lean_is_scalar(x_700)) {
 x_701 = lean_alloc_ctor(1, 2, 0);
} else {
 x_701 = x_700;
}
lean_ctor_set(x_701, 0, x_698);
lean_ctor_set(x_701, 1, x_699);
return x_701;
}
}
else
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; 
lean_dec(x_679);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_702 = lean_ctor_get(x_681, 0);
lean_inc(x_702);
x_703 = lean_ctor_get(x_681, 1);
lean_inc(x_703);
if (lean_is_exclusive(x_681)) {
 lean_ctor_release(x_681, 0);
 lean_ctor_release(x_681, 1);
 x_704 = x_681;
} else {
 lean_dec_ref(x_681);
 x_704 = lean_box(0);
}
if (lean_is_scalar(x_704)) {
 x_705 = lean_alloc_ctor(1, 2, 0);
} else {
 x_705 = x_704;
}
lean_ctor_set(x_705, 0, x_702);
lean_ctor_set(x_705, 1, x_703);
return x_705;
}
}
case 7:
{
lean_object* x_706; lean_object* x_707; uint64_t x_708; lean_object* x_709; 
x_706 = lean_ctor_get(x_5, 1);
lean_inc(x_706);
x_707 = lean_ctor_get(x_5, 2);
lean_inc(x_707);
x_708 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_709 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_706, x_6, x_651, x_8, x_649);
if (lean_obj_tag(x_709) == 0)
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_710 = lean_ctor_get(x_709, 0);
lean_inc(x_710);
x_711 = lean_ctor_get(x_709, 1);
lean_inc(x_711);
lean_dec(x_709);
x_712 = lean_ctor_get(x_710, 0);
lean_inc(x_712);
x_713 = lean_ctor_get(x_710, 1);
lean_inc(x_713);
lean_dec(x_710);
x_714 = lean_nat_add(x_6, x_650);
lean_dec(x_6);
x_715 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_707, x_714, x_713, x_8, x_711);
if (lean_obj_tag(x_715) == 0)
{
lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; uint8_t x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; 
x_716 = lean_ctor_get(x_715, 0);
lean_inc(x_716);
x_717 = lean_ctor_get(x_715, 1);
lean_inc(x_717);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 lean_ctor_release(x_715, 1);
 x_718 = x_715;
} else {
 lean_dec_ref(x_715);
 x_718 = lean_box(0);
}
x_719 = lean_ctor_get(x_716, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_716, 1);
lean_inc(x_720);
if (lean_is_exclusive(x_716)) {
 lean_ctor_release(x_716, 0);
 lean_ctor_release(x_716, 1);
 x_721 = x_716;
} else {
 lean_dec_ref(x_716);
 x_721 = lean_box(0);
}
x_722 = (uint8_t)((x_708 << 24) >> 61);
x_723 = lean_expr_update_forall(x_5, x_722, x_712, x_719);
if (lean_is_scalar(x_721)) {
 x_724 = lean_alloc_ctor(0, 2, 0);
} else {
 x_724 = x_721;
}
lean_ctor_set(x_724, 0, x_723);
lean_ctor_set(x_724, 1, x_720);
if (lean_is_scalar(x_718)) {
 x_725 = lean_alloc_ctor(0, 2, 0);
} else {
 x_725 = x_718;
}
lean_ctor_set(x_725, 0, x_724);
lean_ctor_set(x_725, 1, x_717);
return x_725;
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; 
lean_dec(x_712);
lean_dec(x_5);
x_726 = lean_ctor_get(x_715, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_715, 1);
lean_inc(x_727);
if (lean_is_exclusive(x_715)) {
 lean_ctor_release(x_715, 0);
 lean_ctor_release(x_715, 1);
 x_728 = x_715;
} else {
 lean_dec_ref(x_715);
 x_728 = lean_box(0);
}
if (lean_is_scalar(x_728)) {
 x_729 = lean_alloc_ctor(1, 2, 0);
} else {
 x_729 = x_728;
}
lean_ctor_set(x_729, 0, x_726);
lean_ctor_set(x_729, 1, x_727);
return x_729;
}
}
else
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; 
lean_dec(x_707);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_730 = lean_ctor_get(x_709, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_709, 1);
lean_inc(x_731);
if (lean_is_exclusive(x_709)) {
 lean_ctor_release(x_709, 0);
 lean_ctor_release(x_709, 1);
 x_732 = x_709;
} else {
 lean_dec_ref(x_709);
 x_732 = lean_box(0);
}
if (lean_is_scalar(x_732)) {
 x_733 = lean_alloc_ctor(1, 2, 0);
} else {
 x_733 = x_732;
}
lean_ctor_set(x_733, 0, x_730);
lean_ctor_set(x_733, 1, x_731);
return x_733;
}
}
case 8:
{
lean_object* x_734; lean_object* x_735; lean_object* x_736; lean_object* x_737; 
x_734 = lean_ctor_get(x_5, 1);
lean_inc(x_734);
x_735 = lean_ctor_get(x_5, 2);
lean_inc(x_735);
x_736 = lean_ctor_get(x_5, 3);
lean_inc(x_736);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_737 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_734, x_6, x_651, x_8, x_649);
if (lean_obj_tag(x_737) == 0)
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; 
x_738 = lean_ctor_get(x_737, 0);
lean_inc(x_738);
x_739 = lean_ctor_get(x_737, 1);
lean_inc(x_739);
lean_dec(x_737);
x_740 = lean_ctor_get(x_738, 0);
lean_inc(x_740);
x_741 = lean_ctor_get(x_738, 1);
lean_inc(x_741);
lean_dec(x_738);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_742 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_735, x_6, x_741, x_8, x_739);
if (lean_obj_tag(x_742) == 0)
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; 
x_743 = lean_ctor_get(x_742, 0);
lean_inc(x_743);
x_744 = lean_ctor_get(x_742, 1);
lean_inc(x_744);
lean_dec(x_742);
x_745 = lean_ctor_get(x_743, 0);
lean_inc(x_745);
x_746 = lean_ctor_get(x_743, 1);
lean_inc(x_746);
lean_dec(x_743);
x_747 = lean_nat_add(x_6, x_650);
lean_dec(x_6);
x_748 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_736, x_747, x_746, x_8, x_744);
if (lean_obj_tag(x_748) == 0)
{
lean_object* x_749; lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; 
x_749 = lean_ctor_get(x_748, 0);
lean_inc(x_749);
x_750 = lean_ctor_get(x_748, 1);
lean_inc(x_750);
if (lean_is_exclusive(x_748)) {
 lean_ctor_release(x_748, 0);
 lean_ctor_release(x_748, 1);
 x_751 = x_748;
} else {
 lean_dec_ref(x_748);
 x_751 = lean_box(0);
}
x_752 = lean_ctor_get(x_749, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_749, 1);
lean_inc(x_753);
if (lean_is_exclusive(x_749)) {
 lean_ctor_release(x_749, 0);
 lean_ctor_release(x_749, 1);
 x_754 = x_749;
} else {
 lean_dec_ref(x_749);
 x_754 = lean_box(0);
}
x_755 = lean_expr_update_let(x_5, x_740, x_745, x_752);
if (lean_is_scalar(x_754)) {
 x_756 = lean_alloc_ctor(0, 2, 0);
} else {
 x_756 = x_754;
}
lean_ctor_set(x_756, 0, x_755);
lean_ctor_set(x_756, 1, x_753);
if (lean_is_scalar(x_751)) {
 x_757 = lean_alloc_ctor(0, 2, 0);
} else {
 x_757 = x_751;
}
lean_ctor_set(x_757, 0, x_756);
lean_ctor_set(x_757, 1, x_750);
return x_757;
}
else
{
lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; 
lean_dec(x_745);
lean_dec(x_740);
lean_dec(x_5);
x_758 = lean_ctor_get(x_748, 0);
lean_inc(x_758);
x_759 = lean_ctor_get(x_748, 1);
lean_inc(x_759);
if (lean_is_exclusive(x_748)) {
 lean_ctor_release(x_748, 0);
 lean_ctor_release(x_748, 1);
 x_760 = x_748;
} else {
 lean_dec_ref(x_748);
 x_760 = lean_box(0);
}
if (lean_is_scalar(x_760)) {
 x_761 = lean_alloc_ctor(1, 2, 0);
} else {
 x_761 = x_760;
}
lean_ctor_set(x_761, 0, x_758);
lean_ctor_set(x_761, 1, x_759);
return x_761;
}
}
else
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; 
lean_dec(x_740);
lean_dec(x_736);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_762 = lean_ctor_get(x_742, 0);
lean_inc(x_762);
x_763 = lean_ctor_get(x_742, 1);
lean_inc(x_763);
if (lean_is_exclusive(x_742)) {
 lean_ctor_release(x_742, 0);
 lean_ctor_release(x_742, 1);
 x_764 = x_742;
} else {
 lean_dec_ref(x_742);
 x_764 = lean_box(0);
}
if (lean_is_scalar(x_764)) {
 x_765 = lean_alloc_ctor(1, 2, 0);
} else {
 x_765 = x_764;
}
lean_ctor_set(x_765, 0, x_762);
lean_ctor_set(x_765, 1, x_763);
return x_765;
}
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_dec(x_736);
lean_dec(x_735);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_766 = lean_ctor_get(x_737, 0);
lean_inc(x_766);
x_767 = lean_ctor_get(x_737, 1);
lean_inc(x_767);
if (lean_is_exclusive(x_737)) {
 lean_ctor_release(x_737, 0);
 lean_ctor_release(x_737, 1);
 x_768 = x_737;
} else {
 lean_dec_ref(x_737);
 x_768 = lean_box(0);
}
if (lean_is_scalar(x_768)) {
 x_769 = lean_alloc_ctor(1, 2, 0);
} else {
 x_769 = x_768;
}
lean_ctor_set(x_769, 0, x_766);
lean_ctor_set(x_769, 1, x_767);
return x_769;
}
}
case 10:
{
lean_object* x_770; lean_object* x_771; 
x_770 = lean_ctor_get(x_5, 1);
lean_inc(x_770);
x_771 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_770, x_6, x_651, x_8, x_649);
if (lean_obj_tag(x_771) == 0)
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; 
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_771, 1);
lean_inc(x_773);
if (lean_is_exclusive(x_771)) {
 lean_ctor_release(x_771, 0);
 lean_ctor_release(x_771, 1);
 x_774 = x_771;
} else {
 lean_dec_ref(x_771);
 x_774 = lean_box(0);
}
x_775 = lean_ctor_get(x_772, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_772, 1);
lean_inc(x_776);
if (lean_is_exclusive(x_772)) {
 lean_ctor_release(x_772, 0);
 lean_ctor_release(x_772, 1);
 x_777 = x_772;
} else {
 lean_dec_ref(x_772);
 x_777 = lean_box(0);
}
x_778 = lean_expr_update_mdata(x_5, x_775);
if (lean_is_scalar(x_777)) {
 x_779 = lean_alloc_ctor(0, 2, 0);
} else {
 x_779 = x_777;
}
lean_ctor_set(x_779, 0, x_778);
lean_ctor_set(x_779, 1, x_776);
if (lean_is_scalar(x_774)) {
 x_780 = lean_alloc_ctor(0, 2, 0);
} else {
 x_780 = x_774;
}
lean_ctor_set(x_780, 0, x_779);
lean_ctor_set(x_780, 1, x_773);
return x_780;
}
else
{
lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; 
lean_dec(x_5);
x_781 = lean_ctor_get(x_771, 0);
lean_inc(x_781);
x_782 = lean_ctor_get(x_771, 1);
lean_inc(x_782);
if (lean_is_exclusive(x_771)) {
 lean_ctor_release(x_771, 0);
 lean_ctor_release(x_771, 1);
 x_783 = x_771;
} else {
 lean_dec_ref(x_771);
 x_783 = lean_box(0);
}
if (lean_is_scalar(x_783)) {
 x_784 = lean_alloc_ctor(1, 2, 0);
} else {
 x_784 = x_783;
}
lean_ctor_set(x_784, 0, x_781);
lean_ctor_set(x_784, 1, x_782);
return x_784;
}
}
case 11:
{
lean_object* x_785; lean_object* x_786; 
x_785 = lean_ctor_get(x_5, 2);
lean_inc(x_785);
x_786 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_785, x_6, x_651, x_8, x_649);
if (lean_obj_tag(x_786) == 0)
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
x_787 = lean_ctor_get(x_786, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_786, 1);
lean_inc(x_788);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 x_789 = x_786;
} else {
 lean_dec_ref(x_786);
 x_789 = lean_box(0);
}
x_790 = lean_ctor_get(x_787, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_787, 1);
lean_inc(x_791);
if (lean_is_exclusive(x_787)) {
 lean_ctor_release(x_787, 0);
 lean_ctor_release(x_787, 1);
 x_792 = x_787;
} else {
 lean_dec_ref(x_787);
 x_792 = lean_box(0);
}
x_793 = lean_expr_update_proj(x_5, x_790);
if (lean_is_scalar(x_792)) {
 x_794 = lean_alloc_ctor(0, 2, 0);
} else {
 x_794 = x_792;
}
lean_ctor_set(x_794, 0, x_793);
lean_ctor_set(x_794, 1, x_791);
if (lean_is_scalar(x_789)) {
 x_795 = lean_alloc_ctor(0, 2, 0);
} else {
 x_795 = x_789;
}
lean_ctor_set(x_795, 0, x_794);
lean_ctor_set(x_795, 1, x_788);
return x_795;
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; 
lean_dec(x_5);
x_796 = lean_ctor_get(x_786, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_786, 1);
lean_inc(x_797);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 x_798 = x_786;
} else {
 lean_dec_ref(x_786);
 x_798 = lean_box(0);
}
if (lean_is_scalar(x_798)) {
 x_799 = lean_alloc_ctor(1, 2, 0);
} else {
 x_799 = x_798;
}
lean_ctor_set(x_799, 0, x_796);
lean_ctor_set(x_799, 1, x_797);
return x_799;
}
}
default: 
{
lean_object* x_800; lean_object* x_801; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_800 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_800, 0, x_5);
lean_ctor_set(x_800, 1, x_651);
x_801 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_801, 0, x_800);
lean_ctor_set(x_801, 1, x_649);
return x_801;
}
}
}
else
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_802 = l_Lean_mkBVar(x_6);
x_803 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_803, 0, x_802);
lean_ctor_set(x_803, 1, x_651);
x_804 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_804, 0, x_803);
lean_ctor_set(x_804, 1, x_649);
return x_804;
}
}
}
}
else
{
uint8_t x_805; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_805 = !lean_is_exclusive(x_224);
if (x_805 == 0)
{
return x_224;
}
else
{
lean_object* x_806; lean_object* x_807; lean_object* x_808; 
x_806 = lean_ctor_get(x_224, 0);
x_807 = lean_ctor_get(x_224, 1);
lean_inc(x_807);
lean_inc(x_806);
lean_dec(x_224);
x_808 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_808, 0, x_806);
lean_ctor_set(x_808, 1, x_807);
return x_808;
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
lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_809 = lean_ctor_get(x_5, 0);
lean_inc(x_809);
x_810 = lean_ctor_get(x_5, 1);
lean_inc(x_810);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_811 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_809, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
x_813 = lean_ctor_get(x_811, 1);
lean_inc(x_813);
lean_dec(x_811);
x_814 = lean_ctor_get(x_812, 0);
lean_inc(x_814);
x_815 = lean_ctor_get(x_812, 1);
lean_inc(x_815);
lean_dec(x_812);
x_816 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_810, x_6, x_815, x_8, x_813);
if (lean_obj_tag(x_816) == 0)
{
uint8_t x_817; 
x_817 = !lean_is_exclusive(x_816);
if (x_817 == 0)
{
lean_object* x_818; uint8_t x_819; 
x_818 = lean_ctor_get(x_816, 0);
x_819 = !lean_is_exclusive(x_818);
if (x_819 == 0)
{
lean_object* x_820; lean_object* x_821; 
x_820 = lean_ctor_get(x_818, 0);
x_821 = lean_expr_update_app(x_5, x_814, x_820);
lean_ctor_set(x_818, 0, x_821);
return x_816;
}
else
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_822 = lean_ctor_get(x_818, 0);
x_823 = lean_ctor_get(x_818, 1);
lean_inc(x_823);
lean_inc(x_822);
lean_dec(x_818);
x_824 = lean_expr_update_app(x_5, x_814, x_822);
x_825 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_825, 0, x_824);
lean_ctor_set(x_825, 1, x_823);
lean_ctor_set(x_816, 0, x_825);
return x_816;
}
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; 
x_826 = lean_ctor_get(x_816, 0);
x_827 = lean_ctor_get(x_816, 1);
lean_inc(x_827);
lean_inc(x_826);
lean_dec(x_816);
x_828 = lean_ctor_get(x_826, 0);
lean_inc(x_828);
x_829 = lean_ctor_get(x_826, 1);
lean_inc(x_829);
if (lean_is_exclusive(x_826)) {
 lean_ctor_release(x_826, 0);
 lean_ctor_release(x_826, 1);
 x_830 = x_826;
} else {
 lean_dec_ref(x_826);
 x_830 = lean_box(0);
}
x_831 = lean_expr_update_app(x_5, x_814, x_828);
if (lean_is_scalar(x_830)) {
 x_832 = lean_alloc_ctor(0, 2, 0);
} else {
 x_832 = x_830;
}
lean_ctor_set(x_832, 0, x_831);
lean_ctor_set(x_832, 1, x_829);
x_833 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_833, 0, x_832);
lean_ctor_set(x_833, 1, x_827);
return x_833;
}
}
else
{
uint8_t x_834; 
lean_dec(x_814);
lean_dec(x_5);
x_834 = !lean_is_exclusive(x_816);
if (x_834 == 0)
{
return x_816;
}
else
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; 
x_835 = lean_ctor_get(x_816, 0);
x_836 = lean_ctor_get(x_816, 1);
lean_inc(x_836);
lean_inc(x_835);
lean_dec(x_816);
x_837 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_837, 0, x_835);
lean_ctor_set(x_837, 1, x_836);
return x_837;
}
}
}
else
{
uint8_t x_838; 
lean_dec(x_810);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_838 = !lean_is_exclusive(x_811);
if (x_838 == 0)
{
return x_811;
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; 
x_839 = lean_ctor_get(x_811, 0);
x_840 = lean_ctor_get(x_811, 1);
lean_inc(x_840);
lean_inc(x_839);
lean_dec(x_811);
x_841 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_841, 0, x_839);
lean_ctor_set(x_841, 1, x_840);
return x_841;
}
}
}
case 6:
{
lean_object* x_842; lean_object* x_843; uint64_t x_844; lean_object* x_845; 
x_842 = lean_ctor_get(x_5, 1);
lean_inc(x_842);
x_843 = lean_ctor_get(x_5, 2);
lean_inc(x_843);
x_844 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_845 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_842, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_845) == 0)
{
lean_object* x_846; lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; 
x_846 = lean_ctor_get(x_845, 0);
lean_inc(x_846);
x_847 = lean_ctor_get(x_845, 1);
lean_inc(x_847);
lean_dec(x_845);
x_848 = lean_ctor_get(x_846, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_846, 1);
lean_inc(x_849);
lean_dec(x_846);
x_850 = lean_unsigned_to_nat(1u);
x_851 = lean_nat_add(x_6, x_850);
lean_dec(x_6);
x_852 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_843, x_851, x_849, x_8, x_847);
if (lean_obj_tag(x_852) == 0)
{
uint8_t x_853; 
x_853 = !lean_is_exclusive(x_852);
if (x_853 == 0)
{
lean_object* x_854; uint8_t x_855; 
x_854 = lean_ctor_get(x_852, 0);
x_855 = !lean_is_exclusive(x_854);
if (x_855 == 0)
{
lean_object* x_856; uint8_t x_857; lean_object* x_858; 
x_856 = lean_ctor_get(x_854, 0);
x_857 = (uint8_t)((x_844 << 24) >> 61);
x_858 = lean_expr_update_lambda(x_5, x_857, x_848, x_856);
lean_ctor_set(x_854, 0, x_858);
return x_852;
}
else
{
lean_object* x_859; lean_object* x_860; uint8_t x_861; lean_object* x_862; lean_object* x_863; 
x_859 = lean_ctor_get(x_854, 0);
x_860 = lean_ctor_get(x_854, 1);
lean_inc(x_860);
lean_inc(x_859);
lean_dec(x_854);
x_861 = (uint8_t)((x_844 << 24) >> 61);
x_862 = lean_expr_update_lambda(x_5, x_861, x_848, x_859);
x_863 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_863, 0, x_862);
lean_ctor_set(x_863, 1, x_860);
lean_ctor_set(x_852, 0, x_863);
return x_852;
}
}
else
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; uint8_t x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_864 = lean_ctor_get(x_852, 0);
x_865 = lean_ctor_get(x_852, 1);
lean_inc(x_865);
lean_inc(x_864);
lean_dec(x_852);
x_866 = lean_ctor_get(x_864, 0);
lean_inc(x_866);
x_867 = lean_ctor_get(x_864, 1);
lean_inc(x_867);
if (lean_is_exclusive(x_864)) {
 lean_ctor_release(x_864, 0);
 lean_ctor_release(x_864, 1);
 x_868 = x_864;
} else {
 lean_dec_ref(x_864);
 x_868 = lean_box(0);
}
x_869 = (uint8_t)((x_844 << 24) >> 61);
x_870 = lean_expr_update_lambda(x_5, x_869, x_848, x_866);
if (lean_is_scalar(x_868)) {
 x_871 = lean_alloc_ctor(0, 2, 0);
} else {
 x_871 = x_868;
}
lean_ctor_set(x_871, 0, x_870);
lean_ctor_set(x_871, 1, x_867);
x_872 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_872, 0, x_871);
lean_ctor_set(x_872, 1, x_865);
return x_872;
}
}
else
{
uint8_t x_873; 
lean_dec(x_848);
lean_dec(x_5);
x_873 = !lean_is_exclusive(x_852);
if (x_873 == 0)
{
return x_852;
}
else
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; 
x_874 = lean_ctor_get(x_852, 0);
x_875 = lean_ctor_get(x_852, 1);
lean_inc(x_875);
lean_inc(x_874);
lean_dec(x_852);
x_876 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_876, 0, x_874);
lean_ctor_set(x_876, 1, x_875);
return x_876;
}
}
}
else
{
uint8_t x_877; 
lean_dec(x_843);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_877 = !lean_is_exclusive(x_845);
if (x_877 == 0)
{
return x_845;
}
else
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; 
x_878 = lean_ctor_get(x_845, 0);
x_879 = lean_ctor_get(x_845, 1);
lean_inc(x_879);
lean_inc(x_878);
lean_dec(x_845);
x_880 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_880, 0, x_878);
lean_ctor_set(x_880, 1, x_879);
return x_880;
}
}
}
case 7:
{
lean_object* x_881; lean_object* x_882; uint64_t x_883; lean_object* x_884; 
x_881 = lean_ctor_get(x_5, 1);
lean_inc(x_881);
x_882 = lean_ctor_get(x_5, 2);
lean_inc(x_882);
x_883 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_884 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_881, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_884) == 0)
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; 
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_884, 1);
lean_inc(x_886);
lean_dec(x_884);
x_887 = lean_ctor_get(x_885, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_885, 1);
lean_inc(x_888);
lean_dec(x_885);
x_889 = lean_unsigned_to_nat(1u);
x_890 = lean_nat_add(x_6, x_889);
lean_dec(x_6);
x_891 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_882, x_890, x_888, x_8, x_886);
if (lean_obj_tag(x_891) == 0)
{
uint8_t x_892; 
x_892 = !lean_is_exclusive(x_891);
if (x_892 == 0)
{
lean_object* x_893; uint8_t x_894; 
x_893 = lean_ctor_get(x_891, 0);
x_894 = !lean_is_exclusive(x_893);
if (x_894 == 0)
{
lean_object* x_895; uint8_t x_896; lean_object* x_897; 
x_895 = lean_ctor_get(x_893, 0);
x_896 = (uint8_t)((x_883 << 24) >> 61);
x_897 = lean_expr_update_forall(x_5, x_896, x_887, x_895);
lean_ctor_set(x_893, 0, x_897);
return x_891;
}
else
{
lean_object* x_898; lean_object* x_899; uint8_t x_900; lean_object* x_901; lean_object* x_902; 
x_898 = lean_ctor_get(x_893, 0);
x_899 = lean_ctor_get(x_893, 1);
lean_inc(x_899);
lean_inc(x_898);
lean_dec(x_893);
x_900 = (uint8_t)((x_883 << 24) >> 61);
x_901 = lean_expr_update_forall(x_5, x_900, x_887, x_898);
x_902 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_902, 0, x_901);
lean_ctor_set(x_902, 1, x_899);
lean_ctor_set(x_891, 0, x_902);
return x_891;
}
}
else
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; uint8_t x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; 
x_903 = lean_ctor_get(x_891, 0);
x_904 = lean_ctor_get(x_891, 1);
lean_inc(x_904);
lean_inc(x_903);
lean_dec(x_891);
x_905 = lean_ctor_get(x_903, 0);
lean_inc(x_905);
x_906 = lean_ctor_get(x_903, 1);
lean_inc(x_906);
if (lean_is_exclusive(x_903)) {
 lean_ctor_release(x_903, 0);
 lean_ctor_release(x_903, 1);
 x_907 = x_903;
} else {
 lean_dec_ref(x_903);
 x_907 = lean_box(0);
}
x_908 = (uint8_t)((x_883 << 24) >> 61);
x_909 = lean_expr_update_forall(x_5, x_908, x_887, x_905);
if (lean_is_scalar(x_907)) {
 x_910 = lean_alloc_ctor(0, 2, 0);
} else {
 x_910 = x_907;
}
lean_ctor_set(x_910, 0, x_909);
lean_ctor_set(x_910, 1, x_906);
x_911 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_911, 0, x_910);
lean_ctor_set(x_911, 1, x_904);
return x_911;
}
}
else
{
uint8_t x_912; 
lean_dec(x_887);
lean_dec(x_5);
x_912 = !lean_is_exclusive(x_891);
if (x_912 == 0)
{
return x_891;
}
else
{
lean_object* x_913; lean_object* x_914; lean_object* x_915; 
x_913 = lean_ctor_get(x_891, 0);
x_914 = lean_ctor_get(x_891, 1);
lean_inc(x_914);
lean_inc(x_913);
lean_dec(x_891);
x_915 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_915, 0, x_913);
lean_ctor_set(x_915, 1, x_914);
return x_915;
}
}
}
else
{
uint8_t x_916; 
lean_dec(x_882);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_916 = !lean_is_exclusive(x_884);
if (x_916 == 0)
{
return x_884;
}
else
{
lean_object* x_917; lean_object* x_918; lean_object* x_919; 
x_917 = lean_ctor_get(x_884, 0);
x_918 = lean_ctor_get(x_884, 1);
lean_inc(x_918);
lean_inc(x_917);
lean_dec(x_884);
x_919 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_919, 0, x_917);
lean_ctor_set(x_919, 1, x_918);
return x_919;
}
}
}
case 8:
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; 
x_920 = lean_ctor_get(x_5, 1);
lean_inc(x_920);
x_921 = lean_ctor_get(x_5, 2);
lean_inc(x_921);
x_922 = lean_ctor_get(x_5, 3);
lean_inc(x_922);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_923 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_920, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_923) == 0)
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; 
x_924 = lean_ctor_get(x_923, 0);
lean_inc(x_924);
x_925 = lean_ctor_get(x_923, 1);
lean_inc(x_925);
lean_dec(x_923);
x_926 = lean_ctor_get(x_924, 0);
lean_inc(x_926);
x_927 = lean_ctor_get(x_924, 1);
lean_inc(x_927);
lean_dec(x_924);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_928 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_921, x_6, x_927, x_8, x_925);
if (lean_obj_tag(x_928) == 0)
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; 
x_929 = lean_ctor_get(x_928, 0);
lean_inc(x_929);
x_930 = lean_ctor_get(x_928, 1);
lean_inc(x_930);
lean_dec(x_928);
x_931 = lean_ctor_get(x_929, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_929, 1);
lean_inc(x_932);
lean_dec(x_929);
x_933 = lean_unsigned_to_nat(1u);
x_934 = lean_nat_add(x_6, x_933);
lean_dec(x_6);
x_935 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_922, x_934, x_932, x_8, x_930);
if (lean_obj_tag(x_935) == 0)
{
uint8_t x_936; 
x_936 = !lean_is_exclusive(x_935);
if (x_936 == 0)
{
lean_object* x_937; uint8_t x_938; 
x_937 = lean_ctor_get(x_935, 0);
x_938 = !lean_is_exclusive(x_937);
if (x_938 == 0)
{
lean_object* x_939; lean_object* x_940; 
x_939 = lean_ctor_get(x_937, 0);
x_940 = lean_expr_update_let(x_5, x_926, x_931, x_939);
lean_ctor_set(x_937, 0, x_940);
return x_935;
}
else
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; 
x_941 = lean_ctor_get(x_937, 0);
x_942 = lean_ctor_get(x_937, 1);
lean_inc(x_942);
lean_inc(x_941);
lean_dec(x_937);
x_943 = lean_expr_update_let(x_5, x_926, x_931, x_941);
x_944 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_944, 0, x_943);
lean_ctor_set(x_944, 1, x_942);
lean_ctor_set(x_935, 0, x_944);
return x_935;
}
}
else
{
lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; 
x_945 = lean_ctor_get(x_935, 0);
x_946 = lean_ctor_get(x_935, 1);
lean_inc(x_946);
lean_inc(x_945);
lean_dec(x_935);
x_947 = lean_ctor_get(x_945, 0);
lean_inc(x_947);
x_948 = lean_ctor_get(x_945, 1);
lean_inc(x_948);
if (lean_is_exclusive(x_945)) {
 lean_ctor_release(x_945, 0);
 lean_ctor_release(x_945, 1);
 x_949 = x_945;
} else {
 lean_dec_ref(x_945);
 x_949 = lean_box(0);
}
x_950 = lean_expr_update_let(x_5, x_926, x_931, x_947);
if (lean_is_scalar(x_949)) {
 x_951 = lean_alloc_ctor(0, 2, 0);
} else {
 x_951 = x_949;
}
lean_ctor_set(x_951, 0, x_950);
lean_ctor_set(x_951, 1, x_948);
x_952 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_952, 0, x_951);
lean_ctor_set(x_952, 1, x_946);
return x_952;
}
}
else
{
uint8_t x_953; 
lean_dec(x_931);
lean_dec(x_926);
lean_dec(x_5);
x_953 = !lean_is_exclusive(x_935);
if (x_953 == 0)
{
return x_935;
}
else
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; 
x_954 = lean_ctor_get(x_935, 0);
x_955 = lean_ctor_get(x_935, 1);
lean_inc(x_955);
lean_inc(x_954);
lean_dec(x_935);
x_956 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_956, 0, x_954);
lean_ctor_set(x_956, 1, x_955);
return x_956;
}
}
}
else
{
uint8_t x_957; 
lean_dec(x_926);
lean_dec(x_922);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_957 = !lean_is_exclusive(x_928);
if (x_957 == 0)
{
return x_928;
}
else
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; 
x_958 = lean_ctor_get(x_928, 0);
x_959 = lean_ctor_get(x_928, 1);
lean_inc(x_959);
lean_inc(x_958);
lean_dec(x_928);
x_960 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_960, 0, x_958);
lean_ctor_set(x_960, 1, x_959);
return x_960;
}
}
}
else
{
uint8_t x_961; 
lean_dec(x_922);
lean_dec(x_921);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_961 = !lean_is_exclusive(x_923);
if (x_961 == 0)
{
return x_923;
}
else
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; 
x_962 = lean_ctor_get(x_923, 0);
x_963 = lean_ctor_get(x_923, 1);
lean_inc(x_963);
lean_inc(x_962);
lean_dec(x_923);
x_964 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_964, 0, x_962);
lean_ctor_set(x_964, 1, x_963);
return x_964;
}
}
}
case 10:
{
lean_object* x_965; lean_object* x_966; 
x_965 = lean_ctor_get(x_5, 1);
lean_inc(x_965);
x_966 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_965, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_966) == 0)
{
uint8_t x_967; 
x_967 = !lean_is_exclusive(x_966);
if (x_967 == 0)
{
lean_object* x_968; uint8_t x_969; 
x_968 = lean_ctor_get(x_966, 0);
x_969 = !lean_is_exclusive(x_968);
if (x_969 == 0)
{
lean_object* x_970; lean_object* x_971; 
x_970 = lean_ctor_get(x_968, 0);
x_971 = lean_expr_update_mdata(x_5, x_970);
lean_ctor_set(x_968, 0, x_971);
return x_966;
}
else
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; 
x_972 = lean_ctor_get(x_968, 0);
x_973 = lean_ctor_get(x_968, 1);
lean_inc(x_973);
lean_inc(x_972);
lean_dec(x_968);
x_974 = lean_expr_update_mdata(x_5, x_972);
x_975 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_975, 0, x_974);
lean_ctor_set(x_975, 1, x_973);
lean_ctor_set(x_966, 0, x_975);
return x_966;
}
}
else
{
lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; 
x_976 = lean_ctor_get(x_966, 0);
x_977 = lean_ctor_get(x_966, 1);
lean_inc(x_977);
lean_inc(x_976);
lean_dec(x_966);
x_978 = lean_ctor_get(x_976, 0);
lean_inc(x_978);
x_979 = lean_ctor_get(x_976, 1);
lean_inc(x_979);
if (lean_is_exclusive(x_976)) {
 lean_ctor_release(x_976, 0);
 lean_ctor_release(x_976, 1);
 x_980 = x_976;
} else {
 lean_dec_ref(x_976);
 x_980 = lean_box(0);
}
x_981 = lean_expr_update_mdata(x_5, x_978);
if (lean_is_scalar(x_980)) {
 x_982 = lean_alloc_ctor(0, 2, 0);
} else {
 x_982 = x_980;
}
lean_ctor_set(x_982, 0, x_981);
lean_ctor_set(x_982, 1, x_979);
x_983 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_983, 0, x_982);
lean_ctor_set(x_983, 1, x_977);
return x_983;
}
}
else
{
uint8_t x_984; 
lean_dec(x_5);
x_984 = !lean_is_exclusive(x_966);
if (x_984 == 0)
{
return x_966;
}
else
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; 
x_985 = lean_ctor_get(x_966, 0);
x_986 = lean_ctor_get(x_966, 1);
lean_inc(x_986);
lean_inc(x_985);
lean_dec(x_966);
x_987 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_987, 0, x_985);
lean_ctor_set(x_987, 1, x_986);
return x_987;
}
}
}
case 11:
{
lean_object* x_988; lean_object* x_989; 
x_988 = lean_ctor_get(x_5, 2);
lean_inc(x_988);
x_989 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_988, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_989) == 0)
{
uint8_t x_990; 
x_990 = !lean_is_exclusive(x_989);
if (x_990 == 0)
{
lean_object* x_991; uint8_t x_992; 
x_991 = lean_ctor_get(x_989, 0);
x_992 = !lean_is_exclusive(x_991);
if (x_992 == 0)
{
lean_object* x_993; lean_object* x_994; 
x_993 = lean_ctor_get(x_991, 0);
x_994 = lean_expr_update_proj(x_5, x_993);
lean_ctor_set(x_991, 0, x_994);
return x_989;
}
else
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; 
x_995 = lean_ctor_get(x_991, 0);
x_996 = lean_ctor_get(x_991, 1);
lean_inc(x_996);
lean_inc(x_995);
lean_dec(x_991);
x_997 = lean_expr_update_proj(x_5, x_995);
x_998 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_998, 0, x_997);
lean_ctor_set(x_998, 1, x_996);
lean_ctor_set(x_989, 0, x_998);
return x_989;
}
}
else
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
x_999 = lean_ctor_get(x_989, 0);
x_1000 = lean_ctor_get(x_989, 1);
lean_inc(x_1000);
lean_inc(x_999);
lean_dec(x_989);
x_1001 = lean_ctor_get(x_999, 0);
lean_inc(x_1001);
x_1002 = lean_ctor_get(x_999, 1);
lean_inc(x_1002);
if (lean_is_exclusive(x_999)) {
 lean_ctor_release(x_999, 0);
 lean_ctor_release(x_999, 1);
 x_1003 = x_999;
} else {
 lean_dec_ref(x_999);
 x_1003 = lean_box(0);
}
x_1004 = lean_expr_update_proj(x_5, x_1001);
if (lean_is_scalar(x_1003)) {
 x_1005 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1005 = x_1003;
}
lean_ctor_set(x_1005, 0, x_1004);
lean_ctor_set(x_1005, 1, x_1002);
x_1006 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1006, 0, x_1005);
lean_ctor_set(x_1006, 1, x_1000);
return x_1006;
}
}
else
{
uint8_t x_1007; 
lean_dec(x_5);
x_1007 = !lean_is_exclusive(x_989);
if (x_1007 == 0)
{
return x_989;
}
else
{
lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
x_1008 = lean_ctor_get(x_989, 0);
x_1009 = lean_ctor_get(x_989, 1);
lean_inc(x_1009);
lean_inc(x_1008);
lean_dec(x_989);
x_1010 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1010, 0, x_1008);
lean_ctor_set(x_1010, 1, x_1009);
return x_1010;
}
}
}
default: 
{
lean_object* x_1011; lean_object* x_1012; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_1011 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1011, 0, x_5);
lean_ctor_set(x_1011, 1, x_7);
x_1012 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1012, 0, x_1011);
lean_ctor_set(x_1012, 1, x_9);
return x_1012;
}
}
}
block_215:
{
lean_dec(x_10);
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_5, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_13 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_12, x_6, x_17, x_8, x_15);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_expr_update_app(x_5, x_16, x_22);
lean_ctor_set(x_20, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_expr_update_app(x_5, x_16, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_18, 0, x_27);
return x_18;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_ctor_get(x_18, 0);
x_29 = lean_ctor_get(x_18, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_18);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_32 = x_28;
} else {
 lean_dec_ref(x_28);
 x_32 = lean_box(0);
}
x_33 = lean_expr_update_app(x_5, x_16, x_30);
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_29);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_16);
lean_dec(x_5);
x_36 = !lean_is_exclusive(x_18);
if (x_36 == 0)
{
return x_18;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_18, 0);
x_38 = lean_ctor_get(x_18, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_18);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
return x_13;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
case 6:
{
lean_object* x_44; lean_object* x_45; uint64_t x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_5, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_5, 2);
lean_inc(x_45);
x_46 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_47 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_44, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_add(x_6, x_52);
lean_dec(x_6);
x_54 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_45, x_53, x_51, x_8, x_49);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = !lean_is_exclusive(x_56);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_56, 0);
x_59 = (uint8_t)((x_46 << 24) >> 61);
x_60 = lean_expr_update_lambda(x_5, x_59, x_50, x_58);
lean_ctor_set(x_56, 0, x_60);
return x_54;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; 
x_61 = lean_ctor_get(x_56, 0);
x_62 = lean_ctor_get(x_56, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_56);
x_63 = (uint8_t)((x_46 << 24) >> 61);
x_64 = lean_expr_update_lambda(x_5, x_63, x_50, x_61);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
lean_ctor_set(x_54, 0, x_65);
return x_54;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_66 = lean_ctor_get(x_54, 0);
x_67 = lean_ctor_get(x_54, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_54);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_70 = x_66;
} else {
 lean_dec_ref(x_66);
 x_70 = lean_box(0);
}
x_71 = (uint8_t)((x_46 << 24) >> 61);
x_72 = lean_expr_update_lambda(x_5, x_71, x_50, x_68);
if (lean_is_scalar(x_70)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_70;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_69);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_67);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_50);
lean_dec(x_5);
x_75 = !lean_is_exclusive(x_54);
if (x_75 == 0)
{
return x_54;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_54, 0);
x_77 = lean_ctor_get(x_54, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_54);
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
lean_dec(x_45);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_79 = !lean_is_exclusive(x_47);
if (x_79 == 0)
{
return x_47;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_47, 0);
x_81 = lean_ctor_get(x_47, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_47);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
case 7:
{
lean_object* x_83; lean_object* x_84; uint64_t x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_5, 1);
lean_inc(x_83);
x_84 = lean_ctor_get(x_5, 2);
lean_inc(x_84);
x_85 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_86 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_83, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_87, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_add(x_6, x_91);
lean_dec(x_6);
x_93 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_84, x_92, x_90, x_8, x_88);
if (lean_obj_tag(x_93) == 0)
{
uint8_t x_94; 
x_94 = !lean_is_exclusive(x_93);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; 
x_95 = lean_ctor_get(x_93, 0);
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = (uint8_t)((x_85 << 24) >> 61);
x_99 = lean_expr_update_forall(x_5, x_98, x_89, x_97);
lean_ctor_set(x_95, 0, x_99);
return x_93;
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_95, 0);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_95);
x_102 = (uint8_t)((x_85 << 24) >> 61);
x_103 = lean_expr_update_forall(x_5, x_102, x_89, x_100);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
lean_ctor_set(x_93, 0, x_104);
return x_93;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_105 = lean_ctor_get(x_93, 0);
x_106 = lean_ctor_get(x_93, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_93);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_109 = x_105;
} else {
 lean_dec_ref(x_105);
 x_109 = lean_box(0);
}
x_110 = (uint8_t)((x_85 << 24) >> 61);
x_111 = lean_expr_update_forall(x_5, x_110, x_89, x_107);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_108);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_106);
return x_113;
}
}
else
{
uint8_t x_114; 
lean_dec(x_89);
lean_dec(x_5);
x_114 = !lean_is_exclusive(x_93);
if (x_114 == 0)
{
return x_93;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_93, 0);
x_116 = lean_ctor_get(x_93, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_93);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
else
{
uint8_t x_118; 
lean_dec(x_84);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_118 = !lean_is_exclusive(x_86);
if (x_118 == 0)
{
return x_86;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_86, 0);
x_120 = lean_ctor_get(x_86, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_86);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
}
case 8:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_122 = lean_ctor_get(x_5, 1);
lean_inc(x_122);
x_123 = lean_ctor_get(x_5, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_5, 3);
lean_inc(x_124);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_125 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_122, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
lean_dec(x_126);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_130 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_123, x_6, x_129, x_8, x_127);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_unsigned_to_nat(1u);
x_136 = lean_nat_add(x_6, x_135);
lean_dec(x_6);
x_137 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_124, x_136, x_134, x_8, x_132);
if (lean_obj_tag(x_137) == 0)
{
uint8_t x_138; 
x_138 = !lean_is_exclusive(x_137);
if (x_138 == 0)
{
lean_object* x_139; uint8_t x_140; 
x_139 = lean_ctor_get(x_137, 0);
x_140 = !lean_is_exclusive(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_ctor_get(x_139, 0);
x_142 = lean_expr_update_let(x_5, x_128, x_133, x_141);
lean_ctor_set(x_139, 0, x_142);
return x_137;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_143 = lean_ctor_get(x_139, 0);
x_144 = lean_ctor_get(x_139, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_139);
x_145 = lean_expr_update_let(x_5, x_128, x_133, x_143);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_144);
lean_ctor_set(x_137, 0, x_146);
return x_137;
}
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_147 = lean_ctor_get(x_137, 0);
x_148 = lean_ctor_get(x_137, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_137);
x_149 = lean_ctor_get(x_147, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_151 = x_147;
} else {
 lean_dec_ref(x_147);
 x_151 = lean_box(0);
}
x_152 = lean_expr_update_let(x_5, x_128, x_133, x_149);
if (lean_is_scalar(x_151)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_151;
}
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_150);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_148);
return x_154;
}
}
else
{
uint8_t x_155; 
lean_dec(x_133);
lean_dec(x_128);
lean_dec(x_5);
x_155 = !lean_is_exclusive(x_137);
if (x_155 == 0)
{
return x_137;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_137, 0);
x_157 = lean_ctor_get(x_137, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_137);
x_158 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_158, 0, x_156);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
else
{
uint8_t x_159; 
lean_dec(x_128);
lean_dec(x_124);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_159 = !lean_is_exclusive(x_130);
if (x_159 == 0)
{
return x_130;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_130, 0);
x_161 = lean_ctor_get(x_130, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_130);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_163 = !lean_is_exclusive(x_125);
if (x_163 == 0)
{
return x_125;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_125, 0);
x_165 = lean_ctor_get(x_125, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_125);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
case 10:
{
lean_object* x_167; lean_object* x_168; 
x_167 = lean_ctor_get(x_5, 1);
lean_inc(x_167);
x_168 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_167, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_168) == 0)
{
uint8_t x_169; 
x_169 = !lean_is_exclusive(x_168);
if (x_169 == 0)
{
lean_object* x_170; uint8_t x_171; 
x_170 = lean_ctor_get(x_168, 0);
x_171 = !lean_is_exclusive(x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_170, 0);
x_173 = lean_expr_update_mdata(x_5, x_172);
lean_ctor_set(x_170, 0, x_173);
return x_168;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_174 = lean_ctor_get(x_170, 0);
x_175 = lean_ctor_get(x_170, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_170);
x_176 = lean_expr_update_mdata(x_5, x_174);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_175);
lean_ctor_set(x_168, 0, x_177);
return x_168;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_178 = lean_ctor_get(x_168, 0);
x_179 = lean_ctor_get(x_168, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_168);
x_180 = lean_ctor_get(x_178, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_182 = x_178;
} else {
 lean_dec_ref(x_178);
 x_182 = lean_box(0);
}
x_183 = lean_expr_update_mdata(x_5, x_180);
if (lean_is_scalar(x_182)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_182;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_181);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_179);
return x_185;
}
}
else
{
uint8_t x_186; 
lean_dec(x_5);
x_186 = !lean_is_exclusive(x_168);
if (x_186 == 0)
{
return x_168;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_168, 0);
x_188 = lean_ctor_get(x_168, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_168);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
case 11:
{
lean_object* x_190; lean_object* x_191; 
x_190 = lean_ctor_get(x_5, 2);
lean_inc(x_190);
x_191 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_190, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_191) == 0)
{
uint8_t x_192; 
x_192 = !lean_is_exclusive(x_191);
if (x_192 == 0)
{
lean_object* x_193; uint8_t x_194; 
x_193 = lean_ctor_get(x_191, 0);
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; 
x_195 = lean_ctor_get(x_193, 0);
x_196 = lean_expr_update_proj(x_5, x_195);
lean_ctor_set(x_193, 0, x_196);
return x_191;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_197 = lean_ctor_get(x_193, 0);
x_198 = lean_ctor_get(x_193, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_193);
x_199 = lean_expr_update_proj(x_5, x_197);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_198);
lean_ctor_set(x_191, 0, x_200);
return x_191;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_201 = lean_ctor_get(x_191, 0);
x_202 = lean_ctor_get(x_191, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_191);
x_203 = lean_ctor_get(x_201, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_205 = x_201;
} else {
 lean_dec_ref(x_201);
 x_205 = lean_box(0);
}
x_206 = lean_expr_update_proj(x_5, x_203);
if (lean_is_scalar(x_205)) {
 x_207 = lean_alloc_ctor(0, 2, 0);
} else {
 x_207 = x_205;
}
lean_ctor_set(x_207, 0, x_206);
lean_ctor_set(x_207, 1, x_204);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_202);
return x_208;
}
}
else
{
uint8_t x_209; 
lean_dec(x_5);
x_209 = !lean_is_exclusive(x_191);
if (x_209 == 0)
{
return x_191;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_191, 0);
x_211 = lean_ctor_get(x_191, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_191);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
default: 
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_5);
lean_ctor_set(x_213, 1, x_7);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_9);
return x_214;
}
}
}
}
}
lean_object* l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_KAbstract_1__kabstractAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
lean_object* l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
lean_object* l_Lean_Meta_kabstract(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_6 = l_Lean_Expr_toHeadIndex___main(x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l___private_Init_Lean_HeadIndex_1__headNumArgsAux___main(x_2, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l___private_Init_Lean_Meta_KAbstract_1__kabstractAux___main(x_3, x_2, x_6, x_8, x_1, x_7, x_9, x_4, x_5);
lean_dec(x_8);
lean_dec(x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
return x_10;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_10);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
lean_object* l_Lean_Meta_kabstract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_kabstract(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* initialize_Init_Lean_Data_Occurrences(lean_object*);
lean_object* initialize_Init_Lean_HeadIndex(lean_object*);
lean_object* initialize_Init_Lean_Meta_ExprDefEq(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_KAbstract(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Data_Occurrences(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_HeadIndex(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Lean_Meta_ExprDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
