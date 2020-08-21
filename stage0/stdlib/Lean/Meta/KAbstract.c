// Lean compiler output
// Module: Lean.Meta.KAbstract
// Imports: Init Lean.Data.Occurrences Lean.HeadIndex Lean.Meta.ExprDefEq
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
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* l___private_Lean_HeadIndex_1__headNumArgsAux___main(lean_object*, lean_object*);
uint8_t l_Lean_HeadIndex_HeadIndex_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex___main(lean_object*);
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux___main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Occurrences_contains(lean_object*, lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux___main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_kabstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux___main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_219; 
x_219 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_219 == 0)
{
lean_object* x_220; uint8_t x_221; 
x_220 = l_Lean_Expr_toHeadIndex___main(x_5);
x_221 = l_Lean_HeadIndex_HeadIndex_beq(x_220, x_3);
lean_dec(x_220);
if (x_221 == 0)
{
lean_object* x_222; 
x_222 = lean_box(0);
x_13 = x_222;
goto block_218;
}
else
{
lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_223 = lean_unsigned_to_nat(0u);
x_224 = l___private_Lean_HeadIndex_1__headNumArgsAux___main(x_5, x_223);
x_225 = lean_nat_dec_eq(x_224, x_4);
lean_dec(x_224);
if (x_225 == 0)
{
lean_object* x_226; 
x_226 = lean_box(0);
x_13 = x_226;
goto block_218;
}
else
{
lean_object* x_227; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_5);
x_227 = l_Lean_Meta_isExprDefEq(x_5, x_2, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; uint8_t x_229; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_unbox(x_228);
lean_dec(x_228);
if (x_229 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_230 = lean_ctor_get(x_227, 1);
lean_inc(x_230);
lean_dec(x_227);
x_231 = lean_ctor_get(x_5, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_5, 1);
lean_inc(x_232);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_233 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_231, x_6, x_7, x_8, x_9, x_10, x_11, x_230);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = lean_ctor_get(x_234, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_234, 1);
lean_inc(x_237);
lean_dec(x_234);
x_238 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_232, x_6, x_237, x_8, x_9, x_10, x_11, x_235);
if (lean_obj_tag(x_238) == 0)
{
uint8_t x_239; 
x_239 = !lean_is_exclusive(x_238);
if (x_239 == 0)
{
lean_object* x_240; uint8_t x_241; 
x_240 = lean_ctor_get(x_238, 0);
x_241 = !lean_is_exclusive(x_240);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; 
x_242 = lean_ctor_get(x_240, 0);
x_243 = lean_expr_update_app(x_5, x_236, x_242);
lean_ctor_set(x_240, 0, x_243);
return x_238;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_244 = lean_ctor_get(x_240, 0);
x_245 = lean_ctor_get(x_240, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_240);
x_246 = lean_expr_update_app(x_5, x_236, x_244);
x_247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_245);
lean_ctor_set(x_238, 0, x_247);
return x_238;
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_248 = lean_ctor_get(x_238, 0);
x_249 = lean_ctor_get(x_238, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_238);
x_250 = lean_ctor_get(x_248, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_248, 1);
lean_inc(x_251);
if (lean_is_exclusive(x_248)) {
 lean_ctor_release(x_248, 0);
 lean_ctor_release(x_248, 1);
 x_252 = x_248;
} else {
 lean_dec_ref(x_248);
 x_252 = lean_box(0);
}
x_253 = lean_expr_update_app(x_5, x_236, x_250);
if (lean_is_scalar(x_252)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_252;
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_251);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_249);
return x_255;
}
}
else
{
uint8_t x_256; 
lean_dec(x_236);
lean_dec(x_5);
x_256 = !lean_is_exclusive(x_238);
if (x_256 == 0)
{
return x_238;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_238, 0);
x_258 = lean_ctor_get(x_238, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_238);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
else
{
uint8_t x_260; 
lean_dec(x_232);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_260 = !lean_is_exclusive(x_233);
if (x_260 == 0)
{
return x_233;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_233, 0);
x_262 = lean_ctor_get(x_233, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_233);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
}
case 6:
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; uint64_t x_267; lean_object* x_268; 
x_264 = lean_ctor_get(x_227, 1);
lean_inc(x_264);
lean_dec(x_227);
x_265 = lean_ctor_get(x_5, 1);
lean_inc(x_265);
x_266 = lean_ctor_get(x_5, 2);
lean_inc(x_266);
x_267 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_268 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_265, x_6, x_7, x_8, x_9, x_10, x_11, x_264);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
x_271 = lean_ctor_get(x_269, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_269, 1);
lean_inc(x_272);
lean_dec(x_269);
x_273 = lean_unsigned_to_nat(1u);
x_274 = lean_nat_add(x_6, x_273);
lean_dec(x_6);
x_275 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_266, x_274, x_272, x_8, x_9, x_10, x_11, x_270);
if (lean_obj_tag(x_275) == 0)
{
uint8_t x_276; 
x_276 = !lean_is_exclusive(x_275);
if (x_276 == 0)
{
lean_object* x_277; uint8_t x_278; 
x_277 = lean_ctor_get(x_275, 0);
x_278 = !lean_is_exclusive(x_277);
if (x_278 == 0)
{
lean_object* x_279; uint8_t x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_277, 0);
x_280 = (uint8_t)((x_267 << 24) >> 61);
x_281 = lean_expr_update_lambda(x_5, x_280, x_271, x_279);
lean_ctor_set(x_277, 0, x_281);
return x_275;
}
else
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; lean_object* x_285; lean_object* x_286; 
x_282 = lean_ctor_get(x_277, 0);
x_283 = lean_ctor_get(x_277, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_277);
x_284 = (uint8_t)((x_267 << 24) >> 61);
x_285 = lean_expr_update_lambda(x_5, x_284, x_271, x_282);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_283);
lean_ctor_set(x_275, 0, x_286);
return x_275;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; uint8_t x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_287 = lean_ctor_get(x_275, 0);
x_288 = lean_ctor_get(x_275, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_275);
x_289 = lean_ctor_get(x_287, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_287, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_291 = x_287;
} else {
 lean_dec_ref(x_287);
 x_291 = lean_box(0);
}
x_292 = (uint8_t)((x_267 << 24) >> 61);
x_293 = lean_expr_update_lambda(x_5, x_292, x_271, x_289);
if (lean_is_scalar(x_291)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_291;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_290);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_288);
return x_295;
}
}
else
{
uint8_t x_296; 
lean_dec(x_271);
lean_dec(x_5);
x_296 = !lean_is_exclusive(x_275);
if (x_296 == 0)
{
return x_275;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_297 = lean_ctor_get(x_275, 0);
x_298 = lean_ctor_get(x_275, 1);
lean_inc(x_298);
lean_inc(x_297);
lean_dec(x_275);
x_299 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_299, 0, x_297);
lean_ctor_set(x_299, 1, x_298);
return x_299;
}
}
}
else
{
uint8_t x_300; 
lean_dec(x_266);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_300 = !lean_is_exclusive(x_268);
if (x_300 == 0)
{
return x_268;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_301 = lean_ctor_get(x_268, 0);
x_302 = lean_ctor_get(x_268, 1);
lean_inc(x_302);
lean_inc(x_301);
lean_dec(x_268);
x_303 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_303, 0, x_301);
lean_ctor_set(x_303, 1, x_302);
return x_303;
}
}
}
case 7:
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; uint64_t x_307; lean_object* x_308; 
x_304 = lean_ctor_get(x_227, 1);
lean_inc(x_304);
lean_dec(x_227);
x_305 = lean_ctor_get(x_5, 1);
lean_inc(x_305);
x_306 = lean_ctor_get(x_5, 2);
lean_inc(x_306);
x_307 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_308 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_305, x_6, x_7, x_8, x_9, x_10, x_11, x_304);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
x_311 = lean_ctor_get(x_309, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_309, 1);
lean_inc(x_312);
lean_dec(x_309);
x_313 = lean_unsigned_to_nat(1u);
x_314 = lean_nat_add(x_6, x_313);
lean_dec(x_6);
x_315 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_306, x_314, x_312, x_8, x_9, x_10, x_11, x_310);
if (lean_obj_tag(x_315) == 0)
{
uint8_t x_316; 
x_316 = !lean_is_exclusive(x_315);
if (x_316 == 0)
{
lean_object* x_317; uint8_t x_318; 
x_317 = lean_ctor_get(x_315, 0);
x_318 = !lean_is_exclusive(x_317);
if (x_318 == 0)
{
lean_object* x_319; uint8_t x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_317, 0);
x_320 = (uint8_t)((x_307 << 24) >> 61);
x_321 = lean_expr_update_forall(x_5, x_320, x_311, x_319);
lean_ctor_set(x_317, 0, x_321);
return x_315;
}
else
{
lean_object* x_322; lean_object* x_323; uint8_t x_324; lean_object* x_325; lean_object* x_326; 
x_322 = lean_ctor_get(x_317, 0);
x_323 = lean_ctor_get(x_317, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_317);
x_324 = (uint8_t)((x_307 << 24) >> 61);
x_325 = lean_expr_update_forall(x_5, x_324, x_311, x_322);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_323);
lean_ctor_set(x_315, 0, x_326);
return x_315;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; uint8_t x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
x_327 = lean_ctor_get(x_315, 0);
x_328 = lean_ctor_get(x_315, 1);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_315);
x_329 = lean_ctor_get(x_327, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_327, 1);
lean_inc(x_330);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_331 = x_327;
} else {
 lean_dec_ref(x_327);
 x_331 = lean_box(0);
}
x_332 = (uint8_t)((x_307 << 24) >> 61);
x_333 = lean_expr_update_forall(x_5, x_332, x_311, x_329);
if (lean_is_scalar(x_331)) {
 x_334 = lean_alloc_ctor(0, 2, 0);
} else {
 x_334 = x_331;
}
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_330);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_328);
return x_335;
}
}
else
{
uint8_t x_336; 
lean_dec(x_311);
lean_dec(x_5);
x_336 = !lean_is_exclusive(x_315);
if (x_336 == 0)
{
return x_315;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; 
x_337 = lean_ctor_get(x_315, 0);
x_338 = lean_ctor_get(x_315, 1);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_315);
x_339 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_339, 0, x_337);
lean_ctor_set(x_339, 1, x_338);
return x_339;
}
}
}
else
{
uint8_t x_340; 
lean_dec(x_306);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_340 = !lean_is_exclusive(x_308);
if (x_340 == 0)
{
return x_308;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_308, 0);
x_342 = lean_ctor_get(x_308, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_308);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
return x_343;
}
}
}
case 8:
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_344 = lean_ctor_get(x_227, 1);
lean_inc(x_344);
lean_dec(x_227);
x_345 = lean_ctor_get(x_5, 1);
lean_inc(x_345);
x_346 = lean_ctor_get(x_5, 2);
lean_inc(x_346);
x_347 = lean_ctor_get(x_5, 3);
lean_inc(x_347);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_348 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_345, x_6, x_7, x_8, x_9, x_10, x_11, x_344);
if (lean_obj_tag(x_348) == 0)
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_348, 1);
lean_inc(x_350);
lean_dec(x_348);
x_351 = lean_ctor_get(x_349, 0);
lean_inc(x_351);
x_352 = lean_ctor_get(x_349, 1);
lean_inc(x_352);
lean_dec(x_349);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_353 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_346, x_6, x_352, x_8, x_9, x_10, x_11, x_350);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = lean_ctor_get(x_354, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_354, 1);
lean_inc(x_357);
lean_dec(x_354);
x_358 = lean_unsigned_to_nat(1u);
x_359 = lean_nat_add(x_6, x_358);
lean_dec(x_6);
x_360 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_347, x_359, x_357, x_8, x_9, x_10, x_11, x_355);
if (lean_obj_tag(x_360) == 0)
{
uint8_t x_361; 
x_361 = !lean_is_exclusive(x_360);
if (x_361 == 0)
{
lean_object* x_362; uint8_t x_363; 
x_362 = lean_ctor_get(x_360, 0);
x_363 = !lean_is_exclusive(x_362);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; 
x_364 = lean_ctor_get(x_362, 0);
x_365 = lean_expr_update_let(x_5, x_351, x_356, x_364);
lean_ctor_set(x_362, 0, x_365);
return x_360;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_366 = lean_ctor_get(x_362, 0);
x_367 = lean_ctor_get(x_362, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_362);
x_368 = lean_expr_update_let(x_5, x_351, x_356, x_366);
x_369 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_369, 0, x_368);
lean_ctor_set(x_369, 1, x_367);
lean_ctor_set(x_360, 0, x_369);
return x_360;
}
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_370 = lean_ctor_get(x_360, 0);
x_371 = lean_ctor_get(x_360, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_360);
x_372 = lean_ctor_get(x_370, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_370, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_370)) {
 lean_ctor_release(x_370, 0);
 lean_ctor_release(x_370, 1);
 x_374 = x_370;
} else {
 lean_dec_ref(x_370);
 x_374 = lean_box(0);
}
x_375 = lean_expr_update_let(x_5, x_351, x_356, x_372);
if (lean_is_scalar(x_374)) {
 x_376 = lean_alloc_ctor(0, 2, 0);
} else {
 x_376 = x_374;
}
lean_ctor_set(x_376, 0, x_375);
lean_ctor_set(x_376, 1, x_373);
x_377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_371);
return x_377;
}
}
else
{
uint8_t x_378; 
lean_dec(x_356);
lean_dec(x_351);
lean_dec(x_5);
x_378 = !lean_is_exclusive(x_360);
if (x_378 == 0)
{
return x_360;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_360, 0);
x_380 = lean_ctor_get(x_360, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_360);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
return x_381;
}
}
}
else
{
uint8_t x_382; 
lean_dec(x_351);
lean_dec(x_347);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_382 = !lean_is_exclusive(x_353);
if (x_382 == 0)
{
return x_353;
}
else
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; 
x_383 = lean_ctor_get(x_353, 0);
x_384 = lean_ctor_get(x_353, 1);
lean_inc(x_384);
lean_inc(x_383);
lean_dec(x_353);
x_385 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_385, 0, x_383);
lean_ctor_set(x_385, 1, x_384);
return x_385;
}
}
}
else
{
uint8_t x_386; 
lean_dec(x_347);
lean_dec(x_346);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_386 = !lean_is_exclusive(x_348);
if (x_386 == 0)
{
return x_348;
}
else
{
lean_object* x_387; lean_object* x_388; lean_object* x_389; 
x_387 = lean_ctor_get(x_348, 0);
x_388 = lean_ctor_get(x_348, 1);
lean_inc(x_388);
lean_inc(x_387);
lean_dec(x_348);
x_389 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_389, 0, x_387);
lean_ctor_set(x_389, 1, x_388);
return x_389;
}
}
}
case 10:
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_227, 1);
lean_inc(x_390);
lean_dec(x_227);
x_391 = lean_ctor_get(x_5, 1);
lean_inc(x_391);
x_392 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_391, x_6, x_7, x_8, x_9, x_10, x_11, x_390);
if (lean_obj_tag(x_392) == 0)
{
uint8_t x_393; 
x_393 = !lean_is_exclusive(x_392);
if (x_393 == 0)
{
lean_object* x_394; uint8_t x_395; 
x_394 = lean_ctor_get(x_392, 0);
x_395 = !lean_is_exclusive(x_394);
if (x_395 == 0)
{
lean_object* x_396; lean_object* x_397; 
x_396 = lean_ctor_get(x_394, 0);
x_397 = lean_expr_update_mdata(x_5, x_396);
lean_ctor_set(x_394, 0, x_397);
return x_392;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; 
x_398 = lean_ctor_get(x_394, 0);
x_399 = lean_ctor_get(x_394, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_394);
x_400 = lean_expr_update_mdata(x_5, x_398);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_399);
lean_ctor_set(x_392, 0, x_401);
return x_392;
}
}
else
{
lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_402 = lean_ctor_get(x_392, 0);
x_403 = lean_ctor_get(x_392, 1);
lean_inc(x_403);
lean_inc(x_402);
lean_dec(x_392);
x_404 = lean_ctor_get(x_402, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_402, 1);
lean_inc(x_405);
if (lean_is_exclusive(x_402)) {
 lean_ctor_release(x_402, 0);
 lean_ctor_release(x_402, 1);
 x_406 = x_402;
} else {
 lean_dec_ref(x_402);
 x_406 = lean_box(0);
}
x_407 = lean_expr_update_mdata(x_5, x_404);
if (lean_is_scalar(x_406)) {
 x_408 = lean_alloc_ctor(0, 2, 0);
} else {
 x_408 = x_406;
}
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_405);
x_409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_403);
return x_409;
}
}
else
{
uint8_t x_410; 
lean_dec(x_5);
x_410 = !lean_is_exclusive(x_392);
if (x_410 == 0)
{
return x_392;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_411 = lean_ctor_get(x_392, 0);
x_412 = lean_ctor_get(x_392, 1);
lean_inc(x_412);
lean_inc(x_411);
lean_dec(x_392);
x_413 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
return x_413;
}
}
}
case 11:
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; 
x_414 = lean_ctor_get(x_227, 1);
lean_inc(x_414);
lean_dec(x_227);
x_415 = lean_ctor_get(x_5, 2);
lean_inc(x_415);
x_416 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_415, x_6, x_7, x_8, x_9, x_10, x_11, x_414);
if (lean_obj_tag(x_416) == 0)
{
uint8_t x_417; 
x_417 = !lean_is_exclusive(x_416);
if (x_417 == 0)
{
lean_object* x_418; uint8_t x_419; 
x_418 = lean_ctor_get(x_416, 0);
x_419 = !lean_is_exclusive(x_418);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; 
x_420 = lean_ctor_get(x_418, 0);
x_421 = lean_expr_update_proj(x_5, x_420);
lean_ctor_set(x_418, 0, x_421);
return x_416;
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_422 = lean_ctor_get(x_418, 0);
x_423 = lean_ctor_get(x_418, 1);
lean_inc(x_423);
lean_inc(x_422);
lean_dec(x_418);
x_424 = lean_expr_update_proj(x_5, x_422);
x_425 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_423);
lean_ctor_set(x_416, 0, x_425);
return x_416;
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_426 = lean_ctor_get(x_416, 0);
x_427 = lean_ctor_get(x_416, 1);
lean_inc(x_427);
lean_inc(x_426);
lean_dec(x_416);
x_428 = lean_ctor_get(x_426, 0);
lean_inc(x_428);
x_429 = lean_ctor_get(x_426, 1);
lean_inc(x_429);
if (lean_is_exclusive(x_426)) {
 lean_ctor_release(x_426, 0);
 lean_ctor_release(x_426, 1);
 x_430 = x_426;
} else {
 lean_dec_ref(x_426);
 x_430 = lean_box(0);
}
x_431 = lean_expr_update_proj(x_5, x_428);
if (lean_is_scalar(x_430)) {
 x_432 = lean_alloc_ctor(0, 2, 0);
} else {
 x_432 = x_430;
}
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_429);
x_433 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_427);
return x_433;
}
}
else
{
uint8_t x_434; 
lean_dec(x_5);
x_434 = !lean_is_exclusive(x_416);
if (x_434 == 0)
{
return x_416;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_416, 0);
x_436 = lean_ctor_get(x_416, 1);
lean_inc(x_436);
lean_inc(x_435);
lean_dec(x_416);
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
}
}
default: 
{
uint8_t x_438; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_438 = !lean_is_exclusive(x_227);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; 
x_439 = lean_ctor_get(x_227, 0);
lean_dec(x_439);
x_440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_440, 0, x_5);
lean_ctor_set(x_440, 1, x_7);
lean_ctor_set(x_227, 0, x_440);
return x_227;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_441 = lean_ctor_get(x_227, 1);
lean_inc(x_441);
lean_dec(x_227);
x_442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_442, 0, x_5);
lean_ctor_set(x_442, 1, x_7);
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_442);
lean_ctor_set(x_443, 1, x_441);
return x_443;
}
}
}
}
else
{
uint8_t x_444; 
x_444 = !lean_is_exclusive(x_227);
if (x_444 == 0)
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; 
x_445 = lean_ctor_get(x_227, 1);
x_446 = lean_ctor_get(x_227, 0);
lean_dec(x_446);
x_447 = lean_unsigned_to_nat(1u);
x_448 = lean_nat_add(x_7, x_447);
x_449 = l_Lean_Occurrences_contains(x_1, x_7);
lean_dec(x_7);
if (x_449 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_free_object(x_227);
x_450 = lean_ctor_get(x_5, 0);
lean_inc(x_450);
x_451 = lean_ctor_get(x_5, 1);
lean_inc(x_451);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_452 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_450, x_6, x_448, x_8, x_9, x_10, x_11, x_445);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_ctor_get(x_452, 1);
lean_inc(x_454);
lean_dec(x_452);
x_455 = lean_ctor_get(x_453, 0);
lean_inc(x_455);
x_456 = lean_ctor_get(x_453, 1);
lean_inc(x_456);
lean_dec(x_453);
x_457 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_451, x_6, x_456, x_8, x_9, x_10, x_11, x_454);
if (lean_obj_tag(x_457) == 0)
{
uint8_t x_458; 
x_458 = !lean_is_exclusive(x_457);
if (x_458 == 0)
{
lean_object* x_459; uint8_t x_460; 
x_459 = lean_ctor_get(x_457, 0);
x_460 = !lean_is_exclusive(x_459);
if (x_460 == 0)
{
lean_object* x_461; lean_object* x_462; 
x_461 = lean_ctor_get(x_459, 0);
x_462 = lean_expr_update_app(x_5, x_455, x_461);
lean_ctor_set(x_459, 0, x_462);
return x_457;
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_463 = lean_ctor_get(x_459, 0);
x_464 = lean_ctor_get(x_459, 1);
lean_inc(x_464);
lean_inc(x_463);
lean_dec(x_459);
x_465 = lean_expr_update_app(x_5, x_455, x_463);
x_466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_466, 0, x_465);
lean_ctor_set(x_466, 1, x_464);
lean_ctor_set(x_457, 0, x_466);
return x_457;
}
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_467 = lean_ctor_get(x_457, 0);
x_468 = lean_ctor_get(x_457, 1);
lean_inc(x_468);
lean_inc(x_467);
lean_dec(x_457);
x_469 = lean_ctor_get(x_467, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_467, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_467)) {
 lean_ctor_release(x_467, 0);
 lean_ctor_release(x_467, 1);
 x_471 = x_467;
} else {
 lean_dec_ref(x_467);
 x_471 = lean_box(0);
}
x_472 = lean_expr_update_app(x_5, x_455, x_469);
if (lean_is_scalar(x_471)) {
 x_473 = lean_alloc_ctor(0, 2, 0);
} else {
 x_473 = x_471;
}
lean_ctor_set(x_473, 0, x_472);
lean_ctor_set(x_473, 1, x_470);
x_474 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_474, 0, x_473);
lean_ctor_set(x_474, 1, x_468);
return x_474;
}
}
else
{
uint8_t x_475; 
lean_dec(x_455);
lean_dec(x_5);
x_475 = !lean_is_exclusive(x_457);
if (x_475 == 0)
{
return x_457;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_457, 0);
x_477 = lean_ctor_get(x_457, 1);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_457);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_477);
return x_478;
}
}
}
else
{
uint8_t x_479; 
lean_dec(x_451);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_479 = !lean_is_exclusive(x_452);
if (x_479 == 0)
{
return x_452;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_480 = lean_ctor_get(x_452, 0);
x_481 = lean_ctor_get(x_452, 1);
lean_inc(x_481);
lean_inc(x_480);
lean_dec(x_452);
x_482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_482, 0, x_480);
lean_ctor_set(x_482, 1, x_481);
return x_482;
}
}
}
case 6:
{
lean_object* x_483; lean_object* x_484; uint64_t x_485; lean_object* x_486; 
lean_free_object(x_227);
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
lean_inc(x_2);
x_486 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_483, x_6, x_448, x_8, x_9, x_10, x_11, x_445);
if (lean_obj_tag(x_486) == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_486, 1);
lean_inc(x_488);
lean_dec(x_486);
x_489 = lean_ctor_get(x_487, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_487, 1);
lean_inc(x_490);
lean_dec(x_487);
x_491 = lean_nat_add(x_6, x_447);
lean_dec(x_6);
x_492 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_484, x_491, x_490, x_8, x_9, x_10, x_11, x_488);
if (lean_obj_tag(x_492) == 0)
{
uint8_t x_493; 
x_493 = !lean_is_exclusive(x_492);
if (x_493 == 0)
{
lean_object* x_494; uint8_t x_495; 
x_494 = lean_ctor_get(x_492, 0);
x_495 = !lean_is_exclusive(x_494);
if (x_495 == 0)
{
lean_object* x_496; uint8_t x_497; lean_object* x_498; 
x_496 = lean_ctor_get(x_494, 0);
x_497 = (uint8_t)((x_485 << 24) >> 61);
x_498 = lean_expr_update_lambda(x_5, x_497, x_489, x_496);
lean_ctor_set(x_494, 0, x_498);
return x_492;
}
else
{
lean_object* x_499; lean_object* x_500; uint8_t x_501; lean_object* x_502; lean_object* x_503; 
x_499 = lean_ctor_get(x_494, 0);
x_500 = lean_ctor_get(x_494, 1);
lean_inc(x_500);
lean_inc(x_499);
lean_dec(x_494);
x_501 = (uint8_t)((x_485 << 24) >> 61);
x_502 = lean_expr_update_lambda(x_5, x_501, x_489, x_499);
x_503 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_503, 0, x_502);
lean_ctor_set(x_503, 1, x_500);
lean_ctor_set(x_492, 0, x_503);
return x_492;
}
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_504 = lean_ctor_get(x_492, 0);
x_505 = lean_ctor_get(x_492, 1);
lean_inc(x_505);
lean_inc(x_504);
lean_dec(x_492);
x_506 = lean_ctor_get(x_504, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_504, 1);
lean_inc(x_507);
if (lean_is_exclusive(x_504)) {
 lean_ctor_release(x_504, 0);
 lean_ctor_release(x_504, 1);
 x_508 = x_504;
} else {
 lean_dec_ref(x_504);
 x_508 = lean_box(0);
}
x_509 = (uint8_t)((x_485 << 24) >> 61);
x_510 = lean_expr_update_lambda(x_5, x_509, x_489, x_506);
if (lean_is_scalar(x_508)) {
 x_511 = lean_alloc_ctor(0, 2, 0);
} else {
 x_511 = x_508;
}
lean_ctor_set(x_511, 0, x_510);
lean_ctor_set(x_511, 1, x_507);
x_512 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_505);
return x_512;
}
}
else
{
uint8_t x_513; 
lean_dec(x_489);
lean_dec(x_5);
x_513 = !lean_is_exclusive(x_492);
if (x_513 == 0)
{
return x_492;
}
else
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; 
x_514 = lean_ctor_get(x_492, 0);
x_515 = lean_ctor_get(x_492, 1);
lean_inc(x_515);
lean_inc(x_514);
lean_dec(x_492);
x_516 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_516, 0, x_514);
lean_ctor_set(x_516, 1, x_515);
return x_516;
}
}
}
else
{
uint8_t x_517; 
lean_dec(x_484);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_517 = !lean_is_exclusive(x_486);
if (x_517 == 0)
{
return x_486;
}
else
{
lean_object* x_518; lean_object* x_519; lean_object* x_520; 
x_518 = lean_ctor_get(x_486, 0);
x_519 = lean_ctor_get(x_486, 1);
lean_inc(x_519);
lean_inc(x_518);
lean_dec(x_486);
x_520 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_520, 0, x_518);
lean_ctor_set(x_520, 1, x_519);
return x_520;
}
}
}
case 7:
{
lean_object* x_521; lean_object* x_522; uint64_t x_523; lean_object* x_524; 
lean_free_object(x_227);
x_521 = lean_ctor_get(x_5, 1);
lean_inc(x_521);
x_522 = lean_ctor_get(x_5, 2);
lean_inc(x_522);
x_523 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_524 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_521, x_6, x_448, x_8, x_9, x_10, x_11, x_445);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_524, 1);
lean_inc(x_526);
lean_dec(x_524);
x_527 = lean_ctor_get(x_525, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_525, 1);
lean_inc(x_528);
lean_dec(x_525);
x_529 = lean_nat_add(x_6, x_447);
lean_dec(x_6);
x_530 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_522, x_529, x_528, x_8, x_9, x_10, x_11, x_526);
if (lean_obj_tag(x_530) == 0)
{
uint8_t x_531; 
x_531 = !lean_is_exclusive(x_530);
if (x_531 == 0)
{
lean_object* x_532; uint8_t x_533; 
x_532 = lean_ctor_get(x_530, 0);
x_533 = !lean_is_exclusive(x_532);
if (x_533 == 0)
{
lean_object* x_534; uint8_t x_535; lean_object* x_536; 
x_534 = lean_ctor_get(x_532, 0);
x_535 = (uint8_t)((x_523 << 24) >> 61);
x_536 = lean_expr_update_forall(x_5, x_535, x_527, x_534);
lean_ctor_set(x_532, 0, x_536);
return x_530;
}
else
{
lean_object* x_537; lean_object* x_538; uint8_t x_539; lean_object* x_540; lean_object* x_541; 
x_537 = lean_ctor_get(x_532, 0);
x_538 = lean_ctor_get(x_532, 1);
lean_inc(x_538);
lean_inc(x_537);
lean_dec(x_532);
x_539 = (uint8_t)((x_523 << 24) >> 61);
x_540 = lean_expr_update_forall(x_5, x_539, x_527, x_537);
x_541 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_541, 0, x_540);
lean_ctor_set(x_541, 1, x_538);
lean_ctor_set(x_530, 0, x_541);
return x_530;
}
}
else
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; uint8_t x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
x_542 = lean_ctor_get(x_530, 0);
x_543 = lean_ctor_get(x_530, 1);
lean_inc(x_543);
lean_inc(x_542);
lean_dec(x_530);
x_544 = lean_ctor_get(x_542, 0);
lean_inc(x_544);
x_545 = lean_ctor_get(x_542, 1);
lean_inc(x_545);
if (lean_is_exclusive(x_542)) {
 lean_ctor_release(x_542, 0);
 lean_ctor_release(x_542, 1);
 x_546 = x_542;
} else {
 lean_dec_ref(x_542);
 x_546 = lean_box(0);
}
x_547 = (uint8_t)((x_523 << 24) >> 61);
x_548 = lean_expr_update_forall(x_5, x_547, x_527, x_544);
if (lean_is_scalar(x_546)) {
 x_549 = lean_alloc_ctor(0, 2, 0);
} else {
 x_549 = x_546;
}
lean_ctor_set(x_549, 0, x_548);
lean_ctor_set(x_549, 1, x_545);
x_550 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_550, 0, x_549);
lean_ctor_set(x_550, 1, x_543);
return x_550;
}
}
else
{
uint8_t x_551; 
lean_dec(x_527);
lean_dec(x_5);
x_551 = !lean_is_exclusive(x_530);
if (x_551 == 0)
{
return x_530;
}
else
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_552 = lean_ctor_get(x_530, 0);
x_553 = lean_ctor_get(x_530, 1);
lean_inc(x_553);
lean_inc(x_552);
lean_dec(x_530);
x_554 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_554, 0, x_552);
lean_ctor_set(x_554, 1, x_553);
return x_554;
}
}
}
else
{
uint8_t x_555; 
lean_dec(x_522);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_555 = !lean_is_exclusive(x_524);
if (x_555 == 0)
{
return x_524;
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; 
x_556 = lean_ctor_get(x_524, 0);
x_557 = lean_ctor_get(x_524, 1);
lean_inc(x_557);
lean_inc(x_556);
lean_dec(x_524);
x_558 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_558, 0, x_556);
lean_ctor_set(x_558, 1, x_557);
return x_558;
}
}
}
case 8:
{
lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
lean_free_object(x_227);
x_559 = lean_ctor_get(x_5, 1);
lean_inc(x_559);
x_560 = lean_ctor_get(x_5, 2);
lean_inc(x_560);
x_561 = lean_ctor_get(x_5, 3);
lean_inc(x_561);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_562 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_559, x_6, x_448, x_8, x_9, x_10, x_11, x_445);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_562, 1);
lean_inc(x_564);
lean_dec(x_562);
x_565 = lean_ctor_get(x_563, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_563, 1);
lean_inc(x_566);
lean_dec(x_563);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_567 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_560, x_6, x_566, x_8, x_9, x_10, x_11, x_564);
if (lean_obj_tag(x_567) == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_568 = lean_ctor_get(x_567, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_567, 1);
lean_inc(x_569);
lean_dec(x_567);
x_570 = lean_ctor_get(x_568, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_568, 1);
lean_inc(x_571);
lean_dec(x_568);
x_572 = lean_nat_add(x_6, x_447);
lean_dec(x_6);
x_573 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_561, x_572, x_571, x_8, x_9, x_10, x_11, x_569);
if (lean_obj_tag(x_573) == 0)
{
uint8_t x_574; 
x_574 = !lean_is_exclusive(x_573);
if (x_574 == 0)
{
lean_object* x_575; uint8_t x_576; 
x_575 = lean_ctor_get(x_573, 0);
x_576 = !lean_is_exclusive(x_575);
if (x_576 == 0)
{
lean_object* x_577; lean_object* x_578; 
x_577 = lean_ctor_get(x_575, 0);
x_578 = lean_expr_update_let(x_5, x_565, x_570, x_577);
lean_ctor_set(x_575, 0, x_578);
return x_573;
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_579 = lean_ctor_get(x_575, 0);
x_580 = lean_ctor_get(x_575, 1);
lean_inc(x_580);
lean_inc(x_579);
lean_dec(x_575);
x_581 = lean_expr_update_let(x_5, x_565, x_570, x_579);
x_582 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_582, 0, x_581);
lean_ctor_set(x_582, 1, x_580);
lean_ctor_set(x_573, 0, x_582);
return x_573;
}
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; 
x_583 = lean_ctor_get(x_573, 0);
x_584 = lean_ctor_get(x_573, 1);
lean_inc(x_584);
lean_inc(x_583);
lean_dec(x_573);
x_585 = lean_ctor_get(x_583, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_583, 1);
lean_inc(x_586);
if (lean_is_exclusive(x_583)) {
 lean_ctor_release(x_583, 0);
 lean_ctor_release(x_583, 1);
 x_587 = x_583;
} else {
 lean_dec_ref(x_583);
 x_587 = lean_box(0);
}
x_588 = lean_expr_update_let(x_5, x_565, x_570, x_585);
if (lean_is_scalar(x_587)) {
 x_589 = lean_alloc_ctor(0, 2, 0);
} else {
 x_589 = x_587;
}
lean_ctor_set(x_589, 0, x_588);
lean_ctor_set(x_589, 1, x_586);
x_590 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_584);
return x_590;
}
}
else
{
uint8_t x_591; 
lean_dec(x_570);
lean_dec(x_565);
lean_dec(x_5);
x_591 = !lean_is_exclusive(x_573);
if (x_591 == 0)
{
return x_573;
}
else
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; 
x_592 = lean_ctor_get(x_573, 0);
x_593 = lean_ctor_get(x_573, 1);
lean_inc(x_593);
lean_inc(x_592);
lean_dec(x_573);
x_594 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_594, 0, x_592);
lean_ctor_set(x_594, 1, x_593);
return x_594;
}
}
}
else
{
uint8_t x_595; 
lean_dec(x_565);
lean_dec(x_561);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_595 = !lean_is_exclusive(x_567);
if (x_595 == 0)
{
return x_567;
}
else
{
lean_object* x_596; lean_object* x_597; lean_object* x_598; 
x_596 = lean_ctor_get(x_567, 0);
x_597 = lean_ctor_get(x_567, 1);
lean_inc(x_597);
lean_inc(x_596);
lean_dec(x_567);
x_598 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_598, 0, x_596);
lean_ctor_set(x_598, 1, x_597);
return x_598;
}
}
}
else
{
uint8_t x_599; 
lean_dec(x_561);
lean_dec(x_560);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_599 = !lean_is_exclusive(x_562);
if (x_599 == 0)
{
return x_562;
}
else
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; 
x_600 = lean_ctor_get(x_562, 0);
x_601 = lean_ctor_get(x_562, 1);
lean_inc(x_601);
lean_inc(x_600);
lean_dec(x_562);
x_602 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_602, 0, x_600);
lean_ctor_set(x_602, 1, x_601);
return x_602;
}
}
}
case 10:
{
lean_object* x_603; lean_object* x_604; 
lean_free_object(x_227);
x_603 = lean_ctor_get(x_5, 1);
lean_inc(x_603);
x_604 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_603, x_6, x_448, x_8, x_9, x_10, x_11, x_445);
if (lean_obj_tag(x_604) == 0)
{
uint8_t x_605; 
x_605 = !lean_is_exclusive(x_604);
if (x_605 == 0)
{
lean_object* x_606; uint8_t x_607; 
x_606 = lean_ctor_get(x_604, 0);
x_607 = !lean_is_exclusive(x_606);
if (x_607 == 0)
{
lean_object* x_608; lean_object* x_609; 
x_608 = lean_ctor_get(x_606, 0);
x_609 = lean_expr_update_mdata(x_5, x_608);
lean_ctor_set(x_606, 0, x_609);
return x_604;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_610 = lean_ctor_get(x_606, 0);
x_611 = lean_ctor_get(x_606, 1);
lean_inc(x_611);
lean_inc(x_610);
lean_dec(x_606);
x_612 = lean_expr_update_mdata(x_5, x_610);
x_613 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_613, 0, x_612);
lean_ctor_set(x_613, 1, x_611);
lean_ctor_set(x_604, 0, x_613);
return x_604;
}
}
else
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_614 = lean_ctor_get(x_604, 0);
x_615 = lean_ctor_get(x_604, 1);
lean_inc(x_615);
lean_inc(x_614);
lean_dec(x_604);
x_616 = lean_ctor_get(x_614, 0);
lean_inc(x_616);
x_617 = lean_ctor_get(x_614, 1);
lean_inc(x_617);
if (lean_is_exclusive(x_614)) {
 lean_ctor_release(x_614, 0);
 lean_ctor_release(x_614, 1);
 x_618 = x_614;
} else {
 lean_dec_ref(x_614);
 x_618 = lean_box(0);
}
x_619 = lean_expr_update_mdata(x_5, x_616);
if (lean_is_scalar(x_618)) {
 x_620 = lean_alloc_ctor(0, 2, 0);
} else {
 x_620 = x_618;
}
lean_ctor_set(x_620, 0, x_619);
lean_ctor_set(x_620, 1, x_617);
x_621 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_621, 0, x_620);
lean_ctor_set(x_621, 1, x_615);
return x_621;
}
}
else
{
uint8_t x_622; 
lean_dec(x_5);
x_622 = !lean_is_exclusive(x_604);
if (x_622 == 0)
{
return x_604;
}
else
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_623 = lean_ctor_get(x_604, 0);
x_624 = lean_ctor_get(x_604, 1);
lean_inc(x_624);
lean_inc(x_623);
lean_dec(x_604);
x_625 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_625, 0, x_623);
lean_ctor_set(x_625, 1, x_624);
return x_625;
}
}
}
case 11:
{
lean_object* x_626; lean_object* x_627; 
lean_free_object(x_227);
x_626 = lean_ctor_get(x_5, 2);
lean_inc(x_626);
x_627 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_626, x_6, x_448, x_8, x_9, x_10, x_11, x_445);
if (lean_obj_tag(x_627) == 0)
{
uint8_t x_628; 
x_628 = !lean_is_exclusive(x_627);
if (x_628 == 0)
{
lean_object* x_629; uint8_t x_630; 
x_629 = lean_ctor_get(x_627, 0);
x_630 = !lean_is_exclusive(x_629);
if (x_630 == 0)
{
lean_object* x_631; lean_object* x_632; 
x_631 = lean_ctor_get(x_629, 0);
x_632 = lean_expr_update_proj(x_5, x_631);
lean_ctor_set(x_629, 0, x_632);
return x_627;
}
else
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; 
x_633 = lean_ctor_get(x_629, 0);
x_634 = lean_ctor_get(x_629, 1);
lean_inc(x_634);
lean_inc(x_633);
lean_dec(x_629);
x_635 = lean_expr_update_proj(x_5, x_633);
x_636 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_636, 0, x_635);
lean_ctor_set(x_636, 1, x_634);
lean_ctor_set(x_627, 0, x_636);
return x_627;
}
}
else
{
lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
x_637 = lean_ctor_get(x_627, 0);
x_638 = lean_ctor_get(x_627, 1);
lean_inc(x_638);
lean_inc(x_637);
lean_dec(x_627);
x_639 = lean_ctor_get(x_637, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_637, 1);
lean_inc(x_640);
if (lean_is_exclusive(x_637)) {
 lean_ctor_release(x_637, 0);
 lean_ctor_release(x_637, 1);
 x_641 = x_637;
} else {
 lean_dec_ref(x_637);
 x_641 = lean_box(0);
}
x_642 = lean_expr_update_proj(x_5, x_639);
if (lean_is_scalar(x_641)) {
 x_643 = lean_alloc_ctor(0, 2, 0);
} else {
 x_643 = x_641;
}
lean_ctor_set(x_643, 0, x_642);
lean_ctor_set(x_643, 1, x_640);
x_644 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_644, 0, x_643);
lean_ctor_set(x_644, 1, x_638);
return x_644;
}
}
else
{
uint8_t x_645; 
lean_dec(x_5);
x_645 = !lean_is_exclusive(x_627);
if (x_645 == 0)
{
return x_627;
}
else
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; 
x_646 = lean_ctor_get(x_627, 0);
x_647 = lean_ctor_get(x_627, 1);
lean_inc(x_647);
lean_inc(x_646);
lean_dec(x_627);
x_648 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_648, 0, x_646);
lean_ctor_set(x_648, 1, x_647);
return x_648;
}
}
}
default: 
{
lean_object* x_649; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_649 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_649, 0, x_5);
lean_ctor_set(x_649, 1, x_448);
lean_ctor_set(x_227, 0, x_649);
return x_227;
}
}
}
else
{
lean_object* x_650; lean_object* x_651; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_650 = l_Lean_mkBVar(x_6);
x_651 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_651, 0, x_650);
lean_ctor_set(x_651, 1, x_448);
lean_ctor_set(x_227, 0, x_651);
return x_227;
}
}
else
{
lean_object* x_652; lean_object* x_653; lean_object* x_654; uint8_t x_655; 
x_652 = lean_ctor_get(x_227, 1);
lean_inc(x_652);
lean_dec(x_227);
x_653 = lean_unsigned_to_nat(1u);
x_654 = lean_nat_add(x_7, x_653);
x_655 = l_Lean_Occurrences_contains(x_1, x_7);
lean_dec(x_7);
if (x_655 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; 
x_656 = lean_ctor_get(x_5, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_5, 1);
lean_inc(x_657);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_658 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_656, x_6, x_654, x_8, x_9, x_10, x_11, x_652);
if (lean_obj_tag(x_658) == 0)
{
lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_659 = lean_ctor_get(x_658, 0);
lean_inc(x_659);
x_660 = lean_ctor_get(x_658, 1);
lean_inc(x_660);
lean_dec(x_658);
x_661 = lean_ctor_get(x_659, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_659, 1);
lean_inc(x_662);
lean_dec(x_659);
x_663 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_657, x_6, x_662, x_8, x_9, x_10, x_11, x_660);
if (lean_obj_tag(x_663) == 0)
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_664 = lean_ctor_get(x_663, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_663, 1);
lean_inc(x_665);
if (lean_is_exclusive(x_663)) {
 lean_ctor_release(x_663, 0);
 lean_ctor_release(x_663, 1);
 x_666 = x_663;
} else {
 lean_dec_ref(x_663);
 x_666 = lean_box(0);
}
x_667 = lean_ctor_get(x_664, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_664, 1);
lean_inc(x_668);
if (lean_is_exclusive(x_664)) {
 lean_ctor_release(x_664, 0);
 lean_ctor_release(x_664, 1);
 x_669 = x_664;
} else {
 lean_dec_ref(x_664);
 x_669 = lean_box(0);
}
x_670 = lean_expr_update_app(x_5, x_661, x_667);
if (lean_is_scalar(x_669)) {
 x_671 = lean_alloc_ctor(0, 2, 0);
} else {
 x_671 = x_669;
}
lean_ctor_set(x_671, 0, x_670);
lean_ctor_set(x_671, 1, x_668);
if (lean_is_scalar(x_666)) {
 x_672 = lean_alloc_ctor(0, 2, 0);
} else {
 x_672 = x_666;
}
lean_ctor_set(x_672, 0, x_671);
lean_ctor_set(x_672, 1, x_665);
return x_672;
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; 
lean_dec(x_661);
lean_dec(x_5);
x_673 = lean_ctor_get(x_663, 0);
lean_inc(x_673);
x_674 = lean_ctor_get(x_663, 1);
lean_inc(x_674);
if (lean_is_exclusive(x_663)) {
 lean_ctor_release(x_663, 0);
 lean_ctor_release(x_663, 1);
 x_675 = x_663;
} else {
 lean_dec_ref(x_663);
 x_675 = lean_box(0);
}
if (lean_is_scalar(x_675)) {
 x_676 = lean_alloc_ctor(1, 2, 0);
} else {
 x_676 = x_675;
}
lean_ctor_set(x_676, 0, x_673);
lean_ctor_set(x_676, 1, x_674);
return x_676;
}
}
else
{
lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; 
lean_dec(x_657);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_677 = lean_ctor_get(x_658, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_658, 1);
lean_inc(x_678);
if (lean_is_exclusive(x_658)) {
 lean_ctor_release(x_658, 0);
 lean_ctor_release(x_658, 1);
 x_679 = x_658;
} else {
 lean_dec_ref(x_658);
 x_679 = lean_box(0);
}
if (lean_is_scalar(x_679)) {
 x_680 = lean_alloc_ctor(1, 2, 0);
} else {
 x_680 = x_679;
}
lean_ctor_set(x_680, 0, x_677);
lean_ctor_set(x_680, 1, x_678);
return x_680;
}
}
case 6:
{
lean_object* x_681; lean_object* x_682; uint64_t x_683; lean_object* x_684; 
x_681 = lean_ctor_get(x_5, 1);
lean_inc(x_681);
x_682 = lean_ctor_get(x_5, 2);
lean_inc(x_682);
x_683 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_684 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_681, x_6, x_654, x_8, x_9, x_10, x_11, x_652);
if (lean_obj_tag(x_684) == 0)
{
lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; 
x_685 = lean_ctor_get(x_684, 0);
lean_inc(x_685);
x_686 = lean_ctor_get(x_684, 1);
lean_inc(x_686);
lean_dec(x_684);
x_687 = lean_ctor_get(x_685, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_685, 1);
lean_inc(x_688);
lean_dec(x_685);
x_689 = lean_nat_add(x_6, x_653);
lean_dec(x_6);
x_690 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_682, x_689, x_688, x_8, x_9, x_10, x_11, x_686);
if (lean_obj_tag(x_690) == 0)
{
lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; uint8_t x_697; lean_object* x_698; lean_object* x_699; lean_object* x_700; 
x_691 = lean_ctor_get(x_690, 0);
lean_inc(x_691);
x_692 = lean_ctor_get(x_690, 1);
lean_inc(x_692);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 x_693 = x_690;
} else {
 lean_dec_ref(x_690);
 x_693 = lean_box(0);
}
x_694 = lean_ctor_get(x_691, 0);
lean_inc(x_694);
x_695 = lean_ctor_get(x_691, 1);
lean_inc(x_695);
if (lean_is_exclusive(x_691)) {
 lean_ctor_release(x_691, 0);
 lean_ctor_release(x_691, 1);
 x_696 = x_691;
} else {
 lean_dec_ref(x_691);
 x_696 = lean_box(0);
}
x_697 = (uint8_t)((x_683 << 24) >> 61);
x_698 = lean_expr_update_lambda(x_5, x_697, x_687, x_694);
if (lean_is_scalar(x_696)) {
 x_699 = lean_alloc_ctor(0, 2, 0);
} else {
 x_699 = x_696;
}
lean_ctor_set(x_699, 0, x_698);
lean_ctor_set(x_699, 1, x_695);
if (lean_is_scalar(x_693)) {
 x_700 = lean_alloc_ctor(0, 2, 0);
} else {
 x_700 = x_693;
}
lean_ctor_set(x_700, 0, x_699);
lean_ctor_set(x_700, 1, x_692);
return x_700;
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
lean_dec(x_687);
lean_dec(x_5);
x_701 = lean_ctor_get(x_690, 0);
lean_inc(x_701);
x_702 = lean_ctor_get(x_690, 1);
lean_inc(x_702);
if (lean_is_exclusive(x_690)) {
 lean_ctor_release(x_690, 0);
 lean_ctor_release(x_690, 1);
 x_703 = x_690;
} else {
 lean_dec_ref(x_690);
 x_703 = lean_box(0);
}
if (lean_is_scalar(x_703)) {
 x_704 = lean_alloc_ctor(1, 2, 0);
} else {
 x_704 = x_703;
}
lean_ctor_set(x_704, 0, x_701);
lean_ctor_set(x_704, 1, x_702);
return x_704;
}
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; 
lean_dec(x_682);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_705 = lean_ctor_get(x_684, 0);
lean_inc(x_705);
x_706 = lean_ctor_get(x_684, 1);
lean_inc(x_706);
if (lean_is_exclusive(x_684)) {
 lean_ctor_release(x_684, 0);
 lean_ctor_release(x_684, 1);
 x_707 = x_684;
} else {
 lean_dec_ref(x_684);
 x_707 = lean_box(0);
}
if (lean_is_scalar(x_707)) {
 x_708 = lean_alloc_ctor(1, 2, 0);
} else {
 x_708 = x_707;
}
lean_ctor_set(x_708, 0, x_705);
lean_ctor_set(x_708, 1, x_706);
return x_708;
}
}
case 7:
{
lean_object* x_709; lean_object* x_710; uint64_t x_711; lean_object* x_712; 
x_709 = lean_ctor_get(x_5, 1);
lean_inc(x_709);
x_710 = lean_ctor_get(x_5, 2);
lean_inc(x_710);
x_711 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_712 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_709, x_6, x_654, x_8, x_9, x_10, x_11, x_652);
if (lean_obj_tag(x_712) == 0)
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; 
x_713 = lean_ctor_get(x_712, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_712, 1);
lean_inc(x_714);
lean_dec(x_712);
x_715 = lean_ctor_get(x_713, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_713, 1);
lean_inc(x_716);
lean_dec(x_713);
x_717 = lean_nat_add(x_6, x_653);
lean_dec(x_6);
x_718 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_710, x_717, x_716, x_8, x_9, x_10, x_11, x_714);
if (lean_obj_tag(x_718) == 0)
{
lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; uint8_t x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_719 = lean_ctor_get(x_718, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_718, 1);
lean_inc(x_720);
if (lean_is_exclusive(x_718)) {
 lean_ctor_release(x_718, 0);
 lean_ctor_release(x_718, 1);
 x_721 = x_718;
} else {
 lean_dec_ref(x_718);
 x_721 = lean_box(0);
}
x_722 = lean_ctor_get(x_719, 0);
lean_inc(x_722);
x_723 = lean_ctor_get(x_719, 1);
lean_inc(x_723);
if (lean_is_exclusive(x_719)) {
 lean_ctor_release(x_719, 0);
 lean_ctor_release(x_719, 1);
 x_724 = x_719;
} else {
 lean_dec_ref(x_719);
 x_724 = lean_box(0);
}
x_725 = (uint8_t)((x_711 << 24) >> 61);
x_726 = lean_expr_update_forall(x_5, x_725, x_715, x_722);
if (lean_is_scalar(x_724)) {
 x_727 = lean_alloc_ctor(0, 2, 0);
} else {
 x_727 = x_724;
}
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_723);
if (lean_is_scalar(x_721)) {
 x_728 = lean_alloc_ctor(0, 2, 0);
} else {
 x_728 = x_721;
}
lean_ctor_set(x_728, 0, x_727);
lean_ctor_set(x_728, 1, x_720);
return x_728;
}
else
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
lean_dec(x_715);
lean_dec(x_5);
x_729 = lean_ctor_get(x_718, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_718, 1);
lean_inc(x_730);
if (lean_is_exclusive(x_718)) {
 lean_ctor_release(x_718, 0);
 lean_ctor_release(x_718, 1);
 x_731 = x_718;
} else {
 lean_dec_ref(x_718);
 x_731 = lean_box(0);
}
if (lean_is_scalar(x_731)) {
 x_732 = lean_alloc_ctor(1, 2, 0);
} else {
 x_732 = x_731;
}
lean_ctor_set(x_732, 0, x_729);
lean_ctor_set(x_732, 1, x_730);
return x_732;
}
}
else
{
lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
lean_dec(x_710);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_733 = lean_ctor_get(x_712, 0);
lean_inc(x_733);
x_734 = lean_ctor_get(x_712, 1);
lean_inc(x_734);
if (lean_is_exclusive(x_712)) {
 lean_ctor_release(x_712, 0);
 lean_ctor_release(x_712, 1);
 x_735 = x_712;
} else {
 lean_dec_ref(x_712);
 x_735 = lean_box(0);
}
if (lean_is_scalar(x_735)) {
 x_736 = lean_alloc_ctor(1, 2, 0);
} else {
 x_736 = x_735;
}
lean_ctor_set(x_736, 0, x_733);
lean_ctor_set(x_736, 1, x_734);
return x_736;
}
}
case 8:
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
x_737 = lean_ctor_get(x_5, 1);
lean_inc(x_737);
x_738 = lean_ctor_get(x_5, 2);
lean_inc(x_738);
x_739 = lean_ctor_get(x_5, 3);
lean_inc(x_739);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_740 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_737, x_6, x_654, x_8, x_9, x_10, x_11, x_652);
if (lean_obj_tag(x_740) == 0)
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_741 = lean_ctor_get(x_740, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_740, 1);
lean_inc(x_742);
lean_dec(x_740);
x_743 = lean_ctor_get(x_741, 0);
lean_inc(x_743);
x_744 = lean_ctor_get(x_741, 1);
lean_inc(x_744);
lean_dec(x_741);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_745 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_738, x_6, x_744, x_8, x_9, x_10, x_11, x_742);
if (lean_obj_tag(x_745) == 0)
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; 
x_746 = lean_ctor_get(x_745, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_745, 1);
lean_inc(x_747);
lean_dec(x_745);
x_748 = lean_ctor_get(x_746, 0);
lean_inc(x_748);
x_749 = lean_ctor_get(x_746, 1);
lean_inc(x_749);
lean_dec(x_746);
x_750 = lean_nat_add(x_6, x_653);
lean_dec(x_6);
x_751 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_739, x_750, x_749, x_8, x_9, x_10, x_11, x_747);
if (lean_obj_tag(x_751) == 0)
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; 
x_752 = lean_ctor_get(x_751, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_751, 1);
lean_inc(x_753);
if (lean_is_exclusive(x_751)) {
 lean_ctor_release(x_751, 0);
 lean_ctor_release(x_751, 1);
 x_754 = x_751;
} else {
 lean_dec_ref(x_751);
 x_754 = lean_box(0);
}
x_755 = lean_ctor_get(x_752, 0);
lean_inc(x_755);
x_756 = lean_ctor_get(x_752, 1);
lean_inc(x_756);
if (lean_is_exclusive(x_752)) {
 lean_ctor_release(x_752, 0);
 lean_ctor_release(x_752, 1);
 x_757 = x_752;
} else {
 lean_dec_ref(x_752);
 x_757 = lean_box(0);
}
x_758 = lean_expr_update_let(x_5, x_743, x_748, x_755);
if (lean_is_scalar(x_757)) {
 x_759 = lean_alloc_ctor(0, 2, 0);
} else {
 x_759 = x_757;
}
lean_ctor_set(x_759, 0, x_758);
lean_ctor_set(x_759, 1, x_756);
if (lean_is_scalar(x_754)) {
 x_760 = lean_alloc_ctor(0, 2, 0);
} else {
 x_760 = x_754;
}
lean_ctor_set(x_760, 0, x_759);
lean_ctor_set(x_760, 1, x_753);
return x_760;
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; 
lean_dec(x_748);
lean_dec(x_743);
lean_dec(x_5);
x_761 = lean_ctor_get(x_751, 0);
lean_inc(x_761);
x_762 = lean_ctor_get(x_751, 1);
lean_inc(x_762);
if (lean_is_exclusive(x_751)) {
 lean_ctor_release(x_751, 0);
 lean_ctor_release(x_751, 1);
 x_763 = x_751;
} else {
 lean_dec_ref(x_751);
 x_763 = lean_box(0);
}
if (lean_is_scalar(x_763)) {
 x_764 = lean_alloc_ctor(1, 2, 0);
} else {
 x_764 = x_763;
}
lean_ctor_set(x_764, 0, x_761);
lean_ctor_set(x_764, 1, x_762);
return x_764;
}
}
else
{
lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; 
lean_dec(x_743);
lean_dec(x_739);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_765 = lean_ctor_get(x_745, 0);
lean_inc(x_765);
x_766 = lean_ctor_get(x_745, 1);
lean_inc(x_766);
if (lean_is_exclusive(x_745)) {
 lean_ctor_release(x_745, 0);
 lean_ctor_release(x_745, 1);
 x_767 = x_745;
} else {
 lean_dec_ref(x_745);
 x_767 = lean_box(0);
}
if (lean_is_scalar(x_767)) {
 x_768 = lean_alloc_ctor(1, 2, 0);
} else {
 x_768 = x_767;
}
lean_ctor_set(x_768, 0, x_765);
lean_ctor_set(x_768, 1, x_766);
return x_768;
}
}
else
{
lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; 
lean_dec(x_739);
lean_dec(x_738);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_769 = lean_ctor_get(x_740, 0);
lean_inc(x_769);
x_770 = lean_ctor_get(x_740, 1);
lean_inc(x_770);
if (lean_is_exclusive(x_740)) {
 lean_ctor_release(x_740, 0);
 lean_ctor_release(x_740, 1);
 x_771 = x_740;
} else {
 lean_dec_ref(x_740);
 x_771 = lean_box(0);
}
if (lean_is_scalar(x_771)) {
 x_772 = lean_alloc_ctor(1, 2, 0);
} else {
 x_772 = x_771;
}
lean_ctor_set(x_772, 0, x_769);
lean_ctor_set(x_772, 1, x_770);
return x_772;
}
}
case 10:
{
lean_object* x_773; lean_object* x_774; 
x_773 = lean_ctor_get(x_5, 1);
lean_inc(x_773);
x_774 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_773, x_6, x_654, x_8, x_9, x_10, x_11, x_652);
if (lean_obj_tag(x_774) == 0)
{
lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; 
x_775 = lean_ctor_get(x_774, 0);
lean_inc(x_775);
x_776 = lean_ctor_get(x_774, 1);
lean_inc(x_776);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 lean_ctor_release(x_774, 1);
 x_777 = x_774;
} else {
 lean_dec_ref(x_774);
 x_777 = lean_box(0);
}
x_778 = lean_ctor_get(x_775, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_775, 1);
lean_inc(x_779);
if (lean_is_exclusive(x_775)) {
 lean_ctor_release(x_775, 0);
 lean_ctor_release(x_775, 1);
 x_780 = x_775;
} else {
 lean_dec_ref(x_775);
 x_780 = lean_box(0);
}
x_781 = lean_expr_update_mdata(x_5, x_778);
if (lean_is_scalar(x_780)) {
 x_782 = lean_alloc_ctor(0, 2, 0);
} else {
 x_782 = x_780;
}
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_779);
if (lean_is_scalar(x_777)) {
 x_783 = lean_alloc_ctor(0, 2, 0);
} else {
 x_783 = x_777;
}
lean_ctor_set(x_783, 0, x_782);
lean_ctor_set(x_783, 1, x_776);
return x_783;
}
else
{
lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; 
lean_dec(x_5);
x_784 = lean_ctor_get(x_774, 0);
lean_inc(x_784);
x_785 = lean_ctor_get(x_774, 1);
lean_inc(x_785);
if (lean_is_exclusive(x_774)) {
 lean_ctor_release(x_774, 0);
 lean_ctor_release(x_774, 1);
 x_786 = x_774;
} else {
 lean_dec_ref(x_774);
 x_786 = lean_box(0);
}
if (lean_is_scalar(x_786)) {
 x_787 = lean_alloc_ctor(1, 2, 0);
} else {
 x_787 = x_786;
}
lean_ctor_set(x_787, 0, x_784);
lean_ctor_set(x_787, 1, x_785);
return x_787;
}
}
case 11:
{
lean_object* x_788; lean_object* x_789; 
x_788 = lean_ctor_get(x_5, 2);
lean_inc(x_788);
x_789 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_788, x_6, x_654, x_8, x_9, x_10, x_11, x_652);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; 
x_790 = lean_ctor_get(x_789, 0);
lean_inc(x_790);
x_791 = lean_ctor_get(x_789, 1);
lean_inc(x_791);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 lean_ctor_release(x_789, 1);
 x_792 = x_789;
} else {
 lean_dec_ref(x_789);
 x_792 = lean_box(0);
}
x_793 = lean_ctor_get(x_790, 0);
lean_inc(x_793);
x_794 = lean_ctor_get(x_790, 1);
lean_inc(x_794);
if (lean_is_exclusive(x_790)) {
 lean_ctor_release(x_790, 0);
 lean_ctor_release(x_790, 1);
 x_795 = x_790;
} else {
 lean_dec_ref(x_790);
 x_795 = lean_box(0);
}
x_796 = lean_expr_update_proj(x_5, x_793);
if (lean_is_scalar(x_795)) {
 x_797 = lean_alloc_ctor(0, 2, 0);
} else {
 x_797 = x_795;
}
lean_ctor_set(x_797, 0, x_796);
lean_ctor_set(x_797, 1, x_794);
if (lean_is_scalar(x_792)) {
 x_798 = lean_alloc_ctor(0, 2, 0);
} else {
 x_798 = x_792;
}
lean_ctor_set(x_798, 0, x_797);
lean_ctor_set(x_798, 1, x_791);
return x_798;
}
else
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; 
lean_dec(x_5);
x_799 = lean_ctor_get(x_789, 0);
lean_inc(x_799);
x_800 = lean_ctor_get(x_789, 1);
lean_inc(x_800);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 lean_ctor_release(x_789, 1);
 x_801 = x_789;
} else {
 lean_dec_ref(x_789);
 x_801 = lean_box(0);
}
if (lean_is_scalar(x_801)) {
 x_802 = lean_alloc_ctor(1, 2, 0);
} else {
 x_802 = x_801;
}
lean_ctor_set(x_802, 0, x_799);
lean_ctor_set(x_802, 1, x_800);
return x_802;
}
}
default: 
{
lean_object* x_803; lean_object* x_804; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_803 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_803, 0, x_5);
lean_ctor_set(x_803, 1, x_654);
x_804 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_804, 0, x_803);
lean_ctor_set(x_804, 1, x_652);
return x_804;
}
}
}
else
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_805 = l_Lean_mkBVar(x_6);
x_806 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_806, 0, x_805);
lean_ctor_set(x_806, 1, x_654);
x_807 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_807, 0, x_806);
lean_ctor_set(x_807, 1, x_652);
return x_807;
}
}
}
}
else
{
uint8_t x_808; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_808 = !lean_is_exclusive(x_227);
if (x_808 == 0)
{
return x_227;
}
else
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_809 = lean_ctor_get(x_227, 0);
x_810 = lean_ctor_get(x_227, 1);
lean_inc(x_810);
lean_inc(x_809);
lean_dec(x_227);
x_811 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_811, 0, x_809);
lean_ctor_set(x_811, 1, x_810);
return x_811;
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
lean_object* x_812; lean_object* x_813; lean_object* x_814; 
x_812 = lean_ctor_get(x_5, 0);
lean_inc(x_812);
x_813 = lean_ctor_get(x_5, 1);
lean_inc(x_813);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_814 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_812, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_814) == 0)
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_815 = lean_ctor_get(x_814, 0);
lean_inc(x_815);
x_816 = lean_ctor_get(x_814, 1);
lean_inc(x_816);
lean_dec(x_814);
x_817 = lean_ctor_get(x_815, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_815, 1);
lean_inc(x_818);
lean_dec(x_815);
x_819 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_813, x_6, x_818, x_8, x_9, x_10, x_11, x_816);
if (lean_obj_tag(x_819) == 0)
{
uint8_t x_820; 
x_820 = !lean_is_exclusive(x_819);
if (x_820 == 0)
{
lean_object* x_821; uint8_t x_822; 
x_821 = lean_ctor_get(x_819, 0);
x_822 = !lean_is_exclusive(x_821);
if (x_822 == 0)
{
lean_object* x_823; lean_object* x_824; 
x_823 = lean_ctor_get(x_821, 0);
x_824 = lean_expr_update_app(x_5, x_817, x_823);
lean_ctor_set(x_821, 0, x_824);
return x_819;
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
x_825 = lean_ctor_get(x_821, 0);
x_826 = lean_ctor_get(x_821, 1);
lean_inc(x_826);
lean_inc(x_825);
lean_dec(x_821);
x_827 = lean_expr_update_app(x_5, x_817, x_825);
x_828 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_828, 0, x_827);
lean_ctor_set(x_828, 1, x_826);
lean_ctor_set(x_819, 0, x_828);
return x_819;
}
}
else
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; 
x_829 = lean_ctor_get(x_819, 0);
x_830 = lean_ctor_get(x_819, 1);
lean_inc(x_830);
lean_inc(x_829);
lean_dec(x_819);
x_831 = lean_ctor_get(x_829, 0);
lean_inc(x_831);
x_832 = lean_ctor_get(x_829, 1);
lean_inc(x_832);
if (lean_is_exclusive(x_829)) {
 lean_ctor_release(x_829, 0);
 lean_ctor_release(x_829, 1);
 x_833 = x_829;
} else {
 lean_dec_ref(x_829);
 x_833 = lean_box(0);
}
x_834 = lean_expr_update_app(x_5, x_817, x_831);
if (lean_is_scalar(x_833)) {
 x_835 = lean_alloc_ctor(0, 2, 0);
} else {
 x_835 = x_833;
}
lean_ctor_set(x_835, 0, x_834);
lean_ctor_set(x_835, 1, x_832);
x_836 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_836, 0, x_835);
lean_ctor_set(x_836, 1, x_830);
return x_836;
}
}
else
{
uint8_t x_837; 
lean_dec(x_817);
lean_dec(x_5);
x_837 = !lean_is_exclusive(x_819);
if (x_837 == 0)
{
return x_819;
}
else
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; 
x_838 = lean_ctor_get(x_819, 0);
x_839 = lean_ctor_get(x_819, 1);
lean_inc(x_839);
lean_inc(x_838);
lean_dec(x_819);
x_840 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_840, 0, x_838);
lean_ctor_set(x_840, 1, x_839);
return x_840;
}
}
}
else
{
uint8_t x_841; 
lean_dec(x_813);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_841 = !lean_is_exclusive(x_814);
if (x_841 == 0)
{
return x_814;
}
else
{
lean_object* x_842; lean_object* x_843; lean_object* x_844; 
x_842 = lean_ctor_get(x_814, 0);
x_843 = lean_ctor_get(x_814, 1);
lean_inc(x_843);
lean_inc(x_842);
lean_dec(x_814);
x_844 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_844, 0, x_842);
lean_ctor_set(x_844, 1, x_843);
return x_844;
}
}
}
case 6:
{
lean_object* x_845; lean_object* x_846; uint64_t x_847; lean_object* x_848; 
x_845 = lean_ctor_get(x_5, 1);
lean_inc(x_845);
x_846 = lean_ctor_get(x_5, 2);
lean_inc(x_846);
x_847 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_848 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_845, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_848) == 0)
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; 
x_849 = lean_ctor_get(x_848, 0);
lean_inc(x_849);
x_850 = lean_ctor_get(x_848, 1);
lean_inc(x_850);
lean_dec(x_848);
x_851 = lean_ctor_get(x_849, 0);
lean_inc(x_851);
x_852 = lean_ctor_get(x_849, 1);
lean_inc(x_852);
lean_dec(x_849);
x_853 = lean_unsigned_to_nat(1u);
x_854 = lean_nat_add(x_6, x_853);
lean_dec(x_6);
x_855 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_846, x_854, x_852, x_8, x_9, x_10, x_11, x_850);
if (lean_obj_tag(x_855) == 0)
{
uint8_t x_856; 
x_856 = !lean_is_exclusive(x_855);
if (x_856 == 0)
{
lean_object* x_857; uint8_t x_858; 
x_857 = lean_ctor_get(x_855, 0);
x_858 = !lean_is_exclusive(x_857);
if (x_858 == 0)
{
lean_object* x_859; uint8_t x_860; lean_object* x_861; 
x_859 = lean_ctor_get(x_857, 0);
x_860 = (uint8_t)((x_847 << 24) >> 61);
x_861 = lean_expr_update_lambda(x_5, x_860, x_851, x_859);
lean_ctor_set(x_857, 0, x_861);
return x_855;
}
else
{
lean_object* x_862; lean_object* x_863; uint8_t x_864; lean_object* x_865; lean_object* x_866; 
x_862 = lean_ctor_get(x_857, 0);
x_863 = lean_ctor_get(x_857, 1);
lean_inc(x_863);
lean_inc(x_862);
lean_dec(x_857);
x_864 = (uint8_t)((x_847 << 24) >> 61);
x_865 = lean_expr_update_lambda(x_5, x_864, x_851, x_862);
x_866 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_866, 0, x_865);
lean_ctor_set(x_866, 1, x_863);
lean_ctor_set(x_855, 0, x_866);
return x_855;
}
}
else
{
lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; uint8_t x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
x_867 = lean_ctor_get(x_855, 0);
x_868 = lean_ctor_get(x_855, 1);
lean_inc(x_868);
lean_inc(x_867);
lean_dec(x_855);
x_869 = lean_ctor_get(x_867, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_867, 1);
lean_inc(x_870);
if (lean_is_exclusive(x_867)) {
 lean_ctor_release(x_867, 0);
 lean_ctor_release(x_867, 1);
 x_871 = x_867;
} else {
 lean_dec_ref(x_867);
 x_871 = lean_box(0);
}
x_872 = (uint8_t)((x_847 << 24) >> 61);
x_873 = lean_expr_update_lambda(x_5, x_872, x_851, x_869);
if (lean_is_scalar(x_871)) {
 x_874 = lean_alloc_ctor(0, 2, 0);
} else {
 x_874 = x_871;
}
lean_ctor_set(x_874, 0, x_873);
lean_ctor_set(x_874, 1, x_870);
x_875 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_875, 0, x_874);
lean_ctor_set(x_875, 1, x_868);
return x_875;
}
}
else
{
uint8_t x_876; 
lean_dec(x_851);
lean_dec(x_5);
x_876 = !lean_is_exclusive(x_855);
if (x_876 == 0)
{
return x_855;
}
else
{
lean_object* x_877; lean_object* x_878; lean_object* x_879; 
x_877 = lean_ctor_get(x_855, 0);
x_878 = lean_ctor_get(x_855, 1);
lean_inc(x_878);
lean_inc(x_877);
lean_dec(x_855);
x_879 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_879, 0, x_877);
lean_ctor_set(x_879, 1, x_878);
return x_879;
}
}
}
else
{
uint8_t x_880; 
lean_dec(x_846);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_880 = !lean_is_exclusive(x_848);
if (x_880 == 0)
{
return x_848;
}
else
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_881 = lean_ctor_get(x_848, 0);
x_882 = lean_ctor_get(x_848, 1);
lean_inc(x_882);
lean_inc(x_881);
lean_dec(x_848);
x_883 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_883, 0, x_881);
lean_ctor_set(x_883, 1, x_882);
return x_883;
}
}
}
case 7:
{
lean_object* x_884; lean_object* x_885; uint64_t x_886; lean_object* x_887; 
x_884 = lean_ctor_get(x_5, 1);
lean_inc(x_884);
x_885 = lean_ctor_get(x_5, 2);
lean_inc(x_885);
x_886 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_887 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_884, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_887) == 0)
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_888 = lean_ctor_get(x_887, 0);
lean_inc(x_888);
x_889 = lean_ctor_get(x_887, 1);
lean_inc(x_889);
lean_dec(x_887);
x_890 = lean_ctor_get(x_888, 0);
lean_inc(x_890);
x_891 = lean_ctor_get(x_888, 1);
lean_inc(x_891);
lean_dec(x_888);
x_892 = lean_unsigned_to_nat(1u);
x_893 = lean_nat_add(x_6, x_892);
lean_dec(x_6);
x_894 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_885, x_893, x_891, x_8, x_9, x_10, x_11, x_889);
if (lean_obj_tag(x_894) == 0)
{
uint8_t x_895; 
x_895 = !lean_is_exclusive(x_894);
if (x_895 == 0)
{
lean_object* x_896; uint8_t x_897; 
x_896 = lean_ctor_get(x_894, 0);
x_897 = !lean_is_exclusive(x_896);
if (x_897 == 0)
{
lean_object* x_898; uint8_t x_899; lean_object* x_900; 
x_898 = lean_ctor_get(x_896, 0);
x_899 = (uint8_t)((x_886 << 24) >> 61);
x_900 = lean_expr_update_forall(x_5, x_899, x_890, x_898);
lean_ctor_set(x_896, 0, x_900);
return x_894;
}
else
{
lean_object* x_901; lean_object* x_902; uint8_t x_903; lean_object* x_904; lean_object* x_905; 
x_901 = lean_ctor_get(x_896, 0);
x_902 = lean_ctor_get(x_896, 1);
lean_inc(x_902);
lean_inc(x_901);
lean_dec(x_896);
x_903 = (uint8_t)((x_886 << 24) >> 61);
x_904 = lean_expr_update_forall(x_5, x_903, x_890, x_901);
x_905 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_905, 0, x_904);
lean_ctor_set(x_905, 1, x_902);
lean_ctor_set(x_894, 0, x_905);
return x_894;
}
}
else
{
lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; uint8_t x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; 
x_906 = lean_ctor_get(x_894, 0);
x_907 = lean_ctor_get(x_894, 1);
lean_inc(x_907);
lean_inc(x_906);
lean_dec(x_894);
x_908 = lean_ctor_get(x_906, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_906, 1);
lean_inc(x_909);
if (lean_is_exclusive(x_906)) {
 lean_ctor_release(x_906, 0);
 lean_ctor_release(x_906, 1);
 x_910 = x_906;
} else {
 lean_dec_ref(x_906);
 x_910 = lean_box(0);
}
x_911 = (uint8_t)((x_886 << 24) >> 61);
x_912 = lean_expr_update_forall(x_5, x_911, x_890, x_908);
if (lean_is_scalar(x_910)) {
 x_913 = lean_alloc_ctor(0, 2, 0);
} else {
 x_913 = x_910;
}
lean_ctor_set(x_913, 0, x_912);
lean_ctor_set(x_913, 1, x_909);
x_914 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_914, 0, x_913);
lean_ctor_set(x_914, 1, x_907);
return x_914;
}
}
else
{
uint8_t x_915; 
lean_dec(x_890);
lean_dec(x_5);
x_915 = !lean_is_exclusive(x_894);
if (x_915 == 0)
{
return x_894;
}
else
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; 
x_916 = lean_ctor_get(x_894, 0);
x_917 = lean_ctor_get(x_894, 1);
lean_inc(x_917);
lean_inc(x_916);
lean_dec(x_894);
x_918 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_918, 0, x_916);
lean_ctor_set(x_918, 1, x_917);
return x_918;
}
}
}
else
{
uint8_t x_919; 
lean_dec(x_885);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_919 = !lean_is_exclusive(x_887);
if (x_919 == 0)
{
return x_887;
}
else
{
lean_object* x_920; lean_object* x_921; lean_object* x_922; 
x_920 = lean_ctor_get(x_887, 0);
x_921 = lean_ctor_get(x_887, 1);
lean_inc(x_921);
lean_inc(x_920);
lean_dec(x_887);
x_922 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_922, 0, x_920);
lean_ctor_set(x_922, 1, x_921);
return x_922;
}
}
}
case 8:
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; 
x_923 = lean_ctor_get(x_5, 1);
lean_inc(x_923);
x_924 = lean_ctor_get(x_5, 2);
lean_inc(x_924);
x_925 = lean_ctor_get(x_5, 3);
lean_inc(x_925);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_926 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_923, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_926) == 0)
{
lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; 
x_927 = lean_ctor_get(x_926, 0);
lean_inc(x_927);
x_928 = lean_ctor_get(x_926, 1);
lean_inc(x_928);
lean_dec(x_926);
x_929 = lean_ctor_get(x_927, 0);
lean_inc(x_929);
x_930 = lean_ctor_get(x_927, 1);
lean_inc(x_930);
lean_dec(x_927);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_931 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_924, x_6, x_930, x_8, x_9, x_10, x_11, x_928);
if (lean_obj_tag(x_931) == 0)
{
lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
x_932 = lean_ctor_get(x_931, 0);
lean_inc(x_932);
x_933 = lean_ctor_get(x_931, 1);
lean_inc(x_933);
lean_dec(x_931);
x_934 = lean_ctor_get(x_932, 0);
lean_inc(x_934);
x_935 = lean_ctor_get(x_932, 1);
lean_inc(x_935);
lean_dec(x_932);
x_936 = lean_unsigned_to_nat(1u);
x_937 = lean_nat_add(x_6, x_936);
lean_dec(x_6);
x_938 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_925, x_937, x_935, x_8, x_9, x_10, x_11, x_933);
if (lean_obj_tag(x_938) == 0)
{
uint8_t x_939; 
x_939 = !lean_is_exclusive(x_938);
if (x_939 == 0)
{
lean_object* x_940; uint8_t x_941; 
x_940 = lean_ctor_get(x_938, 0);
x_941 = !lean_is_exclusive(x_940);
if (x_941 == 0)
{
lean_object* x_942; lean_object* x_943; 
x_942 = lean_ctor_get(x_940, 0);
x_943 = lean_expr_update_let(x_5, x_929, x_934, x_942);
lean_ctor_set(x_940, 0, x_943);
return x_938;
}
else
{
lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; 
x_944 = lean_ctor_get(x_940, 0);
x_945 = lean_ctor_get(x_940, 1);
lean_inc(x_945);
lean_inc(x_944);
lean_dec(x_940);
x_946 = lean_expr_update_let(x_5, x_929, x_934, x_944);
x_947 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_947, 0, x_946);
lean_ctor_set(x_947, 1, x_945);
lean_ctor_set(x_938, 0, x_947);
return x_938;
}
}
else
{
lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; lean_object* x_955; 
x_948 = lean_ctor_get(x_938, 0);
x_949 = lean_ctor_get(x_938, 1);
lean_inc(x_949);
lean_inc(x_948);
lean_dec(x_938);
x_950 = lean_ctor_get(x_948, 0);
lean_inc(x_950);
x_951 = lean_ctor_get(x_948, 1);
lean_inc(x_951);
if (lean_is_exclusive(x_948)) {
 lean_ctor_release(x_948, 0);
 lean_ctor_release(x_948, 1);
 x_952 = x_948;
} else {
 lean_dec_ref(x_948);
 x_952 = lean_box(0);
}
x_953 = lean_expr_update_let(x_5, x_929, x_934, x_950);
if (lean_is_scalar(x_952)) {
 x_954 = lean_alloc_ctor(0, 2, 0);
} else {
 x_954 = x_952;
}
lean_ctor_set(x_954, 0, x_953);
lean_ctor_set(x_954, 1, x_951);
x_955 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_955, 0, x_954);
lean_ctor_set(x_955, 1, x_949);
return x_955;
}
}
else
{
uint8_t x_956; 
lean_dec(x_934);
lean_dec(x_929);
lean_dec(x_5);
x_956 = !lean_is_exclusive(x_938);
if (x_956 == 0)
{
return x_938;
}
else
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; 
x_957 = lean_ctor_get(x_938, 0);
x_958 = lean_ctor_get(x_938, 1);
lean_inc(x_958);
lean_inc(x_957);
lean_dec(x_938);
x_959 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_959, 0, x_957);
lean_ctor_set(x_959, 1, x_958);
return x_959;
}
}
}
else
{
uint8_t x_960; 
lean_dec(x_929);
lean_dec(x_925);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_960 = !lean_is_exclusive(x_931);
if (x_960 == 0)
{
return x_931;
}
else
{
lean_object* x_961; lean_object* x_962; lean_object* x_963; 
x_961 = lean_ctor_get(x_931, 0);
x_962 = lean_ctor_get(x_931, 1);
lean_inc(x_962);
lean_inc(x_961);
lean_dec(x_931);
x_963 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_963, 0, x_961);
lean_ctor_set(x_963, 1, x_962);
return x_963;
}
}
}
else
{
uint8_t x_964; 
lean_dec(x_925);
lean_dec(x_924);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_964 = !lean_is_exclusive(x_926);
if (x_964 == 0)
{
return x_926;
}
else
{
lean_object* x_965; lean_object* x_966; lean_object* x_967; 
x_965 = lean_ctor_get(x_926, 0);
x_966 = lean_ctor_get(x_926, 1);
lean_inc(x_966);
lean_inc(x_965);
lean_dec(x_926);
x_967 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_967, 0, x_965);
lean_ctor_set(x_967, 1, x_966);
return x_967;
}
}
}
case 10:
{
lean_object* x_968; lean_object* x_969; 
x_968 = lean_ctor_get(x_5, 1);
lean_inc(x_968);
x_969 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_968, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_969) == 0)
{
uint8_t x_970; 
x_970 = !lean_is_exclusive(x_969);
if (x_970 == 0)
{
lean_object* x_971; uint8_t x_972; 
x_971 = lean_ctor_get(x_969, 0);
x_972 = !lean_is_exclusive(x_971);
if (x_972 == 0)
{
lean_object* x_973; lean_object* x_974; 
x_973 = lean_ctor_get(x_971, 0);
x_974 = lean_expr_update_mdata(x_5, x_973);
lean_ctor_set(x_971, 0, x_974);
return x_969;
}
else
{
lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; 
x_975 = lean_ctor_get(x_971, 0);
x_976 = lean_ctor_get(x_971, 1);
lean_inc(x_976);
lean_inc(x_975);
lean_dec(x_971);
x_977 = lean_expr_update_mdata(x_5, x_975);
x_978 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_978, 0, x_977);
lean_ctor_set(x_978, 1, x_976);
lean_ctor_set(x_969, 0, x_978);
return x_969;
}
}
else
{
lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; 
x_979 = lean_ctor_get(x_969, 0);
x_980 = lean_ctor_get(x_969, 1);
lean_inc(x_980);
lean_inc(x_979);
lean_dec(x_969);
x_981 = lean_ctor_get(x_979, 0);
lean_inc(x_981);
x_982 = lean_ctor_get(x_979, 1);
lean_inc(x_982);
if (lean_is_exclusive(x_979)) {
 lean_ctor_release(x_979, 0);
 lean_ctor_release(x_979, 1);
 x_983 = x_979;
} else {
 lean_dec_ref(x_979);
 x_983 = lean_box(0);
}
x_984 = lean_expr_update_mdata(x_5, x_981);
if (lean_is_scalar(x_983)) {
 x_985 = lean_alloc_ctor(0, 2, 0);
} else {
 x_985 = x_983;
}
lean_ctor_set(x_985, 0, x_984);
lean_ctor_set(x_985, 1, x_982);
x_986 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_986, 0, x_985);
lean_ctor_set(x_986, 1, x_980);
return x_986;
}
}
else
{
uint8_t x_987; 
lean_dec(x_5);
x_987 = !lean_is_exclusive(x_969);
if (x_987 == 0)
{
return x_969;
}
else
{
lean_object* x_988; lean_object* x_989; lean_object* x_990; 
x_988 = lean_ctor_get(x_969, 0);
x_989 = lean_ctor_get(x_969, 1);
lean_inc(x_989);
lean_inc(x_988);
lean_dec(x_969);
x_990 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_990, 0, x_988);
lean_ctor_set(x_990, 1, x_989);
return x_990;
}
}
}
case 11:
{
lean_object* x_991; lean_object* x_992; 
x_991 = lean_ctor_get(x_5, 2);
lean_inc(x_991);
x_992 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_991, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_992) == 0)
{
uint8_t x_993; 
x_993 = !lean_is_exclusive(x_992);
if (x_993 == 0)
{
lean_object* x_994; uint8_t x_995; 
x_994 = lean_ctor_get(x_992, 0);
x_995 = !lean_is_exclusive(x_994);
if (x_995 == 0)
{
lean_object* x_996; lean_object* x_997; 
x_996 = lean_ctor_get(x_994, 0);
x_997 = lean_expr_update_proj(x_5, x_996);
lean_ctor_set(x_994, 0, x_997);
return x_992;
}
else
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
x_998 = lean_ctor_get(x_994, 0);
x_999 = lean_ctor_get(x_994, 1);
lean_inc(x_999);
lean_inc(x_998);
lean_dec(x_994);
x_1000 = lean_expr_update_proj(x_5, x_998);
x_1001 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1001, 0, x_1000);
lean_ctor_set(x_1001, 1, x_999);
lean_ctor_set(x_992, 0, x_1001);
return x_992;
}
}
else
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; 
x_1002 = lean_ctor_get(x_992, 0);
x_1003 = lean_ctor_get(x_992, 1);
lean_inc(x_1003);
lean_inc(x_1002);
lean_dec(x_992);
x_1004 = lean_ctor_get(x_1002, 0);
lean_inc(x_1004);
x_1005 = lean_ctor_get(x_1002, 1);
lean_inc(x_1005);
if (lean_is_exclusive(x_1002)) {
 lean_ctor_release(x_1002, 0);
 lean_ctor_release(x_1002, 1);
 x_1006 = x_1002;
} else {
 lean_dec_ref(x_1002);
 x_1006 = lean_box(0);
}
x_1007 = lean_expr_update_proj(x_5, x_1004);
if (lean_is_scalar(x_1006)) {
 x_1008 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1008 = x_1006;
}
lean_ctor_set(x_1008, 0, x_1007);
lean_ctor_set(x_1008, 1, x_1005);
x_1009 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1009, 0, x_1008);
lean_ctor_set(x_1009, 1, x_1003);
return x_1009;
}
}
else
{
uint8_t x_1010; 
lean_dec(x_5);
x_1010 = !lean_is_exclusive(x_992);
if (x_1010 == 0)
{
return x_992;
}
else
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; 
x_1011 = lean_ctor_get(x_992, 0);
x_1012 = lean_ctor_get(x_992, 1);
lean_inc(x_1012);
lean_inc(x_1011);
lean_dec(x_992);
x_1013 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1013, 0, x_1011);
lean_ctor_set(x_1013, 1, x_1012);
return x_1013;
}
}
}
default: 
{
lean_object* x_1014; lean_object* x_1015; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_1014 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1014, 0, x_5);
lean_ctor_set(x_1014, 1, x_7);
x_1015 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1015, 0, x_1014);
lean_ctor_set(x_1015, 1, x_12);
return x_1015;
}
}
}
block_218:
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
lean_inc(x_2);
x_16 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_15, x_6, x_20, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_expr_update_app(x_5, x_19, x_25);
lean_ctor_set(x_23, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = lean_expr_update_app(x_5, x_19, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_21, 0, x_30);
return x_21;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_21, 0);
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_21);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_35 = x_31;
} else {
 lean_dec_ref(x_31);
 x_35 = lean_box(0);
}
x_36 = lean_expr_update_app(x_5, x_19, x_33);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_32);
return x_38;
}
}
else
{
uint8_t x_39; 
lean_dec(x_19);
lean_dec(x_5);
x_39 = !lean_is_exclusive(x_21);
if (x_39 == 0)
{
return x_21;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_21, 0);
x_41 = lean_ctor_get(x_21, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_21);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_16);
if (x_43 == 0)
{
return x_16;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_16, 0);
x_45 = lean_ctor_get(x_16, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_16);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
case 6:
{
lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_5, 2);
lean_inc(x_48);
x_49 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_50 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_47, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_add(x_6, x_55);
lean_dec(x_6);
x_57 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_48, x_56, x_54, x_8, x_9, x_10, x_11, x_52);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = (uint8_t)((x_49 << 24) >> 61);
x_63 = lean_expr_update_lambda(x_5, x_62, x_53, x_61);
lean_ctor_set(x_59, 0, x_63);
return x_57;
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_59, 0);
x_65 = lean_ctor_get(x_59, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_59);
x_66 = (uint8_t)((x_49 << 24) >> 61);
x_67 = lean_expr_update_lambda(x_5, x_66, x_53, x_64);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
lean_ctor_set(x_57, 0, x_68);
return x_57;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_69 = lean_ctor_get(x_57, 0);
x_70 = lean_ctor_get(x_57, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_57);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_73 = x_69;
} else {
 lean_dec_ref(x_69);
 x_73 = lean_box(0);
}
x_74 = (uint8_t)((x_49 << 24) >> 61);
x_75 = lean_expr_update_lambda(x_5, x_74, x_53, x_71);
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_73;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_70);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_dec(x_53);
lean_dec(x_5);
x_78 = !lean_is_exclusive(x_57);
if (x_78 == 0)
{
return x_57;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_57, 0);
x_80 = lean_ctor_get(x_57, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_57);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_dec(x_48);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_82 = !lean_is_exclusive(x_50);
if (x_82 == 0)
{
return x_50;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_50, 0);
x_84 = lean_ctor_get(x_50, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_50);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
case 7:
{
lean_object* x_86; lean_object* x_87; uint64_t x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_5, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_5, 2);
lean_inc(x_87);
x_88 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_89 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_86, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_add(x_6, x_94);
lean_dec(x_6);
x_96 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_87, x_95, x_93, x_8, x_9, x_10, x_11, x_91);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; uint8_t x_99; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; uint8_t x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = (uint8_t)((x_88 << 24) >> 61);
x_102 = lean_expr_update_forall(x_5, x_101, x_92, x_100);
lean_ctor_set(x_98, 0, x_102);
return x_96;
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; 
x_103 = lean_ctor_get(x_98, 0);
x_104 = lean_ctor_get(x_98, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_98);
x_105 = (uint8_t)((x_88 << 24) >> 61);
x_106 = lean_expr_update_forall(x_5, x_105, x_92, x_103);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_104);
lean_ctor_set(x_96, 0, x_107);
return x_96;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_108 = lean_ctor_get(x_96, 0);
x_109 = lean_ctor_get(x_96, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_96);
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_108, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_112 = x_108;
} else {
 lean_dec_ref(x_108);
 x_112 = lean_box(0);
}
x_113 = (uint8_t)((x_88 << 24) >> 61);
x_114 = lean_expr_update_forall(x_5, x_113, x_92, x_110);
if (lean_is_scalar(x_112)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_112;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_111);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_109);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_dec(x_92);
lean_dec(x_5);
x_117 = !lean_is_exclusive(x_96);
if (x_117 == 0)
{
return x_96;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_96, 0);
x_119 = lean_ctor_get(x_96, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_96);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_87);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_121 = !lean_is_exclusive(x_89);
if (x_121 == 0)
{
return x_89;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_89, 0);
x_123 = lean_ctor_get(x_89, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_89);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
case 8:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_5, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_5, 2);
lean_inc(x_126);
x_127 = lean_ctor_get(x_5, 3);
lean_inc(x_127);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_128 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_125, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_ctor_get(x_129, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_2);
x_133 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_126, x_6, x_132, x_8, x_9, x_10, x_11, x_130);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
lean_dec(x_134);
x_138 = lean_unsigned_to_nat(1u);
x_139 = lean_nat_add(x_6, x_138);
lean_dec(x_6);
x_140 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_127, x_139, x_137, x_8, x_9, x_10, x_11, x_135);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_141; 
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; uint8_t x_143; 
x_142 = lean_ctor_get(x_140, 0);
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = lean_expr_update_let(x_5, x_131, x_136, x_144);
lean_ctor_set(x_142, 0, x_145);
return x_140;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_142, 0);
x_147 = lean_ctor_get(x_142, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_142);
x_148 = lean_expr_update_let(x_5, x_131, x_136, x_146);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_147);
lean_ctor_set(x_140, 0, x_149);
return x_140;
}
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_150 = lean_ctor_get(x_140, 0);
x_151 = lean_ctor_get(x_140, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_140);
x_152 = lean_ctor_get(x_150, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_154 = x_150;
} else {
 lean_dec_ref(x_150);
 x_154 = lean_box(0);
}
x_155 = lean_expr_update_let(x_5, x_131, x_136, x_152);
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_154;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_151);
return x_157;
}
}
else
{
uint8_t x_158; 
lean_dec(x_136);
lean_dec(x_131);
lean_dec(x_5);
x_158 = !lean_is_exclusive(x_140);
if (x_158 == 0)
{
return x_140;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_140, 0);
x_160 = lean_ctor_get(x_140, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_140);
x_161 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
}
else
{
uint8_t x_162; 
lean_dec(x_131);
lean_dec(x_127);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_162 = !lean_is_exclusive(x_133);
if (x_162 == 0)
{
return x_133;
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_163 = lean_ctor_get(x_133, 0);
x_164 = lean_ctor_get(x_133, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_133);
x_165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_165, 0, x_163);
lean_ctor_set(x_165, 1, x_164);
return x_165;
}
}
}
else
{
uint8_t x_166; 
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_166 = !lean_is_exclusive(x_128);
if (x_166 == 0)
{
return x_128;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_ctor_get(x_128, 0);
x_168 = lean_ctor_get(x_128, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_128);
x_169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set(x_169, 1, x_168);
return x_169;
}
}
}
case 10:
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_5, 1);
lean_inc(x_170);
x_171 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_170, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_171) == 0)
{
uint8_t x_172; 
x_172 = !lean_is_exclusive(x_171);
if (x_172 == 0)
{
lean_object* x_173; uint8_t x_174; 
x_173 = lean_ctor_get(x_171, 0);
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; 
x_175 = lean_ctor_get(x_173, 0);
x_176 = lean_expr_update_mdata(x_5, x_175);
lean_ctor_set(x_173, 0, x_176);
return x_171;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_177 = lean_ctor_get(x_173, 0);
x_178 = lean_ctor_get(x_173, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_173);
x_179 = lean_expr_update_mdata(x_5, x_177);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_179);
lean_ctor_set(x_180, 1, x_178);
lean_ctor_set(x_171, 0, x_180);
return x_171;
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_181 = lean_ctor_get(x_171, 0);
x_182 = lean_ctor_get(x_171, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_171);
x_183 = lean_ctor_get(x_181, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_181, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_185 = x_181;
} else {
 lean_dec_ref(x_181);
 x_185 = lean_box(0);
}
x_186 = lean_expr_update_mdata(x_5, x_183);
if (lean_is_scalar(x_185)) {
 x_187 = lean_alloc_ctor(0, 2, 0);
} else {
 x_187 = x_185;
}
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_184);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_182);
return x_188;
}
}
else
{
uint8_t x_189; 
lean_dec(x_5);
x_189 = !lean_is_exclusive(x_171);
if (x_189 == 0)
{
return x_171;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_171, 0);
x_191 = lean_ctor_get(x_171, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_171);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
case 11:
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_5, 2);
lean_inc(x_193);
x_194 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_193, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_194) == 0)
{
uint8_t x_195; 
x_195 = !lean_is_exclusive(x_194);
if (x_195 == 0)
{
lean_object* x_196; uint8_t x_197; 
x_196 = lean_ctor_get(x_194, 0);
x_197 = !lean_is_exclusive(x_196);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_ctor_get(x_196, 0);
x_199 = lean_expr_update_proj(x_5, x_198);
lean_ctor_set(x_196, 0, x_199);
return x_194;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_200 = lean_ctor_get(x_196, 0);
x_201 = lean_ctor_get(x_196, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_196);
x_202 = lean_expr_update_proj(x_5, x_200);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_201);
lean_ctor_set(x_194, 0, x_203);
return x_194;
}
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_204 = lean_ctor_get(x_194, 0);
x_205 = lean_ctor_get(x_194, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_194);
x_206 = lean_ctor_get(x_204, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_204, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_208 = x_204;
} else {
 lean_dec_ref(x_204);
 x_208 = lean_box(0);
}
x_209 = lean_expr_update_proj(x_5, x_206);
if (lean_is_scalar(x_208)) {
 x_210 = lean_alloc_ctor(0, 2, 0);
} else {
 x_210 = x_208;
}
lean_ctor_set(x_210, 0, x_209);
lean_ctor_set(x_210, 1, x_207);
x_211 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_211, 0, x_210);
lean_ctor_set(x_211, 1, x_205);
return x_211;
}
}
else
{
uint8_t x_212; 
lean_dec(x_5);
x_212 = !lean_is_exclusive(x_194);
if (x_212 == 0)
{
return x_194;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_194, 0);
x_214 = lean_ctor_get(x_194, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_194);
x_215 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
return x_215;
}
}
}
default: 
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
x_216 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_216, 0, x_5);
lean_ctor_set(x_216, 1, x_7);
x_217 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_217, 0, x_216);
lean_ctor_set(x_217, 1, x_12);
return x_217;
}
}
}
}
}
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux___main___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
lean_object* l___private_Lean_Meta_KAbstract_1__kabstractAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_KAbstract_1__kabstractAux(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
lean_object* l_Lean_Meta_kabstract(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = l_Lean_Expr_toHeadIndex___main(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lean_HeadIndex_1__headNumArgsAux___main(x_2, x_10);
x_12 = lean_unsigned_to_nat(1u);
x_13 = l___private_Lean_Meta_KAbstract_1__kabstractAux___main(x_3, x_2, x_9, x_11, x_1, x_10, x_12, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
lean_dec(x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
lean_object* l_Lean_Meta_kabstract___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_kabstract(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Occurrences(lean_object*);
lean_object* initialize_Lean_HeadIndex(lean_object*);
lean_object* initialize_Lean_Meta_ExprDefEq(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Lean_Meta_KAbstract(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Occurrences(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_HeadIndex(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_ExprDefEq(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
