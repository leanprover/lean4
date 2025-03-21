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
lean_object* l_Lean_Expr_headNumArgs_go(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Occurrences_contains(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(lean_object*, lean_object*);
uint8_t l___private_Init_MetaTypes_0__Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1231_(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_250; 
x_250 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_250 == 0)
{
lean_object* x_251; uint8_t x_252; 
lean_inc(x_5);
x_251 = l_Lean_Expr_toHeadIndex(x_5);
x_252 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_251, x_3);
lean_dec(x_251);
if (x_252 == 0)
{
lean_object* x_253; 
x_253 = lean_box(0);
x_13 = x_253;
goto block_249;
}
else
{
lean_object* x_254; lean_object* x_255; uint8_t x_256; 
x_254 = lean_unsigned_to_nat(0u);
x_255 = l_Lean_Expr_headNumArgs_go(x_5, x_254);
x_256 = lean_nat_dec_eq(x_255, x_4);
lean_dec(x_255);
if (x_256 == 0)
{
lean_object* x_257; 
x_257 = lean_box(0);
x_13 = x_257;
goto block_249;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_258 = lean_st_ref_get(x_9, x_12);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = lean_ctor_get(x_259, 0);
lean_inc(x_261);
lean_dec(x_259);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_5);
x_262 = l_Lean_Meta_isExprDefEq(x_5, x_1, x_8, x_9, x_10, x_11, x_260);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; uint8_t x_264; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_unbox(x_263);
lean_dec(x_263);
if (x_264 == 0)
{
lean_dec(x_261);
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_265 = lean_ctor_get(x_262, 1);
lean_inc(x_265);
lean_dec(x_262);
x_266 = lean_ctor_get(x_5, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_5, 1);
lean_inc(x_267);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_266);
lean_inc(x_1);
x_268 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_266, x_6, x_7, x_8, x_9, x_10, x_11, x_265);
if (lean_obj_tag(x_268) == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_268, 0);
lean_inc(x_269);
x_270 = lean_ctor_get(x_268, 1);
lean_inc(x_270);
lean_dec(x_268);
lean_inc(x_267);
x_271 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_267, x_6, x_7, x_8, x_9, x_10, x_11, x_270);
if (lean_obj_tag(x_271) == 0)
{
uint8_t x_272; 
x_272 = !lean_is_exclusive(x_271);
if (x_272 == 0)
{
lean_object* x_273; size_t x_274; size_t x_275; uint8_t x_276; 
x_273 = lean_ctor_get(x_271, 0);
x_274 = lean_ptr_addr(x_266);
lean_dec(x_266);
x_275 = lean_ptr_addr(x_269);
x_276 = lean_usize_dec_eq(x_274, x_275);
if (x_276 == 0)
{
lean_object* x_277; 
lean_dec(x_267);
lean_dec(x_5);
x_277 = l_Lean_Expr_app___override(x_269, x_273);
lean_ctor_set(x_271, 0, x_277);
return x_271;
}
else
{
size_t x_278; size_t x_279; uint8_t x_280; 
x_278 = lean_ptr_addr(x_267);
lean_dec(x_267);
x_279 = lean_ptr_addr(x_273);
x_280 = lean_usize_dec_eq(x_278, x_279);
if (x_280 == 0)
{
lean_object* x_281; 
lean_dec(x_5);
x_281 = l_Lean_Expr_app___override(x_269, x_273);
lean_ctor_set(x_271, 0, x_281);
return x_271;
}
else
{
lean_dec(x_273);
lean_dec(x_269);
lean_ctor_set(x_271, 0, x_5);
return x_271;
}
}
}
else
{
lean_object* x_282; lean_object* x_283; size_t x_284; size_t x_285; uint8_t x_286; 
x_282 = lean_ctor_get(x_271, 0);
x_283 = lean_ctor_get(x_271, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_271);
x_284 = lean_ptr_addr(x_266);
lean_dec(x_266);
x_285 = lean_ptr_addr(x_269);
x_286 = lean_usize_dec_eq(x_284, x_285);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; 
lean_dec(x_267);
lean_dec(x_5);
x_287 = l_Lean_Expr_app___override(x_269, x_282);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_283);
return x_288;
}
else
{
size_t x_289; size_t x_290; uint8_t x_291; 
x_289 = lean_ptr_addr(x_267);
lean_dec(x_267);
x_290 = lean_ptr_addr(x_282);
x_291 = lean_usize_dec_eq(x_289, x_290);
if (x_291 == 0)
{
lean_object* x_292; lean_object* x_293; 
lean_dec(x_5);
x_292 = l_Lean_Expr_app___override(x_269, x_282);
x_293 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_293, 0, x_292);
lean_ctor_set(x_293, 1, x_283);
return x_293;
}
else
{
lean_object* x_294; 
lean_dec(x_282);
lean_dec(x_269);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_5);
lean_ctor_set(x_294, 1, x_283);
return x_294;
}
}
}
}
else
{
uint8_t x_295; 
lean_dec(x_269);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_5);
x_295 = !lean_is_exclusive(x_271);
if (x_295 == 0)
{
return x_271;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_271, 0);
x_297 = lean_ctor_get(x_271, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_271);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
return x_298;
}
}
}
else
{
uint8_t x_299; 
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_299 = !lean_is_exclusive(x_268);
if (x_299 == 0)
{
return x_268;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_268, 0);
x_301 = lean_ctor_get(x_268, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_268);
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
return x_302;
}
}
}
case 6:
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; lean_object* x_308; 
x_303 = lean_ctor_get(x_262, 1);
lean_inc(x_303);
lean_dec(x_262);
x_304 = lean_ctor_get(x_5, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_5, 1);
lean_inc(x_305);
x_306 = lean_ctor_get(x_5, 2);
lean_inc(x_306);
x_307 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_305);
lean_inc(x_1);
x_308 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_305, x_6, x_7, x_8, x_9, x_10, x_11, x_303);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_309 = lean_ctor_get(x_308, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_308, 1);
lean_inc(x_310);
lean_dec(x_308);
x_311 = lean_unsigned_to_nat(1u);
x_312 = lean_nat_add(x_6, x_311);
lean_dec(x_6);
lean_inc(x_306);
x_313 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_306, x_312, x_7, x_8, x_9, x_10, x_11, x_310);
if (lean_obj_tag(x_313) == 0)
{
uint8_t x_314; 
x_314 = !lean_is_exclusive(x_313);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; size_t x_317; size_t x_318; uint8_t x_319; 
x_315 = lean_ctor_get(x_313, 0);
lean_inc(x_306);
lean_inc(x_305);
lean_inc(x_304);
x_316 = l_Lean_Expr_lam___override(x_304, x_305, x_306, x_307);
x_317 = lean_ptr_addr(x_305);
lean_dec(x_305);
x_318 = lean_ptr_addr(x_309);
x_319 = lean_usize_dec_eq(x_317, x_318);
if (x_319 == 0)
{
lean_object* x_320; 
lean_dec(x_316);
lean_dec(x_306);
x_320 = l_Lean_Expr_lam___override(x_304, x_309, x_315, x_307);
lean_ctor_set(x_313, 0, x_320);
return x_313;
}
else
{
size_t x_321; size_t x_322; uint8_t x_323; 
x_321 = lean_ptr_addr(x_306);
lean_dec(x_306);
x_322 = lean_ptr_addr(x_315);
x_323 = lean_usize_dec_eq(x_321, x_322);
if (x_323 == 0)
{
lean_object* x_324; 
lean_dec(x_316);
x_324 = l_Lean_Expr_lam___override(x_304, x_309, x_315, x_307);
lean_ctor_set(x_313, 0, x_324);
return x_313;
}
else
{
uint8_t x_325; 
x_325 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_307, x_307);
if (x_325 == 0)
{
lean_object* x_326; 
lean_dec(x_316);
x_326 = l_Lean_Expr_lam___override(x_304, x_309, x_315, x_307);
lean_ctor_set(x_313, 0, x_326);
return x_313;
}
else
{
lean_dec(x_315);
lean_dec(x_309);
lean_dec(x_304);
lean_ctor_set(x_313, 0, x_316);
return x_313;
}
}
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; size_t x_330; size_t x_331; uint8_t x_332; 
x_327 = lean_ctor_get(x_313, 0);
x_328 = lean_ctor_get(x_313, 1);
lean_inc(x_328);
lean_inc(x_327);
lean_dec(x_313);
lean_inc(x_306);
lean_inc(x_305);
lean_inc(x_304);
x_329 = l_Lean_Expr_lam___override(x_304, x_305, x_306, x_307);
x_330 = lean_ptr_addr(x_305);
lean_dec(x_305);
x_331 = lean_ptr_addr(x_309);
x_332 = lean_usize_dec_eq(x_330, x_331);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; 
lean_dec(x_329);
lean_dec(x_306);
x_333 = l_Lean_Expr_lam___override(x_304, x_309, x_327, x_307);
x_334 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_334, 0, x_333);
lean_ctor_set(x_334, 1, x_328);
return x_334;
}
else
{
size_t x_335; size_t x_336; uint8_t x_337; 
x_335 = lean_ptr_addr(x_306);
lean_dec(x_306);
x_336 = lean_ptr_addr(x_327);
x_337 = lean_usize_dec_eq(x_335, x_336);
if (x_337 == 0)
{
lean_object* x_338; lean_object* x_339; 
lean_dec(x_329);
x_338 = l_Lean_Expr_lam___override(x_304, x_309, x_327, x_307);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_328);
return x_339;
}
else
{
uint8_t x_340; 
x_340 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_307, x_307);
if (x_340 == 0)
{
lean_object* x_341; lean_object* x_342; 
lean_dec(x_329);
x_341 = l_Lean_Expr_lam___override(x_304, x_309, x_327, x_307);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_328);
return x_342;
}
else
{
lean_object* x_343; 
lean_dec(x_327);
lean_dec(x_309);
lean_dec(x_304);
x_343 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_343, 0, x_329);
lean_ctor_set(x_343, 1, x_328);
return x_343;
}
}
}
}
}
else
{
uint8_t x_344; 
lean_dec(x_309);
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
x_344 = !lean_is_exclusive(x_313);
if (x_344 == 0)
{
return x_313;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_313, 0);
x_346 = lean_ctor_get(x_313, 1);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_313);
x_347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
return x_347;
}
}
}
else
{
uint8_t x_348; 
lean_dec(x_306);
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_348 = !lean_is_exclusive(x_308);
if (x_348 == 0)
{
return x_308;
}
else
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_349 = lean_ctor_get(x_308, 0);
x_350 = lean_ctor_get(x_308, 1);
lean_inc(x_350);
lean_inc(x_349);
lean_dec(x_308);
x_351 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
return x_351;
}
}
}
case 7:
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; uint8_t x_356; lean_object* x_357; 
x_352 = lean_ctor_get(x_262, 1);
lean_inc(x_352);
lean_dec(x_262);
x_353 = lean_ctor_get(x_5, 0);
lean_inc(x_353);
x_354 = lean_ctor_get(x_5, 1);
lean_inc(x_354);
x_355 = lean_ctor_get(x_5, 2);
lean_inc(x_355);
x_356 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_354);
lean_inc(x_1);
x_357 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_354, x_6, x_7, x_8, x_9, x_10, x_11, x_352);
if (lean_obj_tag(x_357) == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_358 = lean_ctor_get(x_357, 0);
lean_inc(x_358);
x_359 = lean_ctor_get(x_357, 1);
lean_inc(x_359);
lean_dec(x_357);
x_360 = lean_unsigned_to_nat(1u);
x_361 = lean_nat_add(x_6, x_360);
lean_dec(x_6);
lean_inc(x_355);
x_362 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_355, x_361, x_7, x_8, x_9, x_10, x_11, x_359);
if (lean_obj_tag(x_362) == 0)
{
uint8_t x_363; 
x_363 = !lean_is_exclusive(x_362);
if (x_363 == 0)
{
lean_object* x_364; lean_object* x_365; size_t x_366; size_t x_367; uint8_t x_368; 
x_364 = lean_ctor_get(x_362, 0);
lean_inc(x_355);
lean_inc(x_354);
lean_inc(x_353);
x_365 = l_Lean_Expr_forallE___override(x_353, x_354, x_355, x_356);
x_366 = lean_ptr_addr(x_354);
lean_dec(x_354);
x_367 = lean_ptr_addr(x_358);
x_368 = lean_usize_dec_eq(x_366, x_367);
if (x_368 == 0)
{
lean_object* x_369; 
lean_dec(x_365);
lean_dec(x_355);
x_369 = l_Lean_Expr_forallE___override(x_353, x_358, x_364, x_356);
lean_ctor_set(x_362, 0, x_369);
return x_362;
}
else
{
size_t x_370; size_t x_371; uint8_t x_372; 
x_370 = lean_ptr_addr(x_355);
lean_dec(x_355);
x_371 = lean_ptr_addr(x_364);
x_372 = lean_usize_dec_eq(x_370, x_371);
if (x_372 == 0)
{
lean_object* x_373; 
lean_dec(x_365);
x_373 = l_Lean_Expr_forallE___override(x_353, x_358, x_364, x_356);
lean_ctor_set(x_362, 0, x_373);
return x_362;
}
else
{
uint8_t x_374; 
x_374 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_356, x_356);
if (x_374 == 0)
{
lean_object* x_375; 
lean_dec(x_365);
x_375 = l_Lean_Expr_forallE___override(x_353, x_358, x_364, x_356);
lean_ctor_set(x_362, 0, x_375);
return x_362;
}
else
{
lean_dec(x_364);
lean_dec(x_358);
lean_dec(x_353);
lean_ctor_set(x_362, 0, x_365);
return x_362;
}
}
}
}
else
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; size_t x_379; size_t x_380; uint8_t x_381; 
x_376 = lean_ctor_get(x_362, 0);
x_377 = lean_ctor_get(x_362, 1);
lean_inc(x_377);
lean_inc(x_376);
lean_dec(x_362);
lean_inc(x_355);
lean_inc(x_354);
lean_inc(x_353);
x_378 = l_Lean_Expr_forallE___override(x_353, x_354, x_355, x_356);
x_379 = lean_ptr_addr(x_354);
lean_dec(x_354);
x_380 = lean_ptr_addr(x_358);
x_381 = lean_usize_dec_eq(x_379, x_380);
if (x_381 == 0)
{
lean_object* x_382; lean_object* x_383; 
lean_dec(x_378);
lean_dec(x_355);
x_382 = l_Lean_Expr_forallE___override(x_353, x_358, x_376, x_356);
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_377);
return x_383;
}
else
{
size_t x_384; size_t x_385; uint8_t x_386; 
x_384 = lean_ptr_addr(x_355);
lean_dec(x_355);
x_385 = lean_ptr_addr(x_376);
x_386 = lean_usize_dec_eq(x_384, x_385);
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; 
lean_dec(x_378);
x_387 = l_Lean_Expr_forallE___override(x_353, x_358, x_376, x_356);
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_387);
lean_ctor_set(x_388, 1, x_377);
return x_388;
}
else
{
uint8_t x_389; 
x_389 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_356, x_356);
if (x_389 == 0)
{
lean_object* x_390; lean_object* x_391; 
lean_dec(x_378);
x_390 = l_Lean_Expr_forallE___override(x_353, x_358, x_376, x_356);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_377);
return x_391;
}
else
{
lean_object* x_392; 
lean_dec(x_376);
lean_dec(x_358);
lean_dec(x_353);
x_392 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_392, 0, x_378);
lean_ctor_set(x_392, 1, x_377);
return x_392;
}
}
}
}
}
else
{
uint8_t x_393; 
lean_dec(x_358);
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_353);
x_393 = !lean_is_exclusive(x_362);
if (x_393 == 0)
{
return x_362;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_362, 0);
x_395 = lean_ctor_get(x_362, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_362);
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
lean_dec(x_355);
lean_dec(x_354);
lean_dec(x_353);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_397 = !lean_is_exclusive(x_357);
if (x_397 == 0)
{
return x_357;
}
else
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; 
x_398 = lean_ctor_get(x_357, 0);
x_399 = lean_ctor_get(x_357, 1);
lean_inc(x_399);
lean_inc(x_398);
lean_dec(x_357);
x_400 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_400, 0, x_398);
lean_ctor_set(x_400, 1, x_399);
return x_400;
}
}
}
case 8:
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; lean_object* x_407; 
x_401 = lean_ctor_get(x_262, 1);
lean_inc(x_401);
lean_dec(x_262);
x_402 = lean_ctor_get(x_5, 0);
lean_inc(x_402);
x_403 = lean_ctor_get(x_5, 1);
lean_inc(x_403);
x_404 = lean_ctor_get(x_5, 2);
lean_inc(x_404);
x_405 = lean_ctor_get(x_5, 3);
lean_inc(x_405);
x_406 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_403);
lean_inc(x_1);
x_407 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_403, x_6, x_7, x_8, x_9, x_10, x_11, x_401);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_404);
lean_inc(x_1);
x_410 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_404, x_6, x_7, x_8, x_9, x_10, x_11, x_409);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_410, 1);
lean_inc(x_412);
lean_dec(x_410);
x_413 = lean_unsigned_to_nat(1u);
x_414 = lean_nat_add(x_6, x_413);
lean_dec(x_6);
lean_inc(x_405);
x_415 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_405, x_414, x_7, x_8, x_9, x_10, x_11, x_412);
if (lean_obj_tag(x_415) == 0)
{
uint8_t x_416; 
x_416 = !lean_is_exclusive(x_415);
if (x_416 == 0)
{
lean_object* x_417; size_t x_418; size_t x_419; uint8_t x_420; 
x_417 = lean_ctor_get(x_415, 0);
x_418 = lean_ptr_addr(x_403);
lean_dec(x_403);
x_419 = lean_ptr_addr(x_408);
x_420 = lean_usize_dec_eq(x_418, x_419);
if (x_420 == 0)
{
lean_object* x_421; 
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_5);
x_421 = l_Lean_Expr_letE___override(x_402, x_408, x_411, x_417, x_406);
lean_ctor_set(x_415, 0, x_421);
return x_415;
}
else
{
size_t x_422; size_t x_423; uint8_t x_424; 
x_422 = lean_ptr_addr(x_404);
lean_dec(x_404);
x_423 = lean_ptr_addr(x_411);
x_424 = lean_usize_dec_eq(x_422, x_423);
if (x_424 == 0)
{
lean_object* x_425; 
lean_dec(x_405);
lean_dec(x_5);
x_425 = l_Lean_Expr_letE___override(x_402, x_408, x_411, x_417, x_406);
lean_ctor_set(x_415, 0, x_425);
return x_415;
}
else
{
size_t x_426; size_t x_427; uint8_t x_428; 
x_426 = lean_ptr_addr(x_405);
lean_dec(x_405);
x_427 = lean_ptr_addr(x_417);
x_428 = lean_usize_dec_eq(x_426, x_427);
if (x_428 == 0)
{
lean_object* x_429; 
lean_dec(x_5);
x_429 = l_Lean_Expr_letE___override(x_402, x_408, x_411, x_417, x_406);
lean_ctor_set(x_415, 0, x_429);
return x_415;
}
else
{
lean_dec(x_417);
lean_dec(x_411);
lean_dec(x_408);
lean_dec(x_402);
lean_ctor_set(x_415, 0, x_5);
return x_415;
}
}
}
}
else
{
lean_object* x_430; lean_object* x_431; size_t x_432; size_t x_433; uint8_t x_434; 
x_430 = lean_ctor_get(x_415, 0);
x_431 = lean_ctor_get(x_415, 1);
lean_inc(x_431);
lean_inc(x_430);
lean_dec(x_415);
x_432 = lean_ptr_addr(x_403);
lean_dec(x_403);
x_433 = lean_ptr_addr(x_408);
x_434 = lean_usize_dec_eq(x_432, x_433);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; 
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_5);
x_435 = l_Lean_Expr_letE___override(x_402, x_408, x_411, x_430, x_406);
x_436 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_431);
return x_436;
}
else
{
size_t x_437; size_t x_438; uint8_t x_439; 
x_437 = lean_ptr_addr(x_404);
lean_dec(x_404);
x_438 = lean_ptr_addr(x_411);
x_439 = lean_usize_dec_eq(x_437, x_438);
if (x_439 == 0)
{
lean_object* x_440; lean_object* x_441; 
lean_dec(x_405);
lean_dec(x_5);
x_440 = l_Lean_Expr_letE___override(x_402, x_408, x_411, x_430, x_406);
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_431);
return x_441;
}
else
{
size_t x_442; size_t x_443; uint8_t x_444; 
x_442 = lean_ptr_addr(x_405);
lean_dec(x_405);
x_443 = lean_ptr_addr(x_430);
x_444 = lean_usize_dec_eq(x_442, x_443);
if (x_444 == 0)
{
lean_object* x_445; lean_object* x_446; 
lean_dec(x_5);
x_445 = l_Lean_Expr_letE___override(x_402, x_408, x_411, x_430, x_406);
x_446 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_431);
return x_446;
}
else
{
lean_object* x_447; 
lean_dec(x_430);
lean_dec(x_411);
lean_dec(x_408);
lean_dec(x_402);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_5);
lean_ctor_set(x_447, 1, x_431);
return x_447;
}
}
}
}
}
else
{
uint8_t x_448; 
lean_dec(x_411);
lean_dec(x_408);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_402);
lean_dec(x_5);
x_448 = !lean_is_exclusive(x_415);
if (x_448 == 0)
{
return x_415;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_415, 0);
x_450 = lean_ctor_get(x_415, 1);
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_415);
x_451 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_451, 0, x_449);
lean_ctor_set(x_451, 1, x_450);
return x_451;
}
}
}
else
{
uint8_t x_452; 
lean_dec(x_408);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_402);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_452 = !lean_is_exclusive(x_410);
if (x_452 == 0)
{
return x_410;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_410, 0);
x_454 = lean_ctor_get(x_410, 1);
lean_inc(x_454);
lean_inc(x_453);
lean_dec(x_410);
x_455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_455, 0, x_453);
lean_ctor_set(x_455, 1, x_454);
return x_455;
}
}
}
else
{
uint8_t x_456; 
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_403);
lean_dec(x_402);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_456 = !lean_is_exclusive(x_407);
if (x_456 == 0)
{
return x_407;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_407, 0);
x_458 = lean_ctor_get(x_407, 1);
lean_inc(x_458);
lean_inc(x_457);
lean_dec(x_407);
x_459 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_459, 0, x_457);
lean_ctor_set(x_459, 1, x_458);
return x_459;
}
}
}
case 10:
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_460 = lean_ctor_get(x_262, 1);
lean_inc(x_460);
lean_dec(x_262);
x_461 = lean_ctor_get(x_5, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_5, 1);
lean_inc(x_462);
lean_inc(x_462);
x_463 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_462, x_6, x_7, x_8, x_9, x_10, x_11, x_460);
if (lean_obj_tag(x_463) == 0)
{
uint8_t x_464; 
x_464 = !lean_is_exclusive(x_463);
if (x_464 == 0)
{
lean_object* x_465; size_t x_466; size_t x_467; uint8_t x_468; 
x_465 = lean_ctor_get(x_463, 0);
x_466 = lean_ptr_addr(x_462);
lean_dec(x_462);
x_467 = lean_ptr_addr(x_465);
x_468 = lean_usize_dec_eq(x_466, x_467);
if (x_468 == 0)
{
lean_object* x_469; 
lean_dec(x_5);
x_469 = l_Lean_Expr_mdata___override(x_461, x_465);
lean_ctor_set(x_463, 0, x_469);
return x_463;
}
else
{
lean_dec(x_465);
lean_dec(x_461);
lean_ctor_set(x_463, 0, x_5);
return x_463;
}
}
else
{
lean_object* x_470; lean_object* x_471; size_t x_472; size_t x_473; uint8_t x_474; 
x_470 = lean_ctor_get(x_463, 0);
x_471 = lean_ctor_get(x_463, 1);
lean_inc(x_471);
lean_inc(x_470);
lean_dec(x_463);
x_472 = lean_ptr_addr(x_462);
lean_dec(x_462);
x_473 = lean_ptr_addr(x_470);
x_474 = lean_usize_dec_eq(x_472, x_473);
if (x_474 == 0)
{
lean_object* x_475; lean_object* x_476; 
lean_dec(x_5);
x_475 = l_Lean_Expr_mdata___override(x_461, x_470);
x_476 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_476, 0, x_475);
lean_ctor_set(x_476, 1, x_471);
return x_476;
}
else
{
lean_object* x_477; 
lean_dec(x_470);
lean_dec(x_461);
x_477 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_477, 0, x_5);
lean_ctor_set(x_477, 1, x_471);
return x_477;
}
}
}
else
{
uint8_t x_478; 
lean_dec(x_462);
lean_dec(x_461);
lean_dec(x_5);
x_478 = !lean_is_exclusive(x_463);
if (x_478 == 0)
{
return x_463;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_479 = lean_ctor_get(x_463, 0);
x_480 = lean_ctor_get(x_463, 1);
lean_inc(x_480);
lean_inc(x_479);
lean_dec(x_463);
x_481 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_481, 0, x_479);
lean_ctor_set(x_481, 1, x_480);
return x_481;
}
}
}
case 11:
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_482 = lean_ctor_get(x_262, 1);
lean_inc(x_482);
lean_dec(x_262);
x_483 = lean_ctor_get(x_5, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_5, 1);
lean_inc(x_484);
x_485 = lean_ctor_get(x_5, 2);
lean_inc(x_485);
lean_inc(x_485);
x_486 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_485, x_6, x_7, x_8, x_9, x_10, x_11, x_482);
if (lean_obj_tag(x_486) == 0)
{
uint8_t x_487; 
x_487 = !lean_is_exclusive(x_486);
if (x_487 == 0)
{
lean_object* x_488; size_t x_489; size_t x_490; uint8_t x_491; 
x_488 = lean_ctor_get(x_486, 0);
x_489 = lean_ptr_addr(x_485);
lean_dec(x_485);
x_490 = lean_ptr_addr(x_488);
x_491 = lean_usize_dec_eq(x_489, x_490);
if (x_491 == 0)
{
lean_object* x_492; 
lean_dec(x_5);
x_492 = l_Lean_Expr_proj___override(x_483, x_484, x_488);
lean_ctor_set(x_486, 0, x_492);
return x_486;
}
else
{
lean_dec(x_488);
lean_dec(x_484);
lean_dec(x_483);
lean_ctor_set(x_486, 0, x_5);
return x_486;
}
}
else
{
lean_object* x_493; lean_object* x_494; size_t x_495; size_t x_496; uint8_t x_497; 
x_493 = lean_ctor_get(x_486, 0);
x_494 = lean_ctor_get(x_486, 1);
lean_inc(x_494);
lean_inc(x_493);
lean_dec(x_486);
x_495 = lean_ptr_addr(x_485);
lean_dec(x_485);
x_496 = lean_ptr_addr(x_493);
x_497 = lean_usize_dec_eq(x_495, x_496);
if (x_497 == 0)
{
lean_object* x_498; lean_object* x_499; 
lean_dec(x_5);
x_498 = l_Lean_Expr_proj___override(x_483, x_484, x_493);
x_499 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_499, 0, x_498);
lean_ctor_set(x_499, 1, x_494);
return x_499;
}
else
{
lean_object* x_500; 
lean_dec(x_493);
lean_dec(x_484);
lean_dec(x_483);
x_500 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_500, 0, x_5);
lean_ctor_set(x_500, 1, x_494);
return x_500;
}
}
}
else
{
uint8_t x_501; 
lean_dec(x_485);
lean_dec(x_484);
lean_dec(x_483);
lean_dec(x_5);
x_501 = !lean_is_exclusive(x_486);
if (x_501 == 0)
{
return x_486;
}
else
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; 
x_502 = lean_ctor_get(x_486, 0);
x_503 = lean_ctor_get(x_486, 1);
lean_inc(x_503);
lean_inc(x_502);
lean_dec(x_486);
x_504 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_504, 0, x_502);
lean_ctor_set(x_504, 1, x_503);
return x_504;
}
}
}
default: 
{
uint8_t x_505; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_505 = !lean_is_exclusive(x_262);
if (x_505 == 0)
{
lean_object* x_506; 
x_506 = lean_ctor_get(x_262, 0);
lean_dec(x_506);
lean_ctor_set(x_262, 0, x_5);
return x_262;
}
else
{
lean_object* x_507; lean_object* x_508; 
x_507 = lean_ctor_get(x_262, 1);
lean_inc(x_507);
lean_dec(x_262);
x_508 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_508, 0, x_5);
lean_ctor_set(x_508, 1, x_507);
return x_508;
}
}
}
}
else
{
lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; uint8_t x_516; 
x_509 = lean_ctor_get(x_262, 1);
lean_inc(x_509);
lean_dec(x_262);
x_510 = lean_st_ref_get(x_7, x_509);
x_511 = lean_ctor_get(x_510, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_510, 1);
lean_inc(x_512);
lean_dec(x_510);
x_513 = lean_unsigned_to_nat(1u);
x_514 = lean_nat_add(x_511, x_513);
x_515 = lean_st_ref_set(x_7, x_514, x_512);
x_516 = !lean_is_exclusive(x_515);
if (x_516 == 0)
{
lean_object* x_517; lean_object* x_518; uint8_t x_519; 
x_517 = lean_ctor_get(x_515, 1);
x_518 = lean_ctor_get(x_515, 0);
lean_dec(x_518);
x_519 = l_Lean_Meta_Occurrences_contains(x_2, x_511);
lean_dec(x_511);
if (x_519 == 0)
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; uint8_t x_523; 
lean_free_object(x_515);
x_520 = lean_st_ref_take(x_9, x_517);
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_520, 1);
lean_inc(x_522);
lean_dec(x_520);
x_523 = !lean_is_exclusive(x_521);
if (x_523 == 0)
{
lean_object* x_524; lean_object* x_525; 
x_524 = lean_ctor_get(x_521, 0);
lean_dec(x_524);
lean_ctor_set(x_521, 0, x_261);
x_525 = lean_st_ref_set(x_9, x_521, x_522);
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_526 = lean_ctor_get(x_525, 1);
lean_inc(x_526);
lean_dec(x_525);
x_527 = lean_ctor_get(x_5, 0);
lean_inc(x_527);
x_528 = lean_ctor_get(x_5, 1);
lean_inc(x_528);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_527);
lean_inc(x_1);
x_529 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_527, x_6, x_7, x_8, x_9, x_10, x_11, x_526);
if (lean_obj_tag(x_529) == 0)
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; 
x_530 = lean_ctor_get(x_529, 0);
lean_inc(x_530);
x_531 = lean_ctor_get(x_529, 1);
lean_inc(x_531);
lean_dec(x_529);
lean_inc(x_528);
x_532 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_528, x_6, x_7, x_8, x_9, x_10, x_11, x_531);
if (lean_obj_tag(x_532) == 0)
{
uint8_t x_533; 
x_533 = !lean_is_exclusive(x_532);
if (x_533 == 0)
{
lean_object* x_534; size_t x_535; size_t x_536; uint8_t x_537; 
x_534 = lean_ctor_get(x_532, 0);
x_535 = lean_ptr_addr(x_527);
lean_dec(x_527);
x_536 = lean_ptr_addr(x_530);
x_537 = lean_usize_dec_eq(x_535, x_536);
if (x_537 == 0)
{
lean_object* x_538; 
lean_dec(x_528);
lean_dec(x_5);
x_538 = l_Lean_Expr_app___override(x_530, x_534);
lean_ctor_set(x_532, 0, x_538);
return x_532;
}
else
{
size_t x_539; size_t x_540; uint8_t x_541; 
x_539 = lean_ptr_addr(x_528);
lean_dec(x_528);
x_540 = lean_ptr_addr(x_534);
x_541 = lean_usize_dec_eq(x_539, x_540);
if (x_541 == 0)
{
lean_object* x_542; 
lean_dec(x_5);
x_542 = l_Lean_Expr_app___override(x_530, x_534);
lean_ctor_set(x_532, 0, x_542);
return x_532;
}
else
{
lean_dec(x_534);
lean_dec(x_530);
lean_ctor_set(x_532, 0, x_5);
return x_532;
}
}
}
else
{
lean_object* x_543; lean_object* x_544; size_t x_545; size_t x_546; uint8_t x_547; 
x_543 = lean_ctor_get(x_532, 0);
x_544 = lean_ctor_get(x_532, 1);
lean_inc(x_544);
lean_inc(x_543);
lean_dec(x_532);
x_545 = lean_ptr_addr(x_527);
lean_dec(x_527);
x_546 = lean_ptr_addr(x_530);
x_547 = lean_usize_dec_eq(x_545, x_546);
if (x_547 == 0)
{
lean_object* x_548; lean_object* x_549; 
lean_dec(x_528);
lean_dec(x_5);
x_548 = l_Lean_Expr_app___override(x_530, x_543);
x_549 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_549, 0, x_548);
lean_ctor_set(x_549, 1, x_544);
return x_549;
}
else
{
size_t x_550; size_t x_551; uint8_t x_552; 
x_550 = lean_ptr_addr(x_528);
lean_dec(x_528);
x_551 = lean_ptr_addr(x_543);
x_552 = lean_usize_dec_eq(x_550, x_551);
if (x_552 == 0)
{
lean_object* x_553; lean_object* x_554; 
lean_dec(x_5);
x_553 = l_Lean_Expr_app___override(x_530, x_543);
x_554 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_554, 0, x_553);
lean_ctor_set(x_554, 1, x_544);
return x_554;
}
else
{
lean_object* x_555; 
lean_dec(x_543);
lean_dec(x_530);
x_555 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_555, 0, x_5);
lean_ctor_set(x_555, 1, x_544);
return x_555;
}
}
}
}
else
{
uint8_t x_556; 
lean_dec(x_530);
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_5);
x_556 = !lean_is_exclusive(x_532);
if (x_556 == 0)
{
return x_532;
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; 
x_557 = lean_ctor_get(x_532, 0);
x_558 = lean_ctor_get(x_532, 1);
lean_inc(x_558);
lean_inc(x_557);
lean_dec(x_532);
x_559 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_559, 0, x_557);
lean_ctor_set(x_559, 1, x_558);
return x_559;
}
}
}
else
{
uint8_t x_560; 
lean_dec(x_528);
lean_dec(x_527);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_560 = !lean_is_exclusive(x_529);
if (x_560 == 0)
{
return x_529;
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_561 = lean_ctor_get(x_529, 0);
x_562 = lean_ctor_get(x_529, 1);
lean_inc(x_562);
lean_inc(x_561);
lean_dec(x_529);
x_563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_563, 0, x_561);
lean_ctor_set(x_563, 1, x_562);
return x_563;
}
}
}
case 6:
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; uint8_t x_568; lean_object* x_569; 
x_564 = lean_ctor_get(x_525, 1);
lean_inc(x_564);
lean_dec(x_525);
x_565 = lean_ctor_get(x_5, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_5, 1);
lean_inc(x_566);
x_567 = lean_ctor_get(x_5, 2);
lean_inc(x_567);
x_568 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_566);
lean_inc(x_1);
x_569 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_566, x_6, x_7, x_8, x_9, x_10, x_11, x_564);
if (lean_obj_tag(x_569) == 0)
{
lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; 
x_570 = lean_ctor_get(x_569, 0);
lean_inc(x_570);
x_571 = lean_ctor_get(x_569, 1);
lean_inc(x_571);
lean_dec(x_569);
x_572 = lean_nat_add(x_6, x_513);
lean_dec(x_6);
lean_inc(x_567);
x_573 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_567, x_572, x_7, x_8, x_9, x_10, x_11, x_571);
if (lean_obj_tag(x_573) == 0)
{
uint8_t x_574; 
x_574 = !lean_is_exclusive(x_573);
if (x_574 == 0)
{
lean_object* x_575; lean_object* x_576; size_t x_577; size_t x_578; uint8_t x_579; 
x_575 = lean_ctor_get(x_573, 0);
lean_inc(x_567);
lean_inc(x_566);
lean_inc(x_565);
x_576 = l_Lean_Expr_lam___override(x_565, x_566, x_567, x_568);
x_577 = lean_ptr_addr(x_566);
lean_dec(x_566);
x_578 = lean_ptr_addr(x_570);
x_579 = lean_usize_dec_eq(x_577, x_578);
if (x_579 == 0)
{
lean_object* x_580; 
lean_dec(x_576);
lean_dec(x_567);
x_580 = l_Lean_Expr_lam___override(x_565, x_570, x_575, x_568);
lean_ctor_set(x_573, 0, x_580);
return x_573;
}
else
{
size_t x_581; size_t x_582; uint8_t x_583; 
x_581 = lean_ptr_addr(x_567);
lean_dec(x_567);
x_582 = lean_ptr_addr(x_575);
x_583 = lean_usize_dec_eq(x_581, x_582);
if (x_583 == 0)
{
lean_object* x_584; 
lean_dec(x_576);
x_584 = l_Lean_Expr_lam___override(x_565, x_570, x_575, x_568);
lean_ctor_set(x_573, 0, x_584);
return x_573;
}
else
{
uint8_t x_585; 
x_585 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_568, x_568);
if (x_585 == 0)
{
lean_object* x_586; 
lean_dec(x_576);
x_586 = l_Lean_Expr_lam___override(x_565, x_570, x_575, x_568);
lean_ctor_set(x_573, 0, x_586);
return x_573;
}
else
{
lean_dec(x_575);
lean_dec(x_570);
lean_dec(x_565);
lean_ctor_set(x_573, 0, x_576);
return x_573;
}
}
}
}
else
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; size_t x_590; size_t x_591; uint8_t x_592; 
x_587 = lean_ctor_get(x_573, 0);
x_588 = lean_ctor_get(x_573, 1);
lean_inc(x_588);
lean_inc(x_587);
lean_dec(x_573);
lean_inc(x_567);
lean_inc(x_566);
lean_inc(x_565);
x_589 = l_Lean_Expr_lam___override(x_565, x_566, x_567, x_568);
x_590 = lean_ptr_addr(x_566);
lean_dec(x_566);
x_591 = lean_ptr_addr(x_570);
x_592 = lean_usize_dec_eq(x_590, x_591);
if (x_592 == 0)
{
lean_object* x_593; lean_object* x_594; 
lean_dec(x_589);
lean_dec(x_567);
x_593 = l_Lean_Expr_lam___override(x_565, x_570, x_587, x_568);
x_594 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_594, 0, x_593);
lean_ctor_set(x_594, 1, x_588);
return x_594;
}
else
{
size_t x_595; size_t x_596; uint8_t x_597; 
x_595 = lean_ptr_addr(x_567);
lean_dec(x_567);
x_596 = lean_ptr_addr(x_587);
x_597 = lean_usize_dec_eq(x_595, x_596);
if (x_597 == 0)
{
lean_object* x_598; lean_object* x_599; 
lean_dec(x_589);
x_598 = l_Lean_Expr_lam___override(x_565, x_570, x_587, x_568);
x_599 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_599, 0, x_598);
lean_ctor_set(x_599, 1, x_588);
return x_599;
}
else
{
uint8_t x_600; 
x_600 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_568, x_568);
if (x_600 == 0)
{
lean_object* x_601; lean_object* x_602; 
lean_dec(x_589);
x_601 = l_Lean_Expr_lam___override(x_565, x_570, x_587, x_568);
x_602 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_602, 0, x_601);
lean_ctor_set(x_602, 1, x_588);
return x_602;
}
else
{
lean_object* x_603; 
lean_dec(x_587);
lean_dec(x_570);
lean_dec(x_565);
x_603 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_603, 0, x_589);
lean_ctor_set(x_603, 1, x_588);
return x_603;
}
}
}
}
}
else
{
uint8_t x_604; 
lean_dec(x_570);
lean_dec(x_567);
lean_dec(x_566);
lean_dec(x_565);
x_604 = !lean_is_exclusive(x_573);
if (x_604 == 0)
{
return x_573;
}
else
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_605 = lean_ctor_get(x_573, 0);
x_606 = lean_ctor_get(x_573, 1);
lean_inc(x_606);
lean_inc(x_605);
lean_dec(x_573);
x_607 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_607, 0, x_605);
lean_ctor_set(x_607, 1, x_606);
return x_607;
}
}
}
else
{
uint8_t x_608; 
lean_dec(x_567);
lean_dec(x_566);
lean_dec(x_565);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_608 = !lean_is_exclusive(x_569);
if (x_608 == 0)
{
return x_569;
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_609 = lean_ctor_get(x_569, 0);
x_610 = lean_ctor_get(x_569, 1);
lean_inc(x_610);
lean_inc(x_609);
lean_dec(x_569);
x_611 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_611, 0, x_609);
lean_ctor_set(x_611, 1, x_610);
return x_611;
}
}
}
case 7:
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; uint8_t x_616; lean_object* x_617; 
x_612 = lean_ctor_get(x_525, 1);
lean_inc(x_612);
lean_dec(x_525);
x_613 = lean_ctor_get(x_5, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_5, 1);
lean_inc(x_614);
x_615 = lean_ctor_get(x_5, 2);
lean_inc(x_615);
x_616 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_614);
lean_inc(x_1);
x_617 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_614, x_6, x_7, x_8, x_9, x_10, x_11, x_612);
if (lean_obj_tag(x_617) == 0)
{
lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_618 = lean_ctor_get(x_617, 0);
lean_inc(x_618);
x_619 = lean_ctor_get(x_617, 1);
lean_inc(x_619);
lean_dec(x_617);
x_620 = lean_nat_add(x_6, x_513);
lean_dec(x_6);
lean_inc(x_615);
x_621 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_615, x_620, x_7, x_8, x_9, x_10, x_11, x_619);
if (lean_obj_tag(x_621) == 0)
{
uint8_t x_622; 
x_622 = !lean_is_exclusive(x_621);
if (x_622 == 0)
{
lean_object* x_623; lean_object* x_624; size_t x_625; size_t x_626; uint8_t x_627; 
x_623 = lean_ctor_get(x_621, 0);
lean_inc(x_615);
lean_inc(x_614);
lean_inc(x_613);
x_624 = l_Lean_Expr_forallE___override(x_613, x_614, x_615, x_616);
x_625 = lean_ptr_addr(x_614);
lean_dec(x_614);
x_626 = lean_ptr_addr(x_618);
x_627 = lean_usize_dec_eq(x_625, x_626);
if (x_627 == 0)
{
lean_object* x_628; 
lean_dec(x_624);
lean_dec(x_615);
x_628 = l_Lean_Expr_forallE___override(x_613, x_618, x_623, x_616);
lean_ctor_set(x_621, 0, x_628);
return x_621;
}
else
{
size_t x_629; size_t x_630; uint8_t x_631; 
x_629 = lean_ptr_addr(x_615);
lean_dec(x_615);
x_630 = lean_ptr_addr(x_623);
x_631 = lean_usize_dec_eq(x_629, x_630);
if (x_631 == 0)
{
lean_object* x_632; 
lean_dec(x_624);
x_632 = l_Lean_Expr_forallE___override(x_613, x_618, x_623, x_616);
lean_ctor_set(x_621, 0, x_632);
return x_621;
}
else
{
uint8_t x_633; 
x_633 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_616, x_616);
if (x_633 == 0)
{
lean_object* x_634; 
lean_dec(x_624);
x_634 = l_Lean_Expr_forallE___override(x_613, x_618, x_623, x_616);
lean_ctor_set(x_621, 0, x_634);
return x_621;
}
else
{
lean_dec(x_623);
lean_dec(x_618);
lean_dec(x_613);
lean_ctor_set(x_621, 0, x_624);
return x_621;
}
}
}
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; size_t x_638; size_t x_639; uint8_t x_640; 
x_635 = lean_ctor_get(x_621, 0);
x_636 = lean_ctor_get(x_621, 1);
lean_inc(x_636);
lean_inc(x_635);
lean_dec(x_621);
lean_inc(x_615);
lean_inc(x_614);
lean_inc(x_613);
x_637 = l_Lean_Expr_forallE___override(x_613, x_614, x_615, x_616);
x_638 = lean_ptr_addr(x_614);
lean_dec(x_614);
x_639 = lean_ptr_addr(x_618);
x_640 = lean_usize_dec_eq(x_638, x_639);
if (x_640 == 0)
{
lean_object* x_641; lean_object* x_642; 
lean_dec(x_637);
lean_dec(x_615);
x_641 = l_Lean_Expr_forallE___override(x_613, x_618, x_635, x_616);
x_642 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_642, 0, x_641);
lean_ctor_set(x_642, 1, x_636);
return x_642;
}
else
{
size_t x_643; size_t x_644; uint8_t x_645; 
x_643 = lean_ptr_addr(x_615);
lean_dec(x_615);
x_644 = lean_ptr_addr(x_635);
x_645 = lean_usize_dec_eq(x_643, x_644);
if (x_645 == 0)
{
lean_object* x_646; lean_object* x_647; 
lean_dec(x_637);
x_646 = l_Lean_Expr_forallE___override(x_613, x_618, x_635, x_616);
x_647 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_647, 0, x_646);
lean_ctor_set(x_647, 1, x_636);
return x_647;
}
else
{
uint8_t x_648; 
x_648 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_616, x_616);
if (x_648 == 0)
{
lean_object* x_649; lean_object* x_650; 
lean_dec(x_637);
x_649 = l_Lean_Expr_forallE___override(x_613, x_618, x_635, x_616);
x_650 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_650, 0, x_649);
lean_ctor_set(x_650, 1, x_636);
return x_650;
}
else
{
lean_object* x_651; 
lean_dec(x_635);
lean_dec(x_618);
lean_dec(x_613);
x_651 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_651, 0, x_637);
lean_ctor_set(x_651, 1, x_636);
return x_651;
}
}
}
}
}
else
{
uint8_t x_652; 
lean_dec(x_618);
lean_dec(x_615);
lean_dec(x_614);
lean_dec(x_613);
x_652 = !lean_is_exclusive(x_621);
if (x_652 == 0)
{
return x_621;
}
else
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_653 = lean_ctor_get(x_621, 0);
x_654 = lean_ctor_get(x_621, 1);
lean_inc(x_654);
lean_inc(x_653);
lean_dec(x_621);
x_655 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_655, 0, x_653);
lean_ctor_set(x_655, 1, x_654);
return x_655;
}
}
}
else
{
uint8_t x_656; 
lean_dec(x_615);
lean_dec(x_614);
lean_dec(x_613);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_656 = !lean_is_exclusive(x_617);
if (x_656 == 0)
{
return x_617;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_657 = lean_ctor_get(x_617, 0);
x_658 = lean_ctor_get(x_617, 1);
lean_inc(x_658);
lean_inc(x_657);
lean_dec(x_617);
x_659 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_659, 0, x_657);
lean_ctor_set(x_659, 1, x_658);
return x_659;
}
}
}
case 8:
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; uint8_t x_665; lean_object* x_666; 
x_660 = lean_ctor_get(x_525, 1);
lean_inc(x_660);
lean_dec(x_525);
x_661 = lean_ctor_get(x_5, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_5, 1);
lean_inc(x_662);
x_663 = lean_ctor_get(x_5, 2);
lean_inc(x_663);
x_664 = lean_ctor_get(x_5, 3);
lean_inc(x_664);
x_665 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_662);
lean_inc(x_1);
x_666 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_662, x_6, x_7, x_8, x_9, x_10, x_11, x_660);
if (lean_obj_tag(x_666) == 0)
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_667 = lean_ctor_get(x_666, 0);
lean_inc(x_667);
x_668 = lean_ctor_get(x_666, 1);
lean_inc(x_668);
lean_dec(x_666);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_663);
lean_inc(x_1);
x_669 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_663, x_6, x_7, x_8, x_9, x_10, x_11, x_668);
if (lean_obj_tag(x_669) == 0)
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; 
x_670 = lean_ctor_get(x_669, 0);
lean_inc(x_670);
x_671 = lean_ctor_get(x_669, 1);
lean_inc(x_671);
lean_dec(x_669);
x_672 = lean_nat_add(x_6, x_513);
lean_dec(x_6);
lean_inc(x_664);
x_673 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_664, x_672, x_7, x_8, x_9, x_10, x_11, x_671);
if (lean_obj_tag(x_673) == 0)
{
uint8_t x_674; 
x_674 = !lean_is_exclusive(x_673);
if (x_674 == 0)
{
lean_object* x_675; size_t x_676; size_t x_677; uint8_t x_678; 
x_675 = lean_ctor_get(x_673, 0);
x_676 = lean_ptr_addr(x_662);
lean_dec(x_662);
x_677 = lean_ptr_addr(x_667);
x_678 = lean_usize_dec_eq(x_676, x_677);
if (x_678 == 0)
{
lean_object* x_679; 
lean_dec(x_664);
lean_dec(x_663);
lean_dec(x_5);
x_679 = l_Lean_Expr_letE___override(x_661, x_667, x_670, x_675, x_665);
lean_ctor_set(x_673, 0, x_679);
return x_673;
}
else
{
size_t x_680; size_t x_681; uint8_t x_682; 
x_680 = lean_ptr_addr(x_663);
lean_dec(x_663);
x_681 = lean_ptr_addr(x_670);
x_682 = lean_usize_dec_eq(x_680, x_681);
if (x_682 == 0)
{
lean_object* x_683; 
lean_dec(x_664);
lean_dec(x_5);
x_683 = l_Lean_Expr_letE___override(x_661, x_667, x_670, x_675, x_665);
lean_ctor_set(x_673, 0, x_683);
return x_673;
}
else
{
size_t x_684; size_t x_685; uint8_t x_686; 
x_684 = lean_ptr_addr(x_664);
lean_dec(x_664);
x_685 = lean_ptr_addr(x_675);
x_686 = lean_usize_dec_eq(x_684, x_685);
if (x_686 == 0)
{
lean_object* x_687; 
lean_dec(x_5);
x_687 = l_Lean_Expr_letE___override(x_661, x_667, x_670, x_675, x_665);
lean_ctor_set(x_673, 0, x_687);
return x_673;
}
else
{
lean_dec(x_675);
lean_dec(x_670);
lean_dec(x_667);
lean_dec(x_661);
lean_ctor_set(x_673, 0, x_5);
return x_673;
}
}
}
}
else
{
lean_object* x_688; lean_object* x_689; size_t x_690; size_t x_691; uint8_t x_692; 
x_688 = lean_ctor_get(x_673, 0);
x_689 = lean_ctor_get(x_673, 1);
lean_inc(x_689);
lean_inc(x_688);
lean_dec(x_673);
x_690 = lean_ptr_addr(x_662);
lean_dec(x_662);
x_691 = lean_ptr_addr(x_667);
x_692 = lean_usize_dec_eq(x_690, x_691);
if (x_692 == 0)
{
lean_object* x_693; lean_object* x_694; 
lean_dec(x_664);
lean_dec(x_663);
lean_dec(x_5);
x_693 = l_Lean_Expr_letE___override(x_661, x_667, x_670, x_688, x_665);
x_694 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_694, 0, x_693);
lean_ctor_set(x_694, 1, x_689);
return x_694;
}
else
{
size_t x_695; size_t x_696; uint8_t x_697; 
x_695 = lean_ptr_addr(x_663);
lean_dec(x_663);
x_696 = lean_ptr_addr(x_670);
x_697 = lean_usize_dec_eq(x_695, x_696);
if (x_697 == 0)
{
lean_object* x_698; lean_object* x_699; 
lean_dec(x_664);
lean_dec(x_5);
x_698 = l_Lean_Expr_letE___override(x_661, x_667, x_670, x_688, x_665);
x_699 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_699, 0, x_698);
lean_ctor_set(x_699, 1, x_689);
return x_699;
}
else
{
size_t x_700; size_t x_701; uint8_t x_702; 
x_700 = lean_ptr_addr(x_664);
lean_dec(x_664);
x_701 = lean_ptr_addr(x_688);
x_702 = lean_usize_dec_eq(x_700, x_701);
if (x_702 == 0)
{
lean_object* x_703; lean_object* x_704; 
lean_dec(x_5);
x_703 = l_Lean_Expr_letE___override(x_661, x_667, x_670, x_688, x_665);
x_704 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_704, 0, x_703);
lean_ctor_set(x_704, 1, x_689);
return x_704;
}
else
{
lean_object* x_705; 
lean_dec(x_688);
lean_dec(x_670);
lean_dec(x_667);
lean_dec(x_661);
x_705 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_705, 0, x_5);
lean_ctor_set(x_705, 1, x_689);
return x_705;
}
}
}
}
}
else
{
uint8_t x_706; 
lean_dec(x_670);
lean_dec(x_667);
lean_dec(x_664);
lean_dec(x_663);
lean_dec(x_662);
lean_dec(x_661);
lean_dec(x_5);
x_706 = !lean_is_exclusive(x_673);
if (x_706 == 0)
{
return x_673;
}
else
{
lean_object* x_707; lean_object* x_708; lean_object* x_709; 
x_707 = lean_ctor_get(x_673, 0);
x_708 = lean_ctor_get(x_673, 1);
lean_inc(x_708);
lean_inc(x_707);
lean_dec(x_673);
x_709 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_709, 0, x_707);
lean_ctor_set(x_709, 1, x_708);
return x_709;
}
}
}
else
{
uint8_t x_710; 
lean_dec(x_667);
lean_dec(x_664);
lean_dec(x_663);
lean_dec(x_662);
lean_dec(x_661);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_710 = !lean_is_exclusive(x_669);
if (x_710 == 0)
{
return x_669;
}
else
{
lean_object* x_711; lean_object* x_712; lean_object* x_713; 
x_711 = lean_ctor_get(x_669, 0);
x_712 = lean_ctor_get(x_669, 1);
lean_inc(x_712);
lean_inc(x_711);
lean_dec(x_669);
x_713 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_713, 0, x_711);
lean_ctor_set(x_713, 1, x_712);
return x_713;
}
}
}
else
{
uint8_t x_714; 
lean_dec(x_664);
lean_dec(x_663);
lean_dec(x_662);
lean_dec(x_661);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_714 = !lean_is_exclusive(x_666);
if (x_714 == 0)
{
return x_666;
}
else
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; 
x_715 = lean_ctor_get(x_666, 0);
x_716 = lean_ctor_get(x_666, 1);
lean_inc(x_716);
lean_inc(x_715);
lean_dec(x_666);
x_717 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_717, 0, x_715);
lean_ctor_set(x_717, 1, x_716);
return x_717;
}
}
}
case 10:
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; 
x_718 = lean_ctor_get(x_525, 1);
lean_inc(x_718);
lean_dec(x_525);
x_719 = lean_ctor_get(x_5, 0);
lean_inc(x_719);
x_720 = lean_ctor_get(x_5, 1);
lean_inc(x_720);
lean_inc(x_720);
x_721 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_720, x_6, x_7, x_8, x_9, x_10, x_11, x_718);
if (lean_obj_tag(x_721) == 0)
{
uint8_t x_722; 
x_722 = !lean_is_exclusive(x_721);
if (x_722 == 0)
{
lean_object* x_723; size_t x_724; size_t x_725; uint8_t x_726; 
x_723 = lean_ctor_get(x_721, 0);
x_724 = lean_ptr_addr(x_720);
lean_dec(x_720);
x_725 = lean_ptr_addr(x_723);
x_726 = lean_usize_dec_eq(x_724, x_725);
if (x_726 == 0)
{
lean_object* x_727; 
lean_dec(x_5);
x_727 = l_Lean_Expr_mdata___override(x_719, x_723);
lean_ctor_set(x_721, 0, x_727);
return x_721;
}
else
{
lean_dec(x_723);
lean_dec(x_719);
lean_ctor_set(x_721, 0, x_5);
return x_721;
}
}
else
{
lean_object* x_728; lean_object* x_729; size_t x_730; size_t x_731; uint8_t x_732; 
x_728 = lean_ctor_get(x_721, 0);
x_729 = lean_ctor_get(x_721, 1);
lean_inc(x_729);
lean_inc(x_728);
lean_dec(x_721);
x_730 = lean_ptr_addr(x_720);
lean_dec(x_720);
x_731 = lean_ptr_addr(x_728);
x_732 = lean_usize_dec_eq(x_730, x_731);
if (x_732 == 0)
{
lean_object* x_733; lean_object* x_734; 
lean_dec(x_5);
x_733 = l_Lean_Expr_mdata___override(x_719, x_728);
x_734 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_734, 0, x_733);
lean_ctor_set(x_734, 1, x_729);
return x_734;
}
else
{
lean_object* x_735; 
lean_dec(x_728);
lean_dec(x_719);
x_735 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_735, 0, x_5);
lean_ctor_set(x_735, 1, x_729);
return x_735;
}
}
}
else
{
uint8_t x_736; 
lean_dec(x_720);
lean_dec(x_719);
lean_dec(x_5);
x_736 = !lean_is_exclusive(x_721);
if (x_736 == 0)
{
return x_721;
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; 
x_737 = lean_ctor_get(x_721, 0);
x_738 = lean_ctor_get(x_721, 1);
lean_inc(x_738);
lean_inc(x_737);
lean_dec(x_721);
x_739 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_739, 0, x_737);
lean_ctor_set(x_739, 1, x_738);
return x_739;
}
}
}
case 11:
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; 
x_740 = lean_ctor_get(x_525, 1);
lean_inc(x_740);
lean_dec(x_525);
x_741 = lean_ctor_get(x_5, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_5, 1);
lean_inc(x_742);
x_743 = lean_ctor_get(x_5, 2);
lean_inc(x_743);
lean_inc(x_743);
x_744 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_743, x_6, x_7, x_8, x_9, x_10, x_11, x_740);
if (lean_obj_tag(x_744) == 0)
{
uint8_t x_745; 
x_745 = !lean_is_exclusive(x_744);
if (x_745 == 0)
{
lean_object* x_746; size_t x_747; size_t x_748; uint8_t x_749; 
x_746 = lean_ctor_get(x_744, 0);
x_747 = lean_ptr_addr(x_743);
lean_dec(x_743);
x_748 = lean_ptr_addr(x_746);
x_749 = lean_usize_dec_eq(x_747, x_748);
if (x_749 == 0)
{
lean_object* x_750; 
lean_dec(x_5);
x_750 = l_Lean_Expr_proj___override(x_741, x_742, x_746);
lean_ctor_set(x_744, 0, x_750);
return x_744;
}
else
{
lean_dec(x_746);
lean_dec(x_742);
lean_dec(x_741);
lean_ctor_set(x_744, 0, x_5);
return x_744;
}
}
else
{
lean_object* x_751; lean_object* x_752; size_t x_753; size_t x_754; uint8_t x_755; 
x_751 = lean_ctor_get(x_744, 0);
x_752 = lean_ctor_get(x_744, 1);
lean_inc(x_752);
lean_inc(x_751);
lean_dec(x_744);
x_753 = lean_ptr_addr(x_743);
lean_dec(x_743);
x_754 = lean_ptr_addr(x_751);
x_755 = lean_usize_dec_eq(x_753, x_754);
if (x_755 == 0)
{
lean_object* x_756; lean_object* x_757; 
lean_dec(x_5);
x_756 = l_Lean_Expr_proj___override(x_741, x_742, x_751);
x_757 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_757, 0, x_756);
lean_ctor_set(x_757, 1, x_752);
return x_757;
}
else
{
lean_object* x_758; 
lean_dec(x_751);
lean_dec(x_742);
lean_dec(x_741);
x_758 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_758, 0, x_5);
lean_ctor_set(x_758, 1, x_752);
return x_758;
}
}
}
else
{
uint8_t x_759; 
lean_dec(x_743);
lean_dec(x_742);
lean_dec(x_741);
lean_dec(x_5);
x_759 = !lean_is_exclusive(x_744);
if (x_759 == 0)
{
return x_744;
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; 
x_760 = lean_ctor_get(x_744, 0);
x_761 = lean_ctor_get(x_744, 1);
lean_inc(x_761);
lean_inc(x_760);
lean_dec(x_744);
x_762 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_762, 0, x_760);
lean_ctor_set(x_762, 1, x_761);
return x_762;
}
}
}
default: 
{
uint8_t x_763; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_763 = !lean_is_exclusive(x_525);
if (x_763 == 0)
{
lean_object* x_764; 
x_764 = lean_ctor_get(x_525, 0);
lean_dec(x_764);
lean_ctor_set(x_525, 0, x_5);
return x_525;
}
else
{
lean_object* x_765; lean_object* x_766; 
x_765 = lean_ctor_get(x_525, 1);
lean_inc(x_765);
lean_dec(x_525);
x_766 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_766, 0, x_5);
lean_ctor_set(x_766, 1, x_765);
return x_766;
}
}
}
}
else
{
lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; 
x_767 = lean_ctor_get(x_521, 1);
x_768 = lean_ctor_get(x_521, 2);
x_769 = lean_ctor_get(x_521, 3);
x_770 = lean_ctor_get(x_521, 4);
lean_inc(x_770);
lean_inc(x_769);
lean_inc(x_768);
lean_inc(x_767);
lean_dec(x_521);
x_771 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_771, 0, x_261);
lean_ctor_set(x_771, 1, x_767);
lean_ctor_set(x_771, 2, x_768);
lean_ctor_set(x_771, 3, x_769);
lean_ctor_set(x_771, 4, x_770);
x_772 = lean_st_ref_set(x_9, x_771, x_522);
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_773 = lean_ctor_get(x_772, 1);
lean_inc(x_773);
lean_dec(x_772);
x_774 = lean_ctor_get(x_5, 0);
lean_inc(x_774);
x_775 = lean_ctor_get(x_5, 1);
lean_inc(x_775);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_774);
lean_inc(x_1);
x_776 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_774, x_6, x_7, x_8, x_9, x_10, x_11, x_773);
if (lean_obj_tag(x_776) == 0)
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; 
x_777 = lean_ctor_get(x_776, 0);
lean_inc(x_777);
x_778 = lean_ctor_get(x_776, 1);
lean_inc(x_778);
lean_dec(x_776);
lean_inc(x_775);
x_779 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_775, x_6, x_7, x_8, x_9, x_10, x_11, x_778);
if (lean_obj_tag(x_779) == 0)
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; size_t x_783; size_t x_784; uint8_t x_785; 
x_780 = lean_ctor_get(x_779, 0);
lean_inc(x_780);
x_781 = lean_ctor_get(x_779, 1);
lean_inc(x_781);
if (lean_is_exclusive(x_779)) {
 lean_ctor_release(x_779, 0);
 lean_ctor_release(x_779, 1);
 x_782 = x_779;
} else {
 lean_dec_ref(x_779);
 x_782 = lean_box(0);
}
x_783 = lean_ptr_addr(x_774);
lean_dec(x_774);
x_784 = lean_ptr_addr(x_777);
x_785 = lean_usize_dec_eq(x_783, x_784);
if (x_785 == 0)
{
lean_object* x_786; lean_object* x_787; 
lean_dec(x_775);
lean_dec(x_5);
x_786 = l_Lean_Expr_app___override(x_777, x_780);
if (lean_is_scalar(x_782)) {
 x_787 = lean_alloc_ctor(0, 2, 0);
} else {
 x_787 = x_782;
}
lean_ctor_set(x_787, 0, x_786);
lean_ctor_set(x_787, 1, x_781);
return x_787;
}
else
{
size_t x_788; size_t x_789; uint8_t x_790; 
x_788 = lean_ptr_addr(x_775);
lean_dec(x_775);
x_789 = lean_ptr_addr(x_780);
x_790 = lean_usize_dec_eq(x_788, x_789);
if (x_790 == 0)
{
lean_object* x_791; lean_object* x_792; 
lean_dec(x_5);
x_791 = l_Lean_Expr_app___override(x_777, x_780);
if (lean_is_scalar(x_782)) {
 x_792 = lean_alloc_ctor(0, 2, 0);
} else {
 x_792 = x_782;
}
lean_ctor_set(x_792, 0, x_791);
lean_ctor_set(x_792, 1, x_781);
return x_792;
}
else
{
lean_object* x_793; 
lean_dec(x_780);
lean_dec(x_777);
if (lean_is_scalar(x_782)) {
 x_793 = lean_alloc_ctor(0, 2, 0);
} else {
 x_793 = x_782;
}
lean_ctor_set(x_793, 0, x_5);
lean_ctor_set(x_793, 1, x_781);
return x_793;
}
}
}
else
{
lean_object* x_794; lean_object* x_795; lean_object* x_796; lean_object* x_797; 
lean_dec(x_777);
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_5);
x_794 = lean_ctor_get(x_779, 0);
lean_inc(x_794);
x_795 = lean_ctor_get(x_779, 1);
lean_inc(x_795);
if (lean_is_exclusive(x_779)) {
 lean_ctor_release(x_779, 0);
 lean_ctor_release(x_779, 1);
 x_796 = x_779;
} else {
 lean_dec_ref(x_779);
 x_796 = lean_box(0);
}
if (lean_is_scalar(x_796)) {
 x_797 = lean_alloc_ctor(1, 2, 0);
} else {
 x_797 = x_796;
}
lean_ctor_set(x_797, 0, x_794);
lean_ctor_set(x_797, 1, x_795);
return x_797;
}
}
else
{
lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; 
lean_dec(x_775);
lean_dec(x_774);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_798 = lean_ctor_get(x_776, 0);
lean_inc(x_798);
x_799 = lean_ctor_get(x_776, 1);
lean_inc(x_799);
if (lean_is_exclusive(x_776)) {
 lean_ctor_release(x_776, 0);
 lean_ctor_release(x_776, 1);
 x_800 = x_776;
} else {
 lean_dec_ref(x_776);
 x_800 = lean_box(0);
}
if (lean_is_scalar(x_800)) {
 x_801 = lean_alloc_ctor(1, 2, 0);
} else {
 x_801 = x_800;
}
lean_ctor_set(x_801, 0, x_798);
lean_ctor_set(x_801, 1, x_799);
return x_801;
}
}
case 6:
{
lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; uint8_t x_806; lean_object* x_807; 
x_802 = lean_ctor_get(x_772, 1);
lean_inc(x_802);
lean_dec(x_772);
x_803 = lean_ctor_get(x_5, 0);
lean_inc(x_803);
x_804 = lean_ctor_get(x_5, 1);
lean_inc(x_804);
x_805 = lean_ctor_get(x_5, 2);
lean_inc(x_805);
x_806 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_804);
lean_inc(x_1);
x_807 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_804, x_6, x_7, x_8, x_9, x_10, x_11, x_802);
if (lean_obj_tag(x_807) == 0)
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_808 = lean_ctor_get(x_807, 0);
lean_inc(x_808);
x_809 = lean_ctor_get(x_807, 1);
lean_inc(x_809);
lean_dec(x_807);
x_810 = lean_nat_add(x_6, x_513);
lean_dec(x_6);
lean_inc(x_805);
x_811 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_805, x_810, x_7, x_8, x_9, x_10, x_11, x_809);
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_812; lean_object* x_813; lean_object* x_814; lean_object* x_815; size_t x_816; size_t x_817; uint8_t x_818; 
x_812 = lean_ctor_get(x_811, 0);
lean_inc(x_812);
x_813 = lean_ctor_get(x_811, 1);
lean_inc(x_813);
if (lean_is_exclusive(x_811)) {
 lean_ctor_release(x_811, 0);
 lean_ctor_release(x_811, 1);
 x_814 = x_811;
} else {
 lean_dec_ref(x_811);
 x_814 = lean_box(0);
}
lean_inc(x_805);
lean_inc(x_804);
lean_inc(x_803);
x_815 = l_Lean_Expr_lam___override(x_803, x_804, x_805, x_806);
x_816 = lean_ptr_addr(x_804);
lean_dec(x_804);
x_817 = lean_ptr_addr(x_808);
x_818 = lean_usize_dec_eq(x_816, x_817);
if (x_818 == 0)
{
lean_object* x_819; lean_object* x_820; 
lean_dec(x_815);
lean_dec(x_805);
x_819 = l_Lean_Expr_lam___override(x_803, x_808, x_812, x_806);
if (lean_is_scalar(x_814)) {
 x_820 = lean_alloc_ctor(0, 2, 0);
} else {
 x_820 = x_814;
}
lean_ctor_set(x_820, 0, x_819);
lean_ctor_set(x_820, 1, x_813);
return x_820;
}
else
{
size_t x_821; size_t x_822; uint8_t x_823; 
x_821 = lean_ptr_addr(x_805);
lean_dec(x_805);
x_822 = lean_ptr_addr(x_812);
x_823 = lean_usize_dec_eq(x_821, x_822);
if (x_823 == 0)
{
lean_object* x_824; lean_object* x_825; 
lean_dec(x_815);
x_824 = l_Lean_Expr_lam___override(x_803, x_808, x_812, x_806);
if (lean_is_scalar(x_814)) {
 x_825 = lean_alloc_ctor(0, 2, 0);
} else {
 x_825 = x_814;
}
lean_ctor_set(x_825, 0, x_824);
lean_ctor_set(x_825, 1, x_813);
return x_825;
}
else
{
uint8_t x_826; 
x_826 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_806, x_806);
if (x_826 == 0)
{
lean_object* x_827; lean_object* x_828; 
lean_dec(x_815);
x_827 = l_Lean_Expr_lam___override(x_803, x_808, x_812, x_806);
if (lean_is_scalar(x_814)) {
 x_828 = lean_alloc_ctor(0, 2, 0);
} else {
 x_828 = x_814;
}
lean_ctor_set(x_828, 0, x_827);
lean_ctor_set(x_828, 1, x_813);
return x_828;
}
else
{
lean_object* x_829; 
lean_dec(x_812);
lean_dec(x_808);
lean_dec(x_803);
if (lean_is_scalar(x_814)) {
 x_829 = lean_alloc_ctor(0, 2, 0);
} else {
 x_829 = x_814;
}
lean_ctor_set(x_829, 0, x_815);
lean_ctor_set(x_829, 1, x_813);
return x_829;
}
}
}
}
else
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; 
lean_dec(x_808);
lean_dec(x_805);
lean_dec(x_804);
lean_dec(x_803);
x_830 = lean_ctor_get(x_811, 0);
lean_inc(x_830);
x_831 = lean_ctor_get(x_811, 1);
lean_inc(x_831);
if (lean_is_exclusive(x_811)) {
 lean_ctor_release(x_811, 0);
 lean_ctor_release(x_811, 1);
 x_832 = x_811;
} else {
 lean_dec_ref(x_811);
 x_832 = lean_box(0);
}
if (lean_is_scalar(x_832)) {
 x_833 = lean_alloc_ctor(1, 2, 0);
} else {
 x_833 = x_832;
}
lean_ctor_set(x_833, 0, x_830);
lean_ctor_set(x_833, 1, x_831);
return x_833;
}
}
else
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
lean_dec(x_805);
lean_dec(x_804);
lean_dec(x_803);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_834 = lean_ctor_get(x_807, 0);
lean_inc(x_834);
x_835 = lean_ctor_get(x_807, 1);
lean_inc(x_835);
if (lean_is_exclusive(x_807)) {
 lean_ctor_release(x_807, 0);
 lean_ctor_release(x_807, 1);
 x_836 = x_807;
} else {
 lean_dec_ref(x_807);
 x_836 = lean_box(0);
}
if (lean_is_scalar(x_836)) {
 x_837 = lean_alloc_ctor(1, 2, 0);
} else {
 x_837 = x_836;
}
lean_ctor_set(x_837, 0, x_834);
lean_ctor_set(x_837, 1, x_835);
return x_837;
}
}
case 7:
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; uint8_t x_842; lean_object* x_843; 
x_838 = lean_ctor_get(x_772, 1);
lean_inc(x_838);
lean_dec(x_772);
x_839 = lean_ctor_get(x_5, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_5, 1);
lean_inc(x_840);
x_841 = lean_ctor_get(x_5, 2);
lean_inc(x_841);
x_842 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_840);
lean_inc(x_1);
x_843 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_840, x_6, x_7, x_8, x_9, x_10, x_11, x_838);
if (lean_obj_tag(x_843) == 0)
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; 
x_844 = lean_ctor_get(x_843, 0);
lean_inc(x_844);
x_845 = lean_ctor_get(x_843, 1);
lean_inc(x_845);
lean_dec(x_843);
x_846 = lean_nat_add(x_6, x_513);
lean_dec(x_6);
lean_inc(x_841);
x_847 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_841, x_846, x_7, x_8, x_9, x_10, x_11, x_845);
if (lean_obj_tag(x_847) == 0)
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; size_t x_852; size_t x_853; uint8_t x_854; 
x_848 = lean_ctor_get(x_847, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_847, 1);
lean_inc(x_849);
if (lean_is_exclusive(x_847)) {
 lean_ctor_release(x_847, 0);
 lean_ctor_release(x_847, 1);
 x_850 = x_847;
} else {
 lean_dec_ref(x_847);
 x_850 = lean_box(0);
}
lean_inc(x_841);
lean_inc(x_840);
lean_inc(x_839);
x_851 = l_Lean_Expr_forallE___override(x_839, x_840, x_841, x_842);
x_852 = lean_ptr_addr(x_840);
lean_dec(x_840);
x_853 = lean_ptr_addr(x_844);
x_854 = lean_usize_dec_eq(x_852, x_853);
if (x_854 == 0)
{
lean_object* x_855; lean_object* x_856; 
lean_dec(x_851);
lean_dec(x_841);
x_855 = l_Lean_Expr_forallE___override(x_839, x_844, x_848, x_842);
if (lean_is_scalar(x_850)) {
 x_856 = lean_alloc_ctor(0, 2, 0);
} else {
 x_856 = x_850;
}
lean_ctor_set(x_856, 0, x_855);
lean_ctor_set(x_856, 1, x_849);
return x_856;
}
else
{
size_t x_857; size_t x_858; uint8_t x_859; 
x_857 = lean_ptr_addr(x_841);
lean_dec(x_841);
x_858 = lean_ptr_addr(x_848);
x_859 = lean_usize_dec_eq(x_857, x_858);
if (x_859 == 0)
{
lean_object* x_860; lean_object* x_861; 
lean_dec(x_851);
x_860 = l_Lean_Expr_forallE___override(x_839, x_844, x_848, x_842);
if (lean_is_scalar(x_850)) {
 x_861 = lean_alloc_ctor(0, 2, 0);
} else {
 x_861 = x_850;
}
lean_ctor_set(x_861, 0, x_860);
lean_ctor_set(x_861, 1, x_849);
return x_861;
}
else
{
uint8_t x_862; 
x_862 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_842, x_842);
if (x_862 == 0)
{
lean_object* x_863; lean_object* x_864; 
lean_dec(x_851);
x_863 = l_Lean_Expr_forallE___override(x_839, x_844, x_848, x_842);
if (lean_is_scalar(x_850)) {
 x_864 = lean_alloc_ctor(0, 2, 0);
} else {
 x_864 = x_850;
}
lean_ctor_set(x_864, 0, x_863);
lean_ctor_set(x_864, 1, x_849);
return x_864;
}
else
{
lean_object* x_865; 
lean_dec(x_848);
lean_dec(x_844);
lean_dec(x_839);
if (lean_is_scalar(x_850)) {
 x_865 = lean_alloc_ctor(0, 2, 0);
} else {
 x_865 = x_850;
}
lean_ctor_set(x_865, 0, x_851);
lean_ctor_set(x_865, 1, x_849);
return x_865;
}
}
}
}
else
{
lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; 
lean_dec(x_844);
lean_dec(x_841);
lean_dec(x_840);
lean_dec(x_839);
x_866 = lean_ctor_get(x_847, 0);
lean_inc(x_866);
x_867 = lean_ctor_get(x_847, 1);
lean_inc(x_867);
if (lean_is_exclusive(x_847)) {
 lean_ctor_release(x_847, 0);
 lean_ctor_release(x_847, 1);
 x_868 = x_847;
} else {
 lean_dec_ref(x_847);
 x_868 = lean_box(0);
}
if (lean_is_scalar(x_868)) {
 x_869 = lean_alloc_ctor(1, 2, 0);
} else {
 x_869 = x_868;
}
lean_ctor_set(x_869, 0, x_866);
lean_ctor_set(x_869, 1, x_867);
return x_869;
}
}
else
{
lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; 
lean_dec(x_841);
lean_dec(x_840);
lean_dec(x_839);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_870 = lean_ctor_get(x_843, 0);
lean_inc(x_870);
x_871 = lean_ctor_get(x_843, 1);
lean_inc(x_871);
if (lean_is_exclusive(x_843)) {
 lean_ctor_release(x_843, 0);
 lean_ctor_release(x_843, 1);
 x_872 = x_843;
} else {
 lean_dec_ref(x_843);
 x_872 = lean_box(0);
}
if (lean_is_scalar(x_872)) {
 x_873 = lean_alloc_ctor(1, 2, 0);
} else {
 x_873 = x_872;
}
lean_ctor_set(x_873, 0, x_870);
lean_ctor_set(x_873, 1, x_871);
return x_873;
}
}
case 8:
{
lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; uint8_t x_879; lean_object* x_880; 
x_874 = lean_ctor_get(x_772, 1);
lean_inc(x_874);
lean_dec(x_772);
x_875 = lean_ctor_get(x_5, 0);
lean_inc(x_875);
x_876 = lean_ctor_get(x_5, 1);
lean_inc(x_876);
x_877 = lean_ctor_get(x_5, 2);
lean_inc(x_877);
x_878 = lean_ctor_get(x_5, 3);
lean_inc(x_878);
x_879 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_876);
lean_inc(x_1);
x_880 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_876, x_6, x_7, x_8, x_9, x_10, x_11, x_874);
if (lean_obj_tag(x_880) == 0)
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; 
x_881 = lean_ctor_get(x_880, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_880, 1);
lean_inc(x_882);
lean_dec(x_880);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_877);
lean_inc(x_1);
x_883 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_877, x_6, x_7, x_8, x_9, x_10, x_11, x_882);
if (lean_obj_tag(x_883) == 0)
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; 
x_884 = lean_ctor_get(x_883, 0);
lean_inc(x_884);
x_885 = lean_ctor_get(x_883, 1);
lean_inc(x_885);
lean_dec(x_883);
x_886 = lean_nat_add(x_6, x_513);
lean_dec(x_6);
lean_inc(x_878);
x_887 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_878, x_886, x_7, x_8, x_9, x_10, x_11, x_885);
if (lean_obj_tag(x_887) == 0)
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; size_t x_891; size_t x_892; uint8_t x_893; 
x_888 = lean_ctor_get(x_887, 0);
lean_inc(x_888);
x_889 = lean_ctor_get(x_887, 1);
lean_inc(x_889);
if (lean_is_exclusive(x_887)) {
 lean_ctor_release(x_887, 0);
 lean_ctor_release(x_887, 1);
 x_890 = x_887;
} else {
 lean_dec_ref(x_887);
 x_890 = lean_box(0);
}
x_891 = lean_ptr_addr(x_876);
lean_dec(x_876);
x_892 = lean_ptr_addr(x_881);
x_893 = lean_usize_dec_eq(x_891, x_892);
if (x_893 == 0)
{
lean_object* x_894; lean_object* x_895; 
lean_dec(x_878);
lean_dec(x_877);
lean_dec(x_5);
x_894 = l_Lean_Expr_letE___override(x_875, x_881, x_884, x_888, x_879);
if (lean_is_scalar(x_890)) {
 x_895 = lean_alloc_ctor(0, 2, 0);
} else {
 x_895 = x_890;
}
lean_ctor_set(x_895, 0, x_894);
lean_ctor_set(x_895, 1, x_889);
return x_895;
}
else
{
size_t x_896; size_t x_897; uint8_t x_898; 
x_896 = lean_ptr_addr(x_877);
lean_dec(x_877);
x_897 = lean_ptr_addr(x_884);
x_898 = lean_usize_dec_eq(x_896, x_897);
if (x_898 == 0)
{
lean_object* x_899; lean_object* x_900; 
lean_dec(x_878);
lean_dec(x_5);
x_899 = l_Lean_Expr_letE___override(x_875, x_881, x_884, x_888, x_879);
if (lean_is_scalar(x_890)) {
 x_900 = lean_alloc_ctor(0, 2, 0);
} else {
 x_900 = x_890;
}
lean_ctor_set(x_900, 0, x_899);
lean_ctor_set(x_900, 1, x_889);
return x_900;
}
else
{
size_t x_901; size_t x_902; uint8_t x_903; 
x_901 = lean_ptr_addr(x_878);
lean_dec(x_878);
x_902 = lean_ptr_addr(x_888);
x_903 = lean_usize_dec_eq(x_901, x_902);
if (x_903 == 0)
{
lean_object* x_904; lean_object* x_905; 
lean_dec(x_5);
x_904 = l_Lean_Expr_letE___override(x_875, x_881, x_884, x_888, x_879);
if (lean_is_scalar(x_890)) {
 x_905 = lean_alloc_ctor(0, 2, 0);
} else {
 x_905 = x_890;
}
lean_ctor_set(x_905, 0, x_904);
lean_ctor_set(x_905, 1, x_889);
return x_905;
}
else
{
lean_object* x_906; 
lean_dec(x_888);
lean_dec(x_884);
lean_dec(x_881);
lean_dec(x_875);
if (lean_is_scalar(x_890)) {
 x_906 = lean_alloc_ctor(0, 2, 0);
} else {
 x_906 = x_890;
}
lean_ctor_set(x_906, 0, x_5);
lean_ctor_set(x_906, 1, x_889);
return x_906;
}
}
}
}
else
{
lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; 
lean_dec(x_884);
lean_dec(x_881);
lean_dec(x_878);
lean_dec(x_877);
lean_dec(x_876);
lean_dec(x_875);
lean_dec(x_5);
x_907 = lean_ctor_get(x_887, 0);
lean_inc(x_907);
x_908 = lean_ctor_get(x_887, 1);
lean_inc(x_908);
if (lean_is_exclusive(x_887)) {
 lean_ctor_release(x_887, 0);
 lean_ctor_release(x_887, 1);
 x_909 = x_887;
} else {
 lean_dec_ref(x_887);
 x_909 = lean_box(0);
}
if (lean_is_scalar(x_909)) {
 x_910 = lean_alloc_ctor(1, 2, 0);
} else {
 x_910 = x_909;
}
lean_ctor_set(x_910, 0, x_907);
lean_ctor_set(x_910, 1, x_908);
return x_910;
}
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; 
lean_dec(x_881);
lean_dec(x_878);
lean_dec(x_877);
lean_dec(x_876);
lean_dec(x_875);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_911 = lean_ctor_get(x_883, 0);
lean_inc(x_911);
x_912 = lean_ctor_get(x_883, 1);
lean_inc(x_912);
if (lean_is_exclusive(x_883)) {
 lean_ctor_release(x_883, 0);
 lean_ctor_release(x_883, 1);
 x_913 = x_883;
} else {
 lean_dec_ref(x_883);
 x_913 = lean_box(0);
}
if (lean_is_scalar(x_913)) {
 x_914 = lean_alloc_ctor(1, 2, 0);
} else {
 x_914 = x_913;
}
lean_ctor_set(x_914, 0, x_911);
lean_ctor_set(x_914, 1, x_912);
return x_914;
}
}
else
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; 
lean_dec(x_878);
lean_dec(x_877);
lean_dec(x_876);
lean_dec(x_875);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_915 = lean_ctor_get(x_880, 0);
lean_inc(x_915);
x_916 = lean_ctor_get(x_880, 1);
lean_inc(x_916);
if (lean_is_exclusive(x_880)) {
 lean_ctor_release(x_880, 0);
 lean_ctor_release(x_880, 1);
 x_917 = x_880;
} else {
 lean_dec_ref(x_880);
 x_917 = lean_box(0);
}
if (lean_is_scalar(x_917)) {
 x_918 = lean_alloc_ctor(1, 2, 0);
} else {
 x_918 = x_917;
}
lean_ctor_set(x_918, 0, x_915);
lean_ctor_set(x_918, 1, x_916);
return x_918;
}
}
case 10:
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
x_919 = lean_ctor_get(x_772, 1);
lean_inc(x_919);
lean_dec(x_772);
x_920 = lean_ctor_get(x_5, 0);
lean_inc(x_920);
x_921 = lean_ctor_get(x_5, 1);
lean_inc(x_921);
lean_inc(x_921);
x_922 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_921, x_6, x_7, x_8, x_9, x_10, x_11, x_919);
if (lean_obj_tag(x_922) == 0)
{
lean_object* x_923; lean_object* x_924; lean_object* x_925; size_t x_926; size_t x_927; uint8_t x_928; 
x_923 = lean_ctor_get(x_922, 0);
lean_inc(x_923);
x_924 = lean_ctor_get(x_922, 1);
lean_inc(x_924);
if (lean_is_exclusive(x_922)) {
 lean_ctor_release(x_922, 0);
 lean_ctor_release(x_922, 1);
 x_925 = x_922;
} else {
 lean_dec_ref(x_922);
 x_925 = lean_box(0);
}
x_926 = lean_ptr_addr(x_921);
lean_dec(x_921);
x_927 = lean_ptr_addr(x_923);
x_928 = lean_usize_dec_eq(x_926, x_927);
if (x_928 == 0)
{
lean_object* x_929; lean_object* x_930; 
lean_dec(x_5);
x_929 = l_Lean_Expr_mdata___override(x_920, x_923);
if (lean_is_scalar(x_925)) {
 x_930 = lean_alloc_ctor(0, 2, 0);
} else {
 x_930 = x_925;
}
lean_ctor_set(x_930, 0, x_929);
lean_ctor_set(x_930, 1, x_924);
return x_930;
}
else
{
lean_object* x_931; 
lean_dec(x_923);
lean_dec(x_920);
if (lean_is_scalar(x_925)) {
 x_931 = lean_alloc_ctor(0, 2, 0);
} else {
 x_931 = x_925;
}
lean_ctor_set(x_931, 0, x_5);
lean_ctor_set(x_931, 1, x_924);
return x_931;
}
}
else
{
lean_object* x_932; lean_object* x_933; lean_object* x_934; lean_object* x_935; 
lean_dec(x_921);
lean_dec(x_920);
lean_dec(x_5);
x_932 = lean_ctor_get(x_922, 0);
lean_inc(x_932);
x_933 = lean_ctor_get(x_922, 1);
lean_inc(x_933);
if (lean_is_exclusive(x_922)) {
 lean_ctor_release(x_922, 0);
 lean_ctor_release(x_922, 1);
 x_934 = x_922;
} else {
 lean_dec_ref(x_922);
 x_934 = lean_box(0);
}
if (lean_is_scalar(x_934)) {
 x_935 = lean_alloc_ctor(1, 2, 0);
} else {
 x_935 = x_934;
}
lean_ctor_set(x_935, 0, x_932);
lean_ctor_set(x_935, 1, x_933);
return x_935;
}
}
case 11:
{
lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; 
x_936 = lean_ctor_get(x_772, 1);
lean_inc(x_936);
lean_dec(x_772);
x_937 = lean_ctor_get(x_5, 0);
lean_inc(x_937);
x_938 = lean_ctor_get(x_5, 1);
lean_inc(x_938);
x_939 = lean_ctor_get(x_5, 2);
lean_inc(x_939);
lean_inc(x_939);
x_940 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_939, x_6, x_7, x_8, x_9, x_10, x_11, x_936);
if (lean_obj_tag(x_940) == 0)
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; size_t x_944; size_t x_945; uint8_t x_946; 
x_941 = lean_ctor_get(x_940, 0);
lean_inc(x_941);
x_942 = lean_ctor_get(x_940, 1);
lean_inc(x_942);
if (lean_is_exclusive(x_940)) {
 lean_ctor_release(x_940, 0);
 lean_ctor_release(x_940, 1);
 x_943 = x_940;
} else {
 lean_dec_ref(x_940);
 x_943 = lean_box(0);
}
x_944 = lean_ptr_addr(x_939);
lean_dec(x_939);
x_945 = lean_ptr_addr(x_941);
x_946 = lean_usize_dec_eq(x_944, x_945);
if (x_946 == 0)
{
lean_object* x_947; lean_object* x_948; 
lean_dec(x_5);
x_947 = l_Lean_Expr_proj___override(x_937, x_938, x_941);
if (lean_is_scalar(x_943)) {
 x_948 = lean_alloc_ctor(0, 2, 0);
} else {
 x_948 = x_943;
}
lean_ctor_set(x_948, 0, x_947);
lean_ctor_set(x_948, 1, x_942);
return x_948;
}
else
{
lean_object* x_949; 
lean_dec(x_941);
lean_dec(x_938);
lean_dec(x_937);
if (lean_is_scalar(x_943)) {
 x_949 = lean_alloc_ctor(0, 2, 0);
} else {
 x_949 = x_943;
}
lean_ctor_set(x_949, 0, x_5);
lean_ctor_set(x_949, 1, x_942);
return x_949;
}
}
else
{
lean_object* x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; 
lean_dec(x_939);
lean_dec(x_938);
lean_dec(x_937);
lean_dec(x_5);
x_950 = lean_ctor_get(x_940, 0);
lean_inc(x_950);
x_951 = lean_ctor_get(x_940, 1);
lean_inc(x_951);
if (lean_is_exclusive(x_940)) {
 lean_ctor_release(x_940, 0);
 lean_ctor_release(x_940, 1);
 x_952 = x_940;
} else {
 lean_dec_ref(x_940);
 x_952 = lean_box(0);
}
if (lean_is_scalar(x_952)) {
 x_953 = lean_alloc_ctor(1, 2, 0);
} else {
 x_953 = x_952;
}
lean_ctor_set(x_953, 0, x_950);
lean_ctor_set(x_953, 1, x_951);
return x_953;
}
}
default: 
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_954 = lean_ctor_get(x_772, 1);
lean_inc(x_954);
if (lean_is_exclusive(x_772)) {
 lean_ctor_release(x_772, 0);
 lean_ctor_release(x_772, 1);
 x_955 = x_772;
} else {
 lean_dec_ref(x_772);
 x_955 = lean_box(0);
}
if (lean_is_scalar(x_955)) {
 x_956 = lean_alloc_ctor(0, 2, 0);
} else {
 x_956 = x_955;
}
lean_ctor_set(x_956, 0, x_5);
lean_ctor_set(x_956, 1, x_954);
return x_956;
}
}
}
}
else
{
lean_object* x_957; 
lean_dec(x_261);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_957 = l_Lean_Expr_bvar___override(x_6);
lean_ctor_set(x_515, 0, x_957);
return x_515;
}
}
else
{
lean_object* x_958; uint8_t x_959; 
x_958 = lean_ctor_get(x_515, 1);
lean_inc(x_958);
lean_dec(x_515);
x_959 = l_Lean_Meta_Occurrences_contains(x_2, x_511);
lean_dec(x_511);
if (x_959 == 0)
{
lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; 
x_960 = lean_st_ref_take(x_9, x_958);
x_961 = lean_ctor_get(x_960, 0);
lean_inc(x_961);
x_962 = lean_ctor_get(x_960, 1);
lean_inc(x_962);
lean_dec(x_960);
x_963 = lean_ctor_get(x_961, 1);
lean_inc(x_963);
x_964 = lean_ctor_get(x_961, 2);
lean_inc(x_964);
x_965 = lean_ctor_get(x_961, 3);
lean_inc(x_965);
x_966 = lean_ctor_get(x_961, 4);
lean_inc(x_966);
if (lean_is_exclusive(x_961)) {
 lean_ctor_release(x_961, 0);
 lean_ctor_release(x_961, 1);
 lean_ctor_release(x_961, 2);
 lean_ctor_release(x_961, 3);
 lean_ctor_release(x_961, 4);
 x_967 = x_961;
} else {
 lean_dec_ref(x_961);
 x_967 = lean_box(0);
}
if (lean_is_scalar(x_967)) {
 x_968 = lean_alloc_ctor(0, 5, 0);
} else {
 x_968 = x_967;
}
lean_ctor_set(x_968, 0, x_261);
lean_ctor_set(x_968, 1, x_963);
lean_ctor_set(x_968, 2, x_964);
lean_ctor_set(x_968, 3, x_965);
lean_ctor_set(x_968, 4, x_966);
x_969 = lean_st_ref_set(x_9, x_968, x_962);
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; 
x_970 = lean_ctor_get(x_969, 1);
lean_inc(x_970);
lean_dec(x_969);
x_971 = lean_ctor_get(x_5, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_5, 1);
lean_inc(x_972);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_971);
lean_inc(x_1);
x_973 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_971, x_6, x_7, x_8, x_9, x_10, x_11, x_970);
if (lean_obj_tag(x_973) == 0)
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; 
x_974 = lean_ctor_get(x_973, 0);
lean_inc(x_974);
x_975 = lean_ctor_get(x_973, 1);
lean_inc(x_975);
lean_dec(x_973);
lean_inc(x_972);
x_976 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_972, x_6, x_7, x_8, x_9, x_10, x_11, x_975);
if (lean_obj_tag(x_976) == 0)
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; size_t x_980; size_t x_981; uint8_t x_982; 
x_977 = lean_ctor_get(x_976, 0);
lean_inc(x_977);
x_978 = lean_ctor_get(x_976, 1);
lean_inc(x_978);
if (lean_is_exclusive(x_976)) {
 lean_ctor_release(x_976, 0);
 lean_ctor_release(x_976, 1);
 x_979 = x_976;
} else {
 lean_dec_ref(x_976);
 x_979 = lean_box(0);
}
x_980 = lean_ptr_addr(x_971);
lean_dec(x_971);
x_981 = lean_ptr_addr(x_974);
x_982 = lean_usize_dec_eq(x_980, x_981);
if (x_982 == 0)
{
lean_object* x_983; lean_object* x_984; 
lean_dec(x_972);
lean_dec(x_5);
x_983 = l_Lean_Expr_app___override(x_974, x_977);
if (lean_is_scalar(x_979)) {
 x_984 = lean_alloc_ctor(0, 2, 0);
} else {
 x_984 = x_979;
}
lean_ctor_set(x_984, 0, x_983);
lean_ctor_set(x_984, 1, x_978);
return x_984;
}
else
{
size_t x_985; size_t x_986; uint8_t x_987; 
x_985 = lean_ptr_addr(x_972);
lean_dec(x_972);
x_986 = lean_ptr_addr(x_977);
x_987 = lean_usize_dec_eq(x_985, x_986);
if (x_987 == 0)
{
lean_object* x_988; lean_object* x_989; 
lean_dec(x_5);
x_988 = l_Lean_Expr_app___override(x_974, x_977);
if (lean_is_scalar(x_979)) {
 x_989 = lean_alloc_ctor(0, 2, 0);
} else {
 x_989 = x_979;
}
lean_ctor_set(x_989, 0, x_988);
lean_ctor_set(x_989, 1, x_978);
return x_989;
}
else
{
lean_object* x_990; 
lean_dec(x_977);
lean_dec(x_974);
if (lean_is_scalar(x_979)) {
 x_990 = lean_alloc_ctor(0, 2, 0);
} else {
 x_990 = x_979;
}
lean_ctor_set(x_990, 0, x_5);
lean_ctor_set(x_990, 1, x_978);
return x_990;
}
}
}
else
{
lean_object* x_991; lean_object* x_992; lean_object* x_993; lean_object* x_994; 
lean_dec(x_974);
lean_dec(x_972);
lean_dec(x_971);
lean_dec(x_5);
x_991 = lean_ctor_get(x_976, 0);
lean_inc(x_991);
x_992 = lean_ctor_get(x_976, 1);
lean_inc(x_992);
if (lean_is_exclusive(x_976)) {
 lean_ctor_release(x_976, 0);
 lean_ctor_release(x_976, 1);
 x_993 = x_976;
} else {
 lean_dec_ref(x_976);
 x_993 = lean_box(0);
}
if (lean_is_scalar(x_993)) {
 x_994 = lean_alloc_ctor(1, 2, 0);
} else {
 x_994 = x_993;
}
lean_ctor_set(x_994, 0, x_991);
lean_ctor_set(x_994, 1, x_992);
return x_994;
}
}
else
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; 
lean_dec(x_972);
lean_dec(x_971);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_995 = lean_ctor_get(x_973, 0);
lean_inc(x_995);
x_996 = lean_ctor_get(x_973, 1);
lean_inc(x_996);
if (lean_is_exclusive(x_973)) {
 lean_ctor_release(x_973, 0);
 lean_ctor_release(x_973, 1);
 x_997 = x_973;
} else {
 lean_dec_ref(x_973);
 x_997 = lean_box(0);
}
if (lean_is_scalar(x_997)) {
 x_998 = lean_alloc_ctor(1, 2, 0);
} else {
 x_998 = x_997;
}
lean_ctor_set(x_998, 0, x_995);
lean_ctor_set(x_998, 1, x_996);
return x_998;
}
}
case 6:
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; uint8_t x_1003; lean_object* x_1004; 
x_999 = lean_ctor_get(x_969, 1);
lean_inc(x_999);
lean_dec(x_969);
x_1000 = lean_ctor_get(x_5, 0);
lean_inc(x_1000);
x_1001 = lean_ctor_get(x_5, 1);
lean_inc(x_1001);
x_1002 = lean_ctor_get(x_5, 2);
lean_inc(x_1002);
x_1003 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1001);
lean_inc(x_1);
x_1004 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1001, x_6, x_7, x_8, x_9, x_10, x_11, x_999);
if (lean_obj_tag(x_1004) == 0)
{
lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; 
x_1005 = lean_ctor_get(x_1004, 0);
lean_inc(x_1005);
x_1006 = lean_ctor_get(x_1004, 1);
lean_inc(x_1006);
lean_dec(x_1004);
x_1007 = lean_nat_add(x_6, x_513);
lean_dec(x_6);
lean_inc(x_1002);
x_1008 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1002, x_1007, x_7, x_8, x_9, x_10, x_11, x_1006);
if (lean_obj_tag(x_1008) == 0)
{
lean_object* x_1009; lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; size_t x_1013; size_t x_1014; uint8_t x_1015; 
x_1009 = lean_ctor_get(x_1008, 0);
lean_inc(x_1009);
x_1010 = lean_ctor_get(x_1008, 1);
lean_inc(x_1010);
if (lean_is_exclusive(x_1008)) {
 lean_ctor_release(x_1008, 0);
 lean_ctor_release(x_1008, 1);
 x_1011 = x_1008;
} else {
 lean_dec_ref(x_1008);
 x_1011 = lean_box(0);
}
lean_inc(x_1002);
lean_inc(x_1001);
lean_inc(x_1000);
x_1012 = l_Lean_Expr_lam___override(x_1000, x_1001, x_1002, x_1003);
x_1013 = lean_ptr_addr(x_1001);
lean_dec(x_1001);
x_1014 = lean_ptr_addr(x_1005);
x_1015 = lean_usize_dec_eq(x_1013, x_1014);
if (x_1015 == 0)
{
lean_object* x_1016; lean_object* x_1017; 
lean_dec(x_1012);
lean_dec(x_1002);
x_1016 = l_Lean_Expr_lam___override(x_1000, x_1005, x_1009, x_1003);
if (lean_is_scalar(x_1011)) {
 x_1017 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1017 = x_1011;
}
lean_ctor_set(x_1017, 0, x_1016);
lean_ctor_set(x_1017, 1, x_1010);
return x_1017;
}
else
{
size_t x_1018; size_t x_1019; uint8_t x_1020; 
x_1018 = lean_ptr_addr(x_1002);
lean_dec(x_1002);
x_1019 = lean_ptr_addr(x_1009);
x_1020 = lean_usize_dec_eq(x_1018, x_1019);
if (x_1020 == 0)
{
lean_object* x_1021; lean_object* x_1022; 
lean_dec(x_1012);
x_1021 = l_Lean_Expr_lam___override(x_1000, x_1005, x_1009, x_1003);
if (lean_is_scalar(x_1011)) {
 x_1022 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1022 = x_1011;
}
lean_ctor_set(x_1022, 0, x_1021);
lean_ctor_set(x_1022, 1, x_1010);
return x_1022;
}
else
{
uint8_t x_1023; 
x_1023 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_1003, x_1003);
if (x_1023 == 0)
{
lean_object* x_1024; lean_object* x_1025; 
lean_dec(x_1012);
x_1024 = l_Lean_Expr_lam___override(x_1000, x_1005, x_1009, x_1003);
if (lean_is_scalar(x_1011)) {
 x_1025 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1025 = x_1011;
}
lean_ctor_set(x_1025, 0, x_1024);
lean_ctor_set(x_1025, 1, x_1010);
return x_1025;
}
else
{
lean_object* x_1026; 
lean_dec(x_1009);
lean_dec(x_1005);
lean_dec(x_1000);
if (lean_is_scalar(x_1011)) {
 x_1026 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1026 = x_1011;
}
lean_ctor_set(x_1026, 0, x_1012);
lean_ctor_set(x_1026, 1, x_1010);
return x_1026;
}
}
}
}
else
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; 
lean_dec(x_1005);
lean_dec(x_1002);
lean_dec(x_1001);
lean_dec(x_1000);
x_1027 = lean_ctor_get(x_1008, 0);
lean_inc(x_1027);
x_1028 = lean_ctor_get(x_1008, 1);
lean_inc(x_1028);
if (lean_is_exclusive(x_1008)) {
 lean_ctor_release(x_1008, 0);
 lean_ctor_release(x_1008, 1);
 x_1029 = x_1008;
} else {
 lean_dec_ref(x_1008);
 x_1029 = lean_box(0);
}
if (lean_is_scalar(x_1029)) {
 x_1030 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1030 = x_1029;
}
lean_ctor_set(x_1030, 0, x_1027);
lean_ctor_set(x_1030, 1, x_1028);
return x_1030;
}
}
else
{
lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
lean_dec(x_1002);
lean_dec(x_1001);
lean_dec(x_1000);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1031 = lean_ctor_get(x_1004, 0);
lean_inc(x_1031);
x_1032 = lean_ctor_get(x_1004, 1);
lean_inc(x_1032);
if (lean_is_exclusive(x_1004)) {
 lean_ctor_release(x_1004, 0);
 lean_ctor_release(x_1004, 1);
 x_1033 = x_1004;
} else {
 lean_dec_ref(x_1004);
 x_1033 = lean_box(0);
}
if (lean_is_scalar(x_1033)) {
 x_1034 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1034 = x_1033;
}
lean_ctor_set(x_1034, 0, x_1031);
lean_ctor_set(x_1034, 1, x_1032);
return x_1034;
}
}
case 7:
{
lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; uint8_t x_1039; lean_object* x_1040; 
x_1035 = lean_ctor_get(x_969, 1);
lean_inc(x_1035);
lean_dec(x_969);
x_1036 = lean_ctor_get(x_5, 0);
lean_inc(x_1036);
x_1037 = lean_ctor_get(x_5, 1);
lean_inc(x_1037);
x_1038 = lean_ctor_get(x_5, 2);
lean_inc(x_1038);
x_1039 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1037);
lean_inc(x_1);
x_1040 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1037, x_6, x_7, x_8, x_9, x_10, x_11, x_1035);
if (lean_obj_tag(x_1040) == 0)
{
lean_object* x_1041; lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; 
x_1041 = lean_ctor_get(x_1040, 0);
lean_inc(x_1041);
x_1042 = lean_ctor_get(x_1040, 1);
lean_inc(x_1042);
lean_dec(x_1040);
x_1043 = lean_nat_add(x_6, x_513);
lean_dec(x_6);
lean_inc(x_1038);
x_1044 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1038, x_1043, x_7, x_8, x_9, x_10, x_11, x_1042);
if (lean_obj_tag(x_1044) == 0)
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; size_t x_1049; size_t x_1050; uint8_t x_1051; 
x_1045 = lean_ctor_get(x_1044, 0);
lean_inc(x_1045);
x_1046 = lean_ctor_get(x_1044, 1);
lean_inc(x_1046);
if (lean_is_exclusive(x_1044)) {
 lean_ctor_release(x_1044, 0);
 lean_ctor_release(x_1044, 1);
 x_1047 = x_1044;
} else {
 lean_dec_ref(x_1044);
 x_1047 = lean_box(0);
}
lean_inc(x_1038);
lean_inc(x_1037);
lean_inc(x_1036);
x_1048 = l_Lean_Expr_forallE___override(x_1036, x_1037, x_1038, x_1039);
x_1049 = lean_ptr_addr(x_1037);
lean_dec(x_1037);
x_1050 = lean_ptr_addr(x_1041);
x_1051 = lean_usize_dec_eq(x_1049, x_1050);
if (x_1051 == 0)
{
lean_object* x_1052; lean_object* x_1053; 
lean_dec(x_1048);
lean_dec(x_1038);
x_1052 = l_Lean_Expr_forallE___override(x_1036, x_1041, x_1045, x_1039);
if (lean_is_scalar(x_1047)) {
 x_1053 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1053 = x_1047;
}
lean_ctor_set(x_1053, 0, x_1052);
lean_ctor_set(x_1053, 1, x_1046);
return x_1053;
}
else
{
size_t x_1054; size_t x_1055; uint8_t x_1056; 
x_1054 = lean_ptr_addr(x_1038);
lean_dec(x_1038);
x_1055 = lean_ptr_addr(x_1045);
x_1056 = lean_usize_dec_eq(x_1054, x_1055);
if (x_1056 == 0)
{
lean_object* x_1057; lean_object* x_1058; 
lean_dec(x_1048);
x_1057 = l_Lean_Expr_forallE___override(x_1036, x_1041, x_1045, x_1039);
if (lean_is_scalar(x_1047)) {
 x_1058 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1058 = x_1047;
}
lean_ctor_set(x_1058, 0, x_1057);
lean_ctor_set(x_1058, 1, x_1046);
return x_1058;
}
else
{
uint8_t x_1059; 
x_1059 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_1039, x_1039);
if (x_1059 == 0)
{
lean_object* x_1060; lean_object* x_1061; 
lean_dec(x_1048);
x_1060 = l_Lean_Expr_forallE___override(x_1036, x_1041, x_1045, x_1039);
if (lean_is_scalar(x_1047)) {
 x_1061 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1061 = x_1047;
}
lean_ctor_set(x_1061, 0, x_1060);
lean_ctor_set(x_1061, 1, x_1046);
return x_1061;
}
else
{
lean_object* x_1062; 
lean_dec(x_1045);
lean_dec(x_1041);
lean_dec(x_1036);
if (lean_is_scalar(x_1047)) {
 x_1062 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1062 = x_1047;
}
lean_ctor_set(x_1062, 0, x_1048);
lean_ctor_set(x_1062, 1, x_1046);
return x_1062;
}
}
}
}
else
{
lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; 
lean_dec(x_1041);
lean_dec(x_1038);
lean_dec(x_1037);
lean_dec(x_1036);
x_1063 = lean_ctor_get(x_1044, 0);
lean_inc(x_1063);
x_1064 = lean_ctor_get(x_1044, 1);
lean_inc(x_1064);
if (lean_is_exclusive(x_1044)) {
 lean_ctor_release(x_1044, 0);
 lean_ctor_release(x_1044, 1);
 x_1065 = x_1044;
} else {
 lean_dec_ref(x_1044);
 x_1065 = lean_box(0);
}
if (lean_is_scalar(x_1065)) {
 x_1066 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1066 = x_1065;
}
lean_ctor_set(x_1066, 0, x_1063);
lean_ctor_set(x_1066, 1, x_1064);
return x_1066;
}
}
else
{
lean_object* x_1067; lean_object* x_1068; lean_object* x_1069; lean_object* x_1070; 
lean_dec(x_1038);
lean_dec(x_1037);
lean_dec(x_1036);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1067 = lean_ctor_get(x_1040, 0);
lean_inc(x_1067);
x_1068 = lean_ctor_get(x_1040, 1);
lean_inc(x_1068);
if (lean_is_exclusive(x_1040)) {
 lean_ctor_release(x_1040, 0);
 lean_ctor_release(x_1040, 1);
 x_1069 = x_1040;
} else {
 lean_dec_ref(x_1040);
 x_1069 = lean_box(0);
}
if (lean_is_scalar(x_1069)) {
 x_1070 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1070 = x_1069;
}
lean_ctor_set(x_1070, 0, x_1067);
lean_ctor_set(x_1070, 1, x_1068);
return x_1070;
}
}
case 8:
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; uint8_t x_1076; lean_object* x_1077; 
x_1071 = lean_ctor_get(x_969, 1);
lean_inc(x_1071);
lean_dec(x_969);
x_1072 = lean_ctor_get(x_5, 0);
lean_inc(x_1072);
x_1073 = lean_ctor_get(x_5, 1);
lean_inc(x_1073);
x_1074 = lean_ctor_get(x_5, 2);
lean_inc(x_1074);
x_1075 = lean_ctor_get(x_5, 3);
lean_inc(x_1075);
x_1076 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1073);
lean_inc(x_1);
x_1077 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1073, x_6, x_7, x_8, x_9, x_10, x_11, x_1071);
if (lean_obj_tag(x_1077) == 0)
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; 
x_1078 = lean_ctor_get(x_1077, 0);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1077, 1);
lean_inc(x_1079);
lean_dec(x_1077);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1074);
lean_inc(x_1);
x_1080 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1074, x_6, x_7, x_8, x_9, x_10, x_11, x_1079);
if (lean_obj_tag(x_1080) == 0)
{
lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; 
x_1081 = lean_ctor_get(x_1080, 0);
lean_inc(x_1081);
x_1082 = lean_ctor_get(x_1080, 1);
lean_inc(x_1082);
lean_dec(x_1080);
x_1083 = lean_nat_add(x_6, x_513);
lean_dec(x_6);
lean_inc(x_1075);
x_1084 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1075, x_1083, x_7, x_8, x_9, x_10, x_11, x_1082);
if (lean_obj_tag(x_1084) == 0)
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; size_t x_1088; size_t x_1089; uint8_t x_1090; 
x_1085 = lean_ctor_get(x_1084, 0);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_1084, 1);
lean_inc(x_1086);
if (lean_is_exclusive(x_1084)) {
 lean_ctor_release(x_1084, 0);
 lean_ctor_release(x_1084, 1);
 x_1087 = x_1084;
} else {
 lean_dec_ref(x_1084);
 x_1087 = lean_box(0);
}
x_1088 = lean_ptr_addr(x_1073);
lean_dec(x_1073);
x_1089 = lean_ptr_addr(x_1078);
x_1090 = lean_usize_dec_eq(x_1088, x_1089);
if (x_1090 == 0)
{
lean_object* x_1091; lean_object* x_1092; 
lean_dec(x_1075);
lean_dec(x_1074);
lean_dec(x_5);
x_1091 = l_Lean_Expr_letE___override(x_1072, x_1078, x_1081, x_1085, x_1076);
if (lean_is_scalar(x_1087)) {
 x_1092 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1092 = x_1087;
}
lean_ctor_set(x_1092, 0, x_1091);
lean_ctor_set(x_1092, 1, x_1086);
return x_1092;
}
else
{
size_t x_1093; size_t x_1094; uint8_t x_1095; 
x_1093 = lean_ptr_addr(x_1074);
lean_dec(x_1074);
x_1094 = lean_ptr_addr(x_1081);
x_1095 = lean_usize_dec_eq(x_1093, x_1094);
if (x_1095 == 0)
{
lean_object* x_1096; lean_object* x_1097; 
lean_dec(x_1075);
lean_dec(x_5);
x_1096 = l_Lean_Expr_letE___override(x_1072, x_1078, x_1081, x_1085, x_1076);
if (lean_is_scalar(x_1087)) {
 x_1097 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1097 = x_1087;
}
lean_ctor_set(x_1097, 0, x_1096);
lean_ctor_set(x_1097, 1, x_1086);
return x_1097;
}
else
{
size_t x_1098; size_t x_1099; uint8_t x_1100; 
x_1098 = lean_ptr_addr(x_1075);
lean_dec(x_1075);
x_1099 = lean_ptr_addr(x_1085);
x_1100 = lean_usize_dec_eq(x_1098, x_1099);
if (x_1100 == 0)
{
lean_object* x_1101; lean_object* x_1102; 
lean_dec(x_5);
x_1101 = l_Lean_Expr_letE___override(x_1072, x_1078, x_1081, x_1085, x_1076);
if (lean_is_scalar(x_1087)) {
 x_1102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1102 = x_1087;
}
lean_ctor_set(x_1102, 0, x_1101);
lean_ctor_set(x_1102, 1, x_1086);
return x_1102;
}
else
{
lean_object* x_1103; 
lean_dec(x_1085);
lean_dec(x_1081);
lean_dec(x_1078);
lean_dec(x_1072);
if (lean_is_scalar(x_1087)) {
 x_1103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1103 = x_1087;
}
lean_ctor_set(x_1103, 0, x_5);
lean_ctor_set(x_1103, 1, x_1086);
return x_1103;
}
}
}
}
else
{
lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; 
lean_dec(x_1081);
lean_dec(x_1078);
lean_dec(x_1075);
lean_dec(x_1074);
lean_dec(x_1073);
lean_dec(x_1072);
lean_dec(x_5);
x_1104 = lean_ctor_get(x_1084, 0);
lean_inc(x_1104);
x_1105 = lean_ctor_get(x_1084, 1);
lean_inc(x_1105);
if (lean_is_exclusive(x_1084)) {
 lean_ctor_release(x_1084, 0);
 lean_ctor_release(x_1084, 1);
 x_1106 = x_1084;
} else {
 lean_dec_ref(x_1084);
 x_1106 = lean_box(0);
}
if (lean_is_scalar(x_1106)) {
 x_1107 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1107 = x_1106;
}
lean_ctor_set(x_1107, 0, x_1104);
lean_ctor_set(x_1107, 1, x_1105);
return x_1107;
}
}
else
{
lean_object* x_1108; lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; 
lean_dec(x_1078);
lean_dec(x_1075);
lean_dec(x_1074);
lean_dec(x_1073);
lean_dec(x_1072);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1108 = lean_ctor_get(x_1080, 0);
lean_inc(x_1108);
x_1109 = lean_ctor_get(x_1080, 1);
lean_inc(x_1109);
if (lean_is_exclusive(x_1080)) {
 lean_ctor_release(x_1080, 0);
 lean_ctor_release(x_1080, 1);
 x_1110 = x_1080;
} else {
 lean_dec_ref(x_1080);
 x_1110 = lean_box(0);
}
if (lean_is_scalar(x_1110)) {
 x_1111 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1111 = x_1110;
}
lean_ctor_set(x_1111, 0, x_1108);
lean_ctor_set(x_1111, 1, x_1109);
return x_1111;
}
}
else
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; 
lean_dec(x_1075);
lean_dec(x_1074);
lean_dec(x_1073);
lean_dec(x_1072);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1112 = lean_ctor_get(x_1077, 0);
lean_inc(x_1112);
x_1113 = lean_ctor_get(x_1077, 1);
lean_inc(x_1113);
if (lean_is_exclusive(x_1077)) {
 lean_ctor_release(x_1077, 0);
 lean_ctor_release(x_1077, 1);
 x_1114 = x_1077;
} else {
 lean_dec_ref(x_1077);
 x_1114 = lean_box(0);
}
if (lean_is_scalar(x_1114)) {
 x_1115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1115 = x_1114;
}
lean_ctor_set(x_1115, 0, x_1112);
lean_ctor_set(x_1115, 1, x_1113);
return x_1115;
}
}
case 10:
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; 
x_1116 = lean_ctor_get(x_969, 1);
lean_inc(x_1116);
lean_dec(x_969);
x_1117 = lean_ctor_get(x_5, 0);
lean_inc(x_1117);
x_1118 = lean_ctor_get(x_5, 1);
lean_inc(x_1118);
lean_inc(x_1118);
x_1119 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1118, x_6, x_7, x_8, x_9, x_10, x_11, x_1116);
if (lean_obj_tag(x_1119) == 0)
{
lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; size_t x_1123; size_t x_1124; uint8_t x_1125; 
x_1120 = lean_ctor_get(x_1119, 0);
lean_inc(x_1120);
x_1121 = lean_ctor_get(x_1119, 1);
lean_inc(x_1121);
if (lean_is_exclusive(x_1119)) {
 lean_ctor_release(x_1119, 0);
 lean_ctor_release(x_1119, 1);
 x_1122 = x_1119;
} else {
 lean_dec_ref(x_1119);
 x_1122 = lean_box(0);
}
x_1123 = lean_ptr_addr(x_1118);
lean_dec(x_1118);
x_1124 = lean_ptr_addr(x_1120);
x_1125 = lean_usize_dec_eq(x_1123, x_1124);
if (x_1125 == 0)
{
lean_object* x_1126; lean_object* x_1127; 
lean_dec(x_5);
x_1126 = l_Lean_Expr_mdata___override(x_1117, x_1120);
if (lean_is_scalar(x_1122)) {
 x_1127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1127 = x_1122;
}
lean_ctor_set(x_1127, 0, x_1126);
lean_ctor_set(x_1127, 1, x_1121);
return x_1127;
}
else
{
lean_object* x_1128; 
lean_dec(x_1120);
lean_dec(x_1117);
if (lean_is_scalar(x_1122)) {
 x_1128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1128 = x_1122;
}
lean_ctor_set(x_1128, 0, x_5);
lean_ctor_set(x_1128, 1, x_1121);
return x_1128;
}
}
else
{
lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
lean_dec(x_1118);
lean_dec(x_1117);
lean_dec(x_5);
x_1129 = lean_ctor_get(x_1119, 0);
lean_inc(x_1129);
x_1130 = lean_ctor_get(x_1119, 1);
lean_inc(x_1130);
if (lean_is_exclusive(x_1119)) {
 lean_ctor_release(x_1119, 0);
 lean_ctor_release(x_1119, 1);
 x_1131 = x_1119;
} else {
 lean_dec_ref(x_1119);
 x_1131 = lean_box(0);
}
if (lean_is_scalar(x_1131)) {
 x_1132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1132 = x_1131;
}
lean_ctor_set(x_1132, 0, x_1129);
lean_ctor_set(x_1132, 1, x_1130);
return x_1132;
}
}
case 11:
{
lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; 
x_1133 = lean_ctor_get(x_969, 1);
lean_inc(x_1133);
lean_dec(x_969);
x_1134 = lean_ctor_get(x_5, 0);
lean_inc(x_1134);
x_1135 = lean_ctor_get(x_5, 1);
lean_inc(x_1135);
x_1136 = lean_ctor_get(x_5, 2);
lean_inc(x_1136);
lean_inc(x_1136);
x_1137 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1136, x_6, x_7, x_8, x_9, x_10, x_11, x_1133);
if (lean_obj_tag(x_1137) == 0)
{
lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; size_t x_1141; size_t x_1142; uint8_t x_1143; 
x_1138 = lean_ctor_get(x_1137, 0);
lean_inc(x_1138);
x_1139 = lean_ctor_get(x_1137, 1);
lean_inc(x_1139);
if (lean_is_exclusive(x_1137)) {
 lean_ctor_release(x_1137, 0);
 lean_ctor_release(x_1137, 1);
 x_1140 = x_1137;
} else {
 lean_dec_ref(x_1137);
 x_1140 = lean_box(0);
}
x_1141 = lean_ptr_addr(x_1136);
lean_dec(x_1136);
x_1142 = lean_ptr_addr(x_1138);
x_1143 = lean_usize_dec_eq(x_1141, x_1142);
if (x_1143 == 0)
{
lean_object* x_1144; lean_object* x_1145; 
lean_dec(x_5);
x_1144 = l_Lean_Expr_proj___override(x_1134, x_1135, x_1138);
if (lean_is_scalar(x_1140)) {
 x_1145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1145 = x_1140;
}
lean_ctor_set(x_1145, 0, x_1144);
lean_ctor_set(x_1145, 1, x_1139);
return x_1145;
}
else
{
lean_object* x_1146; 
lean_dec(x_1138);
lean_dec(x_1135);
lean_dec(x_1134);
if (lean_is_scalar(x_1140)) {
 x_1146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1146 = x_1140;
}
lean_ctor_set(x_1146, 0, x_5);
lean_ctor_set(x_1146, 1, x_1139);
return x_1146;
}
}
else
{
lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; 
lean_dec(x_1136);
lean_dec(x_1135);
lean_dec(x_1134);
lean_dec(x_5);
x_1147 = lean_ctor_get(x_1137, 0);
lean_inc(x_1147);
x_1148 = lean_ctor_get(x_1137, 1);
lean_inc(x_1148);
if (lean_is_exclusive(x_1137)) {
 lean_ctor_release(x_1137, 0);
 lean_ctor_release(x_1137, 1);
 x_1149 = x_1137;
} else {
 lean_dec_ref(x_1137);
 x_1149 = lean_box(0);
}
if (lean_is_scalar(x_1149)) {
 x_1150 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1150 = x_1149;
}
lean_ctor_set(x_1150, 0, x_1147);
lean_ctor_set(x_1150, 1, x_1148);
return x_1150;
}
}
default: 
{
lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1151 = lean_ctor_get(x_969, 1);
lean_inc(x_1151);
if (lean_is_exclusive(x_969)) {
 lean_ctor_release(x_969, 0);
 lean_ctor_release(x_969, 1);
 x_1152 = x_969;
} else {
 lean_dec_ref(x_969);
 x_1152 = lean_box(0);
}
if (lean_is_scalar(x_1152)) {
 x_1153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1153 = x_1152;
}
lean_ctor_set(x_1153, 0, x_5);
lean_ctor_set(x_1153, 1, x_1151);
return x_1153;
}
}
}
else
{
lean_object* x_1154; lean_object* x_1155; 
lean_dec(x_261);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_1154 = l_Lean_Expr_bvar___override(x_6);
x_1155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1155, 0, x_1154);
lean_ctor_set(x_1155, 1, x_958);
return x_1155;
}
}
}
}
else
{
uint8_t x_1156; 
lean_dec(x_261);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1156 = !lean_is_exclusive(x_262);
if (x_1156 == 0)
{
return x_262;
}
else
{
lean_object* x_1157; lean_object* x_1158; lean_object* x_1159; 
x_1157 = lean_ctor_get(x_262, 0);
x_1158 = lean_ctor_get(x_262, 1);
lean_inc(x_1158);
lean_inc(x_1157);
lean_dec(x_262);
x_1159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1159, 0, x_1157);
lean_ctor_set(x_1159, 1, x_1158);
return x_1159;
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
lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; 
x_1160 = lean_ctor_get(x_5, 0);
lean_inc(x_1160);
x_1161 = lean_ctor_get(x_5, 1);
lean_inc(x_1161);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1160);
lean_inc(x_1);
x_1162 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1160, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1162) == 0)
{
lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; 
x_1163 = lean_ctor_get(x_1162, 0);
lean_inc(x_1163);
x_1164 = lean_ctor_get(x_1162, 1);
lean_inc(x_1164);
lean_dec(x_1162);
lean_inc(x_1161);
x_1165 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1161, x_6, x_7, x_8, x_9, x_10, x_11, x_1164);
if (lean_obj_tag(x_1165) == 0)
{
uint8_t x_1166; 
x_1166 = !lean_is_exclusive(x_1165);
if (x_1166 == 0)
{
lean_object* x_1167; size_t x_1168; size_t x_1169; uint8_t x_1170; 
x_1167 = lean_ctor_get(x_1165, 0);
x_1168 = lean_ptr_addr(x_1160);
lean_dec(x_1160);
x_1169 = lean_ptr_addr(x_1163);
x_1170 = lean_usize_dec_eq(x_1168, x_1169);
if (x_1170 == 0)
{
lean_object* x_1171; 
lean_dec(x_1161);
lean_dec(x_5);
x_1171 = l_Lean_Expr_app___override(x_1163, x_1167);
lean_ctor_set(x_1165, 0, x_1171);
return x_1165;
}
else
{
size_t x_1172; size_t x_1173; uint8_t x_1174; 
x_1172 = lean_ptr_addr(x_1161);
lean_dec(x_1161);
x_1173 = lean_ptr_addr(x_1167);
x_1174 = lean_usize_dec_eq(x_1172, x_1173);
if (x_1174 == 0)
{
lean_object* x_1175; 
lean_dec(x_5);
x_1175 = l_Lean_Expr_app___override(x_1163, x_1167);
lean_ctor_set(x_1165, 0, x_1175);
return x_1165;
}
else
{
lean_dec(x_1167);
lean_dec(x_1163);
lean_ctor_set(x_1165, 0, x_5);
return x_1165;
}
}
}
else
{
lean_object* x_1176; lean_object* x_1177; size_t x_1178; size_t x_1179; uint8_t x_1180; 
x_1176 = lean_ctor_get(x_1165, 0);
x_1177 = lean_ctor_get(x_1165, 1);
lean_inc(x_1177);
lean_inc(x_1176);
lean_dec(x_1165);
x_1178 = lean_ptr_addr(x_1160);
lean_dec(x_1160);
x_1179 = lean_ptr_addr(x_1163);
x_1180 = lean_usize_dec_eq(x_1178, x_1179);
if (x_1180 == 0)
{
lean_object* x_1181; lean_object* x_1182; 
lean_dec(x_1161);
lean_dec(x_5);
x_1181 = l_Lean_Expr_app___override(x_1163, x_1176);
x_1182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1182, 0, x_1181);
lean_ctor_set(x_1182, 1, x_1177);
return x_1182;
}
else
{
size_t x_1183; size_t x_1184; uint8_t x_1185; 
x_1183 = lean_ptr_addr(x_1161);
lean_dec(x_1161);
x_1184 = lean_ptr_addr(x_1176);
x_1185 = lean_usize_dec_eq(x_1183, x_1184);
if (x_1185 == 0)
{
lean_object* x_1186; lean_object* x_1187; 
lean_dec(x_5);
x_1186 = l_Lean_Expr_app___override(x_1163, x_1176);
x_1187 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1187, 0, x_1186);
lean_ctor_set(x_1187, 1, x_1177);
return x_1187;
}
else
{
lean_object* x_1188; 
lean_dec(x_1176);
lean_dec(x_1163);
x_1188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1188, 0, x_5);
lean_ctor_set(x_1188, 1, x_1177);
return x_1188;
}
}
}
}
else
{
uint8_t x_1189; 
lean_dec(x_1163);
lean_dec(x_1161);
lean_dec(x_1160);
lean_dec(x_5);
x_1189 = !lean_is_exclusive(x_1165);
if (x_1189 == 0)
{
return x_1165;
}
else
{
lean_object* x_1190; lean_object* x_1191; lean_object* x_1192; 
x_1190 = lean_ctor_get(x_1165, 0);
x_1191 = lean_ctor_get(x_1165, 1);
lean_inc(x_1191);
lean_inc(x_1190);
lean_dec(x_1165);
x_1192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1192, 0, x_1190);
lean_ctor_set(x_1192, 1, x_1191);
return x_1192;
}
}
}
else
{
uint8_t x_1193; 
lean_dec(x_1161);
lean_dec(x_1160);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1193 = !lean_is_exclusive(x_1162);
if (x_1193 == 0)
{
return x_1162;
}
else
{
lean_object* x_1194; lean_object* x_1195; lean_object* x_1196; 
x_1194 = lean_ctor_get(x_1162, 0);
x_1195 = lean_ctor_get(x_1162, 1);
lean_inc(x_1195);
lean_inc(x_1194);
lean_dec(x_1162);
x_1196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1196, 0, x_1194);
lean_ctor_set(x_1196, 1, x_1195);
return x_1196;
}
}
}
case 6:
{
lean_object* x_1197; lean_object* x_1198; lean_object* x_1199; uint8_t x_1200; lean_object* x_1201; 
x_1197 = lean_ctor_get(x_5, 0);
lean_inc(x_1197);
x_1198 = lean_ctor_get(x_5, 1);
lean_inc(x_1198);
x_1199 = lean_ctor_get(x_5, 2);
lean_inc(x_1199);
x_1200 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1198);
lean_inc(x_1);
x_1201 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1198, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1201) == 0)
{
lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; 
x_1202 = lean_ctor_get(x_1201, 0);
lean_inc(x_1202);
x_1203 = lean_ctor_get(x_1201, 1);
lean_inc(x_1203);
lean_dec(x_1201);
x_1204 = lean_unsigned_to_nat(1u);
x_1205 = lean_nat_add(x_6, x_1204);
lean_dec(x_6);
lean_inc(x_1199);
x_1206 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1199, x_1205, x_7, x_8, x_9, x_10, x_11, x_1203);
if (lean_obj_tag(x_1206) == 0)
{
uint8_t x_1207; 
x_1207 = !lean_is_exclusive(x_1206);
if (x_1207 == 0)
{
lean_object* x_1208; lean_object* x_1209; size_t x_1210; size_t x_1211; uint8_t x_1212; 
x_1208 = lean_ctor_get(x_1206, 0);
lean_inc(x_1199);
lean_inc(x_1198);
lean_inc(x_1197);
x_1209 = l_Lean_Expr_lam___override(x_1197, x_1198, x_1199, x_1200);
x_1210 = lean_ptr_addr(x_1198);
lean_dec(x_1198);
x_1211 = lean_ptr_addr(x_1202);
x_1212 = lean_usize_dec_eq(x_1210, x_1211);
if (x_1212 == 0)
{
lean_object* x_1213; 
lean_dec(x_1209);
lean_dec(x_1199);
x_1213 = l_Lean_Expr_lam___override(x_1197, x_1202, x_1208, x_1200);
lean_ctor_set(x_1206, 0, x_1213);
return x_1206;
}
else
{
size_t x_1214; size_t x_1215; uint8_t x_1216; 
x_1214 = lean_ptr_addr(x_1199);
lean_dec(x_1199);
x_1215 = lean_ptr_addr(x_1208);
x_1216 = lean_usize_dec_eq(x_1214, x_1215);
if (x_1216 == 0)
{
lean_object* x_1217; 
lean_dec(x_1209);
x_1217 = l_Lean_Expr_lam___override(x_1197, x_1202, x_1208, x_1200);
lean_ctor_set(x_1206, 0, x_1217);
return x_1206;
}
else
{
uint8_t x_1218; 
x_1218 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_1200, x_1200);
if (x_1218 == 0)
{
lean_object* x_1219; 
lean_dec(x_1209);
x_1219 = l_Lean_Expr_lam___override(x_1197, x_1202, x_1208, x_1200);
lean_ctor_set(x_1206, 0, x_1219);
return x_1206;
}
else
{
lean_dec(x_1208);
lean_dec(x_1202);
lean_dec(x_1197);
lean_ctor_set(x_1206, 0, x_1209);
return x_1206;
}
}
}
}
else
{
lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; size_t x_1223; size_t x_1224; uint8_t x_1225; 
x_1220 = lean_ctor_get(x_1206, 0);
x_1221 = lean_ctor_get(x_1206, 1);
lean_inc(x_1221);
lean_inc(x_1220);
lean_dec(x_1206);
lean_inc(x_1199);
lean_inc(x_1198);
lean_inc(x_1197);
x_1222 = l_Lean_Expr_lam___override(x_1197, x_1198, x_1199, x_1200);
x_1223 = lean_ptr_addr(x_1198);
lean_dec(x_1198);
x_1224 = lean_ptr_addr(x_1202);
x_1225 = lean_usize_dec_eq(x_1223, x_1224);
if (x_1225 == 0)
{
lean_object* x_1226; lean_object* x_1227; 
lean_dec(x_1222);
lean_dec(x_1199);
x_1226 = l_Lean_Expr_lam___override(x_1197, x_1202, x_1220, x_1200);
x_1227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1227, 0, x_1226);
lean_ctor_set(x_1227, 1, x_1221);
return x_1227;
}
else
{
size_t x_1228; size_t x_1229; uint8_t x_1230; 
x_1228 = lean_ptr_addr(x_1199);
lean_dec(x_1199);
x_1229 = lean_ptr_addr(x_1220);
x_1230 = lean_usize_dec_eq(x_1228, x_1229);
if (x_1230 == 0)
{
lean_object* x_1231; lean_object* x_1232; 
lean_dec(x_1222);
x_1231 = l_Lean_Expr_lam___override(x_1197, x_1202, x_1220, x_1200);
x_1232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1232, 0, x_1231);
lean_ctor_set(x_1232, 1, x_1221);
return x_1232;
}
else
{
uint8_t x_1233; 
x_1233 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_1200, x_1200);
if (x_1233 == 0)
{
lean_object* x_1234; lean_object* x_1235; 
lean_dec(x_1222);
x_1234 = l_Lean_Expr_lam___override(x_1197, x_1202, x_1220, x_1200);
x_1235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1235, 0, x_1234);
lean_ctor_set(x_1235, 1, x_1221);
return x_1235;
}
else
{
lean_object* x_1236; 
lean_dec(x_1220);
lean_dec(x_1202);
lean_dec(x_1197);
x_1236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1236, 0, x_1222);
lean_ctor_set(x_1236, 1, x_1221);
return x_1236;
}
}
}
}
}
else
{
uint8_t x_1237; 
lean_dec(x_1202);
lean_dec(x_1199);
lean_dec(x_1198);
lean_dec(x_1197);
x_1237 = !lean_is_exclusive(x_1206);
if (x_1237 == 0)
{
return x_1206;
}
else
{
lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; 
x_1238 = lean_ctor_get(x_1206, 0);
x_1239 = lean_ctor_get(x_1206, 1);
lean_inc(x_1239);
lean_inc(x_1238);
lean_dec(x_1206);
x_1240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1240, 0, x_1238);
lean_ctor_set(x_1240, 1, x_1239);
return x_1240;
}
}
}
else
{
uint8_t x_1241; 
lean_dec(x_1199);
lean_dec(x_1198);
lean_dec(x_1197);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1241 = !lean_is_exclusive(x_1201);
if (x_1241 == 0)
{
return x_1201;
}
else
{
lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; 
x_1242 = lean_ctor_get(x_1201, 0);
x_1243 = lean_ctor_get(x_1201, 1);
lean_inc(x_1243);
lean_inc(x_1242);
lean_dec(x_1201);
x_1244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1244, 0, x_1242);
lean_ctor_set(x_1244, 1, x_1243);
return x_1244;
}
}
}
case 7:
{
lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; uint8_t x_1248; lean_object* x_1249; 
x_1245 = lean_ctor_get(x_5, 0);
lean_inc(x_1245);
x_1246 = lean_ctor_get(x_5, 1);
lean_inc(x_1246);
x_1247 = lean_ctor_get(x_5, 2);
lean_inc(x_1247);
x_1248 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1246);
lean_inc(x_1);
x_1249 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1246, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1249) == 0)
{
lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; 
x_1250 = lean_ctor_get(x_1249, 0);
lean_inc(x_1250);
x_1251 = lean_ctor_get(x_1249, 1);
lean_inc(x_1251);
lean_dec(x_1249);
x_1252 = lean_unsigned_to_nat(1u);
x_1253 = lean_nat_add(x_6, x_1252);
lean_dec(x_6);
lean_inc(x_1247);
x_1254 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1247, x_1253, x_7, x_8, x_9, x_10, x_11, x_1251);
if (lean_obj_tag(x_1254) == 0)
{
uint8_t x_1255; 
x_1255 = !lean_is_exclusive(x_1254);
if (x_1255 == 0)
{
lean_object* x_1256; lean_object* x_1257; size_t x_1258; size_t x_1259; uint8_t x_1260; 
x_1256 = lean_ctor_get(x_1254, 0);
lean_inc(x_1247);
lean_inc(x_1246);
lean_inc(x_1245);
x_1257 = l_Lean_Expr_forallE___override(x_1245, x_1246, x_1247, x_1248);
x_1258 = lean_ptr_addr(x_1246);
lean_dec(x_1246);
x_1259 = lean_ptr_addr(x_1250);
x_1260 = lean_usize_dec_eq(x_1258, x_1259);
if (x_1260 == 0)
{
lean_object* x_1261; 
lean_dec(x_1257);
lean_dec(x_1247);
x_1261 = l_Lean_Expr_forallE___override(x_1245, x_1250, x_1256, x_1248);
lean_ctor_set(x_1254, 0, x_1261);
return x_1254;
}
else
{
size_t x_1262; size_t x_1263; uint8_t x_1264; 
x_1262 = lean_ptr_addr(x_1247);
lean_dec(x_1247);
x_1263 = lean_ptr_addr(x_1256);
x_1264 = lean_usize_dec_eq(x_1262, x_1263);
if (x_1264 == 0)
{
lean_object* x_1265; 
lean_dec(x_1257);
x_1265 = l_Lean_Expr_forallE___override(x_1245, x_1250, x_1256, x_1248);
lean_ctor_set(x_1254, 0, x_1265);
return x_1254;
}
else
{
uint8_t x_1266; 
x_1266 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_1248, x_1248);
if (x_1266 == 0)
{
lean_object* x_1267; 
lean_dec(x_1257);
x_1267 = l_Lean_Expr_forallE___override(x_1245, x_1250, x_1256, x_1248);
lean_ctor_set(x_1254, 0, x_1267);
return x_1254;
}
else
{
lean_dec(x_1256);
lean_dec(x_1250);
lean_dec(x_1245);
lean_ctor_set(x_1254, 0, x_1257);
return x_1254;
}
}
}
}
else
{
lean_object* x_1268; lean_object* x_1269; lean_object* x_1270; size_t x_1271; size_t x_1272; uint8_t x_1273; 
x_1268 = lean_ctor_get(x_1254, 0);
x_1269 = lean_ctor_get(x_1254, 1);
lean_inc(x_1269);
lean_inc(x_1268);
lean_dec(x_1254);
lean_inc(x_1247);
lean_inc(x_1246);
lean_inc(x_1245);
x_1270 = l_Lean_Expr_forallE___override(x_1245, x_1246, x_1247, x_1248);
x_1271 = lean_ptr_addr(x_1246);
lean_dec(x_1246);
x_1272 = lean_ptr_addr(x_1250);
x_1273 = lean_usize_dec_eq(x_1271, x_1272);
if (x_1273 == 0)
{
lean_object* x_1274; lean_object* x_1275; 
lean_dec(x_1270);
lean_dec(x_1247);
x_1274 = l_Lean_Expr_forallE___override(x_1245, x_1250, x_1268, x_1248);
x_1275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1275, 0, x_1274);
lean_ctor_set(x_1275, 1, x_1269);
return x_1275;
}
else
{
size_t x_1276; size_t x_1277; uint8_t x_1278; 
x_1276 = lean_ptr_addr(x_1247);
lean_dec(x_1247);
x_1277 = lean_ptr_addr(x_1268);
x_1278 = lean_usize_dec_eq(x_1276, x_1277);
if (x_1278 == 0)
{
lean_object* x_1279; lean_object* x_1280; 
lean_dec(x_1270);
x_1279 = l_Lean_Expr_forallE___override(x_1245, x_1250, x_1268, x_1248);
x_1280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1280, 0, x_1279);
lean_ctor_set(x_1280, 1, x_1269);
return x_1280;
}
else
{
uint8_t x_1281; 
x_1281 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_1248, x_1248);
if (x_1281 == 0)
{
lean_object* x_1282; lean_object* x_1283; 
lean_dec(x_1270);
x_1282 = l_Lean_Expr_forallE___override(x_1245, x_1250, x_1268, x_1248);
x_1283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1283, 0, x_1282);
lean_ctor_set(x_1283, 1, x_1269);
return x_1283;
}
else
{
lean_object* x_1284; 
lean_dec(x_1268);
lean_dec(x_1250);
lean_dec(x_1245);
x_1284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1284, 0, x_1270);
lean_ctor_set(x_1284, 1, x_1269);
return x_1284;
}
}
}
}
}
else
{
uint8_t x_1285; 
lean_dec(x_1250);
lean_dec(x_1247);
lean_dec(x_1246);
lean_dec(x_1245);
x_1285 = !lean_is_exclusive(x_1254);
if (x_1285 == 0)
{
return x_1254;
}
else
{
lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; 
x_1286 = lean_ctor_get(x_1254, 0);
x_1287 = lean_ctor_get(x_1254, 1);
lean_inc(x_1287);
lean_inc(x_1286);
lean_dec(x_1254);
x_1288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1288, 0, x_1286);
lean_ctor_set(x_1288, 1, x_1287);
return x_1288;
}
}
}
else
{
uint8_t x_1289; 
lean_dec(x_1247);
lean_dec(x_1246);
lean_dec(x_1245);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1289 = !lean_is_exclusive(x_1249);
if (x_1289 == 0)
{
return x_1249;
}
else
{
lean_object* x_1290; lean_object* x_1291; lean_object* x_1292; 
x_1290 = lean_ctor_get(x_1249, 0);
x_1291 = lean_ctor_get(x_1249, 1);
lean_inc(x_1291);
lean_inc(x_1290);
lean_dec(x_1249);
x_1292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1292, 0, x_1290);
lean_ctor_set(x_1292, 1, x_1291);
return x_1292;
}
}
}
case 8:
{
lean_object* x_1293; lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; uint8_t x_1297; lean_object* x_1298; 
x_1293 = lean_ctor_get(x_5, 0);
lean_inc(x_1293);
x_1294 = lean_ctor_get(x_5, 1);
lean_inc(x_1294);
x_1295 = lean_ctor_get(x_5, 2);
lean_inc(x_1295);
x_1296 = lean_ctor_get(x_5, 3);
lean_inc(x_1296);
x_1297 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1294);
lean_inc(x_1);
x_1298 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1294, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1298) == 0)
{
lean_object* x_1299; lean_object* x_1300; lean_object* x_1301; 
x_1299 = lean_ctor_get(x_1298, 0);
lean_inc(x_1299);
x_1300 = lean_ctor_get(x_1298, 1);
lean_inc(x_1300);
lean_dec(x_1298);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1295);
lean_inc(x_1);
x_1301 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1295, x_6, x_7, x_8, x_9, x_10, x_11, x_1300);
if (lean_obj_tag(x_1301) == 0)
{
lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; lean_object* x_1305; lean_object* x_1306; 
x_1302 = lean_ctor_get(x_1301, 0);
lean_inc(x_1302);
x_1303 = lean_ctor_get(x_1301, 1);
lean_inc(x_1303);
lean_dec(x_1301);
x_1304 = lean_unsigned_to_nat(1u);
x_1305 = lean_nat_add(x_6, x_1304);
lean_dec(x_6);
lean_inc(x_1296);
x_1306 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1296, x_1305, x_7, x_8, x_9, x_10, x_11, x_1303);
if (lean_obj_tag(x_1306) == 0)
{
uint8_t x_1307; 
x_1307 = !lean_is_exclusive(x_1306);
if (x_1307 == 0)
{
lean_object* x_1308; size_t x_1309; size_t x_1310; uint8_t x_1311; 
x_1308 = lean_ctor_get(x_1306, 0);
x_1309 = lean_ptr_addr(x_1294);
lean_dec(x_1294);
x_1310 = lean_ptr_addr(x_1299);
x_1311 = lean_usize_dec_eq(x_1309, x_1310);
if (x_1311 == 0)
{
lean_object* x_1312; 
lean_dec(x_1296);
lean_dec(x_1295);
lean_dec(x_5);
x_1312 = l_Lean_Expr_letE___override(x_1293, x_1299, x_1302, x_1308, x_1297);
lean_ctor_set(x_1306, 0, x_1312);
return x_1306;
}
else
{
size_t x_1313; size_t x_1314; uint8_t x_1315; 
x_1313 = lean_ptr_addr(x_1295);
lean_dec(x_1295);
x_1314 = lean_ptr_addr(x_1302);
x_1315 = lean_usize_dec_eq(x_1313, x_1314);
if (x_1315 == 0)
{
lean_object* x_1316; 
lean_dec(x_1296);
lean_dec(x_5);
x_1316 = l_Lean_Expr_letE___override(x_1293, x_1299, x_1302, x_1308, x_1297);
lean_ctor_set(x_1306, 0, x_1316);
return x_1306;
}
else
{
size_t x_1317; size_t x_1318; uint8_t x_1319; 
x_1317 = lean_ptr_addr(x_1296);
lean_dec(x_1296);
x_1318 = lean_ptr_addr(x_1308);
x_1319 = lean_usize_dec_eq(x_1317, x_1318);
if (x_1319 == 0)
{
lean_object* x_1320; 
lean_dec(x_5);
x_1320 = l_Lean_Expr_letE___override(x_1293, x_1299, x_1302, x_1308, x_1297);
lean_ctor_set(x_1306, 0, x_1320);
return x_1306;
}
else
{
lean_dec(x_1308);
lean_dec(x_1302);
lean_dec(x_1299);
lean_dec(x_1293);
lean_ctor_set(x_1306, 0, x_5);
return x_1306;
}
}
}
}
else
{
lean_object* x_1321; lean_object* x_1322; size_t x_1323; size_t x_1324; uint8_t x_1325; 
x_1321 = lean_ctor_get(x_1306, 0);
x_1322 = lean_ctor_get(x_1306, 1);
lean_inc(x_1322);
lean_inc(x_1321);
lean_dec(x_1306);
x_1323 = lean_ptr_addr(x_1294);
lean_dec(x_1294);
x_1324 = lean_ptr_addr(x_1299);
x_1325 = lean_usize_dec_eq(x_1323, x_1324);
if (x_1325 == 0)
{
lean_object* x_1326; lean_object* x_1327; 
lean_dec(x_1296);
lean_dec(x_1295);
lean_dec(x_5);
x_1326 = l_Lean_Expr_letE___override(x_1293, x_1299, x_1302, x_1321, x_1297);
x_1327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1327, 0, x_1326);
lean_ctor_set(x_1327, 1, x_1322);
return x_1327;
}
else
{
size_t x_1328; size_t x_1329; uint8_t x_1330; 
x_1328 = lean_ptr_addr(x_1295);
lean_dec(x_1295);
x_1329 = lean_ptr_addr(x_1302);
x_1330 = lean_usize_dec_eq(x_1328, x_1329);
if (x_1330 == 0)
{
lean_object* x_1331; lean_object* x_1332; 
lean_dec(x_1296);
lean_dec(x_5);
x_1331 = l_Lean_Expr_letE___override(x_1293, x_1299, x_1302, x_1321, x_1297);
x_1332 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1332, 0, x_1331);
lean_ctor_set(x_1332, 1, x_1322);
return x_1332;
}
else
{
size_t x_1333; size_t x_1334; uint8_t x_1335; 
x_1333 = lean_ptr_addr(x_1296);
lean_dec(x_1296);
x_1334 = lean_ptr_addr(x_1321);
x_1335 = lean_usize_dec_eq(x_1333, x_1334);
if (x_1335 == 0)
{
lean_object* x_1336; lean_object* x_1337; 
lean_dec(x_5);
x_1336 = l_Lean_Expr_letE___override(x_1293, x_1299, x_1302, x_1321, x_1297);
x_1337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1337, 0, x_1336);
lean_ctor_set(x_1337, 1, x_1322);
return x_1337;
}
else
{
lean_object* x_1338; 
lean_dec(x_1321);
lean_dec(x_1302);
lean_dec(x_1299);
lean_dec(x_1293);
x_1338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1338, 0, x_5);
lean_ctor_set(x_1338, 1, x_1322);
return x_1338;
}
}
}
}
}
else
{
uint8_t x_1339; 
lean_dec(x_1302);
lean_dec(x_1299);
lean_dec(x_1296);
lean_dec(x_1295);
lean_dec(x_1294);
lean_dec(x_1293);
lean_dec(x_5);
x_1339 = !lean_is_exclusive(x_1306);
if (x_1339 == 0)
{
return x_1306;
}
else
{
lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; 
x_1340 = lean_ctor_get(x_1306, 0);
x_1341 = lean_ctor_get(x_1306, 1);
lean_inc(x_1341);
lean_inc(x_1340);
lean_dec(x_1306);
x_1342 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1342, 0, x_1340);
lean_ctor_set(x_1342, 1, x_1341);
return x_1342;
}
}
}
else
{
uint8_t x_1343; 
lean_dec(x_1299);
lean_dec(x_1296);
lean_dec(x_1295);
lean_dec(x_1294);
lean_dec(x_1293);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1343 = !lean_is_exclusive(x_1301);
if (x_1343 == 0)
{
return x_1301;
}
else
{
lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; 
x_1344 = lean_ctor_get(x_1301, 0);
x_1345 = lean_ctor_get(x_1301, 1);
lean_inc(x_1345);
lean_inc(x_1344);
lean_dec(x_1301);
x_1346 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1346, 0, x_1344);
lean_ctor_set(x_1346, 1, x_1345);
return x_1346;
}
}
}
else
{
uint8_t x_1347; 
lean_dec(x_1296);
lean_dec(x_1295);
lean_dec(x_1294);
lean_dec(x_1293);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1347 = !lean_is_exclusive(x_1298);
if (x_1347 == 0)
{
return x_1298;
}
else
{
lean_object* x_1348; lean_object* x_1349; lean_object* x_1350; 
x_1348 = lean_ctor_get(x_1298, 0);
x_1349 = lean_ctor_get(x_1298, 1);
lean_inc(x_1349);
lean_inc(x_1348);
lean_dec(x_1298);
x_1350 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1350, 0, x_1348);
lean_ctor_set(x_1350, 1, x_1349);
return x_1350;
}
}
}
case 10:
{
lean_object* x_1351; lean_object* x_1352; lean_object* x_1353; 
x_1351 = lean_ctor_get(x_5, 0);
lean_inc(x_1351);
x_1352 = lean_ctor_get(x_5, 1);
lean_inc(x_1352);
lean_inc(x_1352);
x_1353 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1352, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1353) == 0)
{
uint8_t x_1354; 
x_1354 = !lean_is_exclusive(x_1353);
if (x_1354 == 0)
{
lean_object* x_1355; size_t x_1356; size_t x_1357; uint8_t x_1358; 
x_1355 = lean_ctor_get(x_1353, 0);
x_1356 = lean_ptr_addr(x_1352);
lean_dec(x_1352);
x_1357 = lean_ptr_addr(x_1355);
x_1358 = lean_usize_dec_eq(x_1356, x_1357);
if (x_1358 == 0)
{
lean_object* x_1359; 
lean_dec(x_5);
x_1359 = l_Lean_Expr_mdata___override(x_1351, x_1355);
lean_ctor_set(x_1353, 0, x_1359);
return x_1353;
}
else
{
lean_dec(x_1355);
lean_dec(x_1351);
lean_ctor_set(x_1353, 0, x_5);
return x_1353;
}
}
else
{
lean_object* x_1360; lean_object* x_1361; size_t x_1362; size_t x_1363; uint8_t x_1364; 
x_1360 = lean_ctor_get(x_1353, 0);
x_1361 = lean_ctor_get(x_1353, 1);
lean_inc(x_1361);
lean_inc(x_1360);
lean_dec(x_1353);
x_1362 = lean_ptr_addr(x_1352);
lean_dec(x_1352);
x_1363 = lean_ptr_addr(x_1360);
x_1364 = lean_usize_dec_eq(x_1362, x_1363);
if (x_1364 == 0)
{
lean_object* x_1365; lean_object* x_1366; 
lean_dec(x_5);
x_1365 = l_Lean_Expr_mdata___override(x_1351, x_1360);
x_1366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1366, 0, x_1365);
lean_ctor_set(x_1366, 1, x_1361);
return x_1366;
}
else
{
lean_object* x_1367; 
lean_dec(x_1360);
lean_dec(x_1351);
x_1367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1367, 0, x_5);
lean_ctor_set(x_1367, 1, x_1361);
return x_1367;
}
}
}
else
{
uint8_t x_1368; 
lean_dec(x_1352);
lean_dec(x_1351);
lean_dec(x_5);
x_1368 = !lean_is_exclusive(x_1353);
if (x_1368 == 0)
{
return x_1353;
}
else
{
lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; 
x_1369 = lean_ctor_get(x_1353, 0);
x_1370 = lean_ctor_get(x_1353, 1);
lean_inc(x_1370);
lean_inc(x_1369);
lean_dec(x_1353);
x_1371 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1371, 0, x_1369);
lean_ctor_set(x_1371, 1, x_1370);
return x_1371;
}
}
}
case 11:
{
lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; 
x_1372 = lean_ctor_get(x_5, 0);
lean_inc(x_1372);
x_1373 = lean_ctor_get(x_5, 1);
lean_inc(x_1373);
x_1374 = lean_ctor_get(x_5, 2);
lean_inc(x_1374);
lean_inc(x_1374);
x_1375 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1374, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1375) == 0)
{
uint8_t x_1376; 
x_1376 = !lean_is_exclusive(x_1375);
if (x_1376 == 0)
{
lean_object* x_1377; size_t x_1378; size_t x_1379; uint8_t x_1380; 
x_1377 = lean_ctor_get(x_1375, 0);
x_1378 = lean_ptr_addr(x_1374);
lean_dec(x_1374);
x_1379 = lean_ptr_addr(x_1377);
x_1380 = lean_usize_dec_eq(x_1378, x_1379);
if (x_1380 == 0)
{
lean_object* x_1381; 
lean_dec(x_5);
x_1381 = l_Lean_Expr_proj___override(x_1372, x_1373, x_1377);
lean_ctor_set(x_1375, 0, x_1381);
return x_1375;
}
else
{
lean_dec(x_1377);
lean_dec(x_1373);
lean_dec(x_1372);
lean_ctor_set(x_1375, 0, x_5);
return x_1375;
}
}
else
{
lean_object* x_1382; lean_object* x_1383; size_t x_1384; size_t x_1385; uint8_t x_1386; 
x_1382 = lean_ctor_get(x_1375, 0);
x_1383 = lean_ctor_get(x_1375, 1);
lean_inc(x_1383);
lean_inc(x_1382);
lean_dec(x_1375);
x_1384 = lean_ptr_addr(x_1374);
lean_dec(x_1374);
x_1385 = lean_ptr_addr(x_1382);
x_1386 = lean_usize_dec_eq(x_1384, x_1385);
if (x_1386 == 0)
{
lean_object* x_1387; lean_object* x_1388; 
lean_dec(x_5);
x_1387 = l_Lean_Expr_proj___override(x_1372, x_1373, x_1382);
x_1388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1388, 0, x_1387);
lean_ctor_set(x_1388, 1, x_1383);
return x_1388;
}
else
{
lean_object* x_1389; 
lean_dec(x_1382);
lean_dec(x_1373);
lean_dec(x_1372);
x_1389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1389, 0, x_5);
lean_ctor_set(x_1389, 1, x_1383);
return x_1389;
}
}
}
else
{
uint8_t x_1390; 
lean_dec(x_1374);
lean_dec(x_1373);
lean_dec(x_1372);
lean_dec(x_5);
x_1390 = !lean_is_exclusive(x_1375);
if (x_1390 == 0)
{
return x_1375;
}
else
{
lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; 
x_1391 = lean_ctor_get(x_1375, 0);
x_1392 = lean_ctor_get(x_1375, 1);
lean_inc(x_1392);
lean_inc(x_1391);
lean_dec(x_1375);
x_1393 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1393, 0, x_1391);
lean_ctor_set(x_1393, 1, x_1392);
return x_1393;
}
}
}
default: 
{
lean_object* x_1394; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1394, 0, x_5);
lean_ctor_set(x_1394, 1, x_12);
return x_1394;
}
}
}
block_249:
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
lean_inc(x_14);
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
lean_inc(x_15);
x_19 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; size_t x_22; size_t x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ptr_addr(x_14);
lean_dec(x_14);
x_23 = lean_ptr_addr(x_17);
x_24 = lean_usize_dec_eq(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_15);
lean_dec(x_5);
x_25 = l_Lean_Expr_app___override(x_17, x_21);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
size_t x_26; size_t x_27; uint8_t x_28; 
x_26 = lean_ptr_addr(x_15);
lean_dec(x_15);
x_27 = lean_ptr_addr(x_21);
x_28 = lean_usize_dec_eq(x_26, x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_5);
x_29 = l_Lean_Expr_app___override(x_17, x_21);
lean_ctor_set(x_19, 0, x_29);
return x_19;
}
else
{
lean_dec(x_21);
lean_dec(x_17);
lean_ctor_set(x_19, 0, x_5);
return x_19;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_19, 0);
x_31 = lean_ctor_get(x_19, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_19);
x_32 = lean_ptr_addr(x_14);
lean_dec(x_14);
x_33 = lean_ptr_addr(x_17);
x_34 = lean_usize_dec_eq(x_32, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_15);
lean_dec(x_5);
x_35 = l_Lean_Expr_app___override(x_17, x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_31);
return x_36;
}
else
{
size_t x_37; size_t x_38; uint8_t x_39; 
x_37 = lean_ptr_addr(x_15);
lean_dec(x_15);
x_38 = lean_ptr_addr(x_30);
x_39 = lean_usize_dec_eq(x_37, x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
x_40 = l_Lean_Expr_app___override(x_17, x_30);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_31);
return x_41;
}
else
{
lean_object* x_42; 
lean_dec(x_30);
lean_dec(x_17);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_5);
lean_ctor_set(x_42, 1, x_31);
return x_42;
}
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_5);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
return x_19;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_19, 0);
x_45 = lean_ctor_get(x_19, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_19);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
return x_16;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_16, 0);
x_49 = lean_ctor_get(x_16, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_16);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
case 6:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_51 = lean_ctor_get(x_5, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_5, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_5, 2);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_52);
lean_inc(x_1);
x_55 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_52, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_nat_add(x_6, x_58);
lean_dec(x_6);
lean_inc(x_53);
x_60 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_53, x_59, x_7, x_8, x_9, x_10, x_11, x_57);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; size_t x_64; size_t x_65; uint8_t x_66; 
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_63 = l_Lean_Expr_lam___override(x_51, x_52, x_53, x_54);
x_64 = lean_ptr_addr(x_52);
lean_dec(x_52);
x_65 = lean_ptr_addr(x_56);
x_66 = lean_usize_dec_eq(x_64, x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_63);
lean_dec(x_53);
x_67 = l_Lean_Expr_lam___override(x_51, x_56, x_62, x_54);
lean_ctor_set(x_60, 0, x_67);
return x_60;
}
else
{
size_t x_68; size_t x_69; uint8_t x_70; 
x_68 = lean_ptr_addr(x_53);
lean_dec(x_53);
x_69 = lean_ptr_addr(x_62);
x_70 = lean_usize_dec_eq(x_68, x_69);
if (x_70 == 0)
{
lean_object* x_71; 
lean_dec(x_63);
x_71 = l_Lean_Expr_lam___override(x_51, x_56, x_62, x_54);
lean_ctor_set(x_60, 0, x_71);
return x_60;
}
else
{
uint8_t x_72; 
x_72 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_54, x_54);
if (x_72 == 0)
{
lean_object* x_73; 
lean_dec(x_63);
x_73 = l_Lean_Expr_lam___override(x_51, x_56, x_62, x_54);
lean_ctor_set(x_60, 0, x_73);
return x_60;
}
else
{
lean_dec(x_62);
lean_dec(x_56);
lean_dec(x_51);
lean_ctor_set(x_60, 0, x_63);
return x_60;
}
}
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; size_t x_77; size_t x_78; uint8_t x_79; 
x_74 = lean_ctor_get(x_60, 0);
x_75 = lean_ctor_get(x_60, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_60);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
x_76 = l_Lean_Expr_lam___override(x_51, x_52, x_53, x_54);
x_77 = lean_ptr_addr(x_52);
lean_dec(x_52);
x_78 = lean_ptr_addr(x_56);
x_79 = lean_usize_dec_eq(x_77, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_76);
lean_dec(x_53);
x_80 = l_Lean_Expr_lam___override(x_51, x_56, x_74, x_54);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_75);
return x_81;
}
else
{
size_t x_82; size_t x_83; uint8_t x_84; 
x_82 = lean_ptr_addr(x_53);
lean_dec(x_53);
x_83 = lean_ptr_addr(x_74);
x_84 = lean_usize_dec_eq(x_82, x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_76);
x_85 = l_Lean_Expr_lam___override(x_51, x_56, x_74, x_54);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_75);
return x_86;
}
else
{
uint8_t x_87; 
x_87 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_54, x_54);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
lean_dec(x_76);
x_88 = l_Lean_Expr_lam___override(x_51, x_56, x_74, x_54);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_75);
return x_89;
}
else
{
lean_object* x_90; 
lean_dec(x_74);
lean_dec(x_56);
lean_dec(x_51);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_76);
lean_ctor_set(x_90, 1, x_75);
return x_90;
}
}
}
}
}
else
{
uint8_t x_91; 
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
x_91 = !lean_is_exclusive(x_60);
if (x_91 == 0)
{
return x_60;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_60, 0);
x_93 = lean_ctor_get(x_60, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_60);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_55);
if (x_95 == 0)
{
return x_55;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_55, 0);
x_97 = lean_ctor_get(x_55, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_55);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
case 7:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_5, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_5, 1);
lean_inc(x_100);
x_101 = lean_ctor_get(x_5, 2);
lean_inc(x_101);
x_102 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_100);
lean_inc(x_1);
x_103 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_100, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
x_106 = lean_unsigned_to_nat(1u);
x_107 = lean_nat_add(x_6, x_106);
lean_dec(x_6);
lean_inc(x_101);
x_108 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_101, x_107, x_7, x_8, x_9, x_10, x_11, x_105);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; size_t x_112; size_t x_113; uint8_t x_114; 
x_110 = lean_ctor_get(x_108, 0);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
x_111 = l_Lean_Expr_forallE___override(x_99, x_100, x_101, x_102);
x_112 = lean_ptr_addr(x_100);
lean_dec(x_100);
x_113 = lean_ptr_addr(x_104);
x_114 = lean_usize_dec_eq(x_112, x_113);
if (x_114 == 0)
{
lean_object* x_115; 
lean_dec(x_111);
lean_dec(x_101);
x_115 = l_Lean_Expr_forallE___override(x_99, x_104, x_110, x_102);
lean_ctor_set(x_108, 0, x_115);
return x_108;
}
else
{
size_t x_116; size_t x_117; uint8_t x_118; 
x_116 = lean_ptr_addr(x_101);
lean_dec(x_101);
x_117 = lean_ptr_addr(x_110);
x_118 = lean_usize_dec_eq(x_116, x_117);
if (x_118 == 0)
{
lean_object* x_119; 
lean_dec(x_111);
x_119 = l_Lean_Expr_forallE___override(x_99, x_104, x_110, x_102);
lean_ctor_set(x_108, 0, x_119);
return x_108;
}
else
{
uint8_t x_120; 
x_120 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_102, x_102);
if (x_120 == 0)
{
lean_object* x_121; 
lean_dec(x_111);
x_121 = l_Lean_Expr_forallE___override(x_99, x_104, x_110, x_102);
lean_ctor_set(x_108, 0, x_121);
return x_108;
}
else
{
lean_dec(x_110);
lean_dec(x_104);
lean_dec(x_99);
lean_ctor_set(x_108, 0, x_111);
return x_108;
}
}
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; size_t x_125; size_t x_126; uint8_t x_127; 
x_122 = lean_ctor_get(x_108, 0);
x_123 = lean_ctor_get(x_108, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_108);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_99);
x_124 = l_Lean_Expr_forallE___override(x_99, x_100, x_101, x_102);
x_125 = lean_ptr_addr(x_100);
lean_dec(x_100);
x_126 = lean_ptr_addr(x_104);
x_127 = lean_usize_dec_eq(x_125, x_126);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_124);
lean_dec(x_101);
x_128 = l_Lean_Expr_forallE___override(x_99, x_104, x_122, x_102);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_123);
return x_129;
}
else
{
size_t x_130; size_t x_131; uint8_t x_132; 
x_130 = lean_ptr_addr(x_101);
lean_dec(x_101);
x_131 = lean_ptr_addr(x_122);
x_132 = lean_usize_dec_eq(x_130, x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_124);
x_133 = l_Lean_Expr_forallE___override(x_99, x_104, x_122, x_102);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_133);
lean_ctor_set(x_134, 1, x_123);
return x_134;
}
else
{
uint8_t x_135; 
x_135 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_406_(x_102, x_102);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; 
lean_dec(x_124);
x_136 = l_Lean_Expr_forallE___override(x_99, x_104, x_122, x_102);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_123);
return x_137;
}
else
{
lean_object* x_138; 
lean_dec(x_122);
lean_dec(x_104);
lean_dec(x_99);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_124);
lean_ctor_set(x_138, 1, x_123);
return x_138;
}
}
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_104);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
x_139 = !lean_is_exclusive(x_108);
if (x_139 == 0)
{
return x_108;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_108, 0);
x_141 = lean_ctor_get(x_108, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_108);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_143 = !lean_is_exclusive(x_103);
if (x_143 == 0)
{
return x_103;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_103, 0);
x_145 = lean_ctor_get(x_103, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_103);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
case 8:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; 
x_147 = lean_ctor_get(x_5, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_5, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_5, 2);
lean_inc(x_149);
x_150 = lean_ctor_get(x_5, 3);
lean_inc(x_150);
x_151 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_148);
lean_inc(x_1);
x_152 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_148, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_149);
lean_inc(x_1);
x_155 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_149, x_6, x_7, x_8, x_9, x_10, x_11, x_154);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_unsigned_to_nat(1u);
x_159 = lean_nat_add(x_6, x_158);
lean_dec(x_6);
lean_inc(x_150);
x_160 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_150, x_159, x_7, x_8, x_9, x_10, x_11, x_157);
if (lean_obj_tag(x_160) == 0)
{
uint8_t x_161; 
x_161 = !lean_is_exclusive(x_160);
if (x_161 == 0)
{
lean_object* x_162; size_t x_163; size_t x_164; uint8_t x_165; 
x_162 = lean_ctor_get(x_160, 0);
x_163 = lean_ptr_addr(x_148);
lean_dec(x_148);
x_164 = lean_ptr_addr(x_153);
x_165 = lean_usize_dec_eq(x_163, x_164);
if (x_165 == 0)
{
lean_object* x_166; 
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_5);
x_166 = l_Lean_Expr_letE___override(x_147, x_153, x_156, x_162, x_151);
lean_ctor_set(x_160, 0, x_166);
return x_160;
}
else
{
size_t x_167; size_t x_168; uint8_t x_169; 
x_167 = lean_ptr_addr(x_149);
lean_dec(x_149);
x_168 = lean_ptr_addr(x_156);
x_169 = lean_usize_dec_eq(x_167, x_168);
if (x_169 == 0)
{
lean_object* x_170; 
lean_dec(x_150);
lean_dec(x_5);
x_170 = l_Lean_Expr_letE___override(x_147, x_153, x_156, x_162, x_151);
lean_ctor_set(x_160, 0, x_170);
return x_160;
}
else
{
size_t x_171; size_t x_172; uint8_t x_173; 
x_171 = lean_ptr_addr(x_150);
lean_dec(x_150);
x_172 = lean_ptr_addr(x_162);
x_173 = lean_usize_dec_eq(x_171, x_172);
if (x_173 == 0)
{
lean_object* x_174; 
lean_dec(x_5);
x_174 = l_Lean_Expr_letE___override(x_147, x_153, x_156, x_162, x_151);
lean_ctor_set(x_160, 0, x_174);
return x_160;
}
else
{
lean_dec(x_162);
lean_dec(x_156);
lean_dec(x_153);
lean_dec(x_147);
lean_ctor_set(x_160, 0, x_5);
return x_160;
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; size_t x_177; size_t x_178; uint8_t x_179; 
x_175 = lean_ctor_get(x_160, 0);
x_176 = lean_ctor_get(x_160, 1);
lean_inc(x_176);
lean_inc(x_175);
lean_dec(x_160);
x_177 = lean_ptr_addr(x_148);
lean_dec(x_148);
x_178 = lean_ptr_addr(x_153);
x_179 = lean_usize_dec_eq(x_177, x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_5);
x_180 = l_Lean_Expr_letE___override(x_147, x_153, x_156, x_175, x_151);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_176);
return x_181;
}
else
{
size_t x_182; size_t x_183; uint8_t x_184; 
x_182 = lean_ptr_addr(x_149);
lean_dec(x_149);
x_183 = lean_ptr_addr(x_156);
x_184 = lean_usize_dec_eq(x_182, x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
lean_dec(x_150);
lean_dec(x_5);
x_185 = l_Lean_Expr_letE___override(x_147, x_153, x_156, x_175, x_151);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_176);
return x_186;
}
else
{
size_t x_187; size_t x_188; uint8_t x_189; 
x_187 = lean_ptr_addr(x_150);
lean_dec(x_150);
x_188 = lean_ptr_addr(x_175);
x_189 = lean_usize_dec_eq(x_187, x_188);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_5);
x_190 = l_Lean_Expr_letE___override(x_147, x_153, x_156, x_175, x_151);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_176);
return x_191;
}
else
{
lean_object* x_192; 
lean_dec(x_175);
lean_dec(x_156);
lean_dec(x_153);
lean_dec(x_147);
x_192 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_192, 0, x_5);
lean_ctor_set(x_192, 1, x_176);
return x_192;
}
}
}
}
}
else
{
uint8_t x_193; 
lean_dec(x_156);
lean_dec(x_153);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_5);
x_193 = !lean_is_exclusive(x_160);
if (x_193 == 0)
{
return x_160;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_194 = lean_ctor_get(x_160, 0);
x_195 = lean_ctor_get(x_160, 1);
lean_inc(x_195);
lean_inc(x_194);
lean_dec(x_160);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_194);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
}
}
else
{
uint8_t x_197; 
lean_dec(x_153);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_197 = !lean_is_exclusive(x_155);
if (x_197 == 0)
{
return x_155;
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_198 = lean_ctor_get(x_155, 0);
x_199 = lean_ctor_get(x_155, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_155);
x_200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_200, 0, x_198);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
else
{
uint8_t x_201; 
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_201 = !lean_is_exclusive(x_152);
if (x_201 == 0)
{
return x_152;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_152, 0);
x_203 = lean_ctor_get(x_152, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_152);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
case 10:
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_5, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_5, 1);
lean_inc(x_206);
lean_inc(x_206);
x_207 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_206, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_207) == 0)
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; size_t x_210; size_t x_211; uint8_t x_212; 
x_209 = lean_ctor_get(x_207, 0);
x_210 = lean_ptr_addr(x_206);
lean_dec(x_206);
x_211 = lean_ptr_addr(x_209);
x_212 = lean_usize_dec_eq(x_210, x_211);
if (x_212 == 0)
{
lean_object* x_213; 
lean_dec(x_5);
x_213 = l_Lean_Expr_mdata___override(x_205, x_209);
lean_ctor_set(x_207, 0, x_213);
return x_207;
}
else
{
lean_dec(x_209);
lean_dec(x_205);
lean_ctor_set(x_207, 0, x_5);
return x_207;
}
}
else
{
lean_object* x_214; lean_object* x_215; size_t x_216; size_t x_217; uint8_t x_218; 
x_214 = lean_ctor_get(x_207, 0);
x_215 = lean_ctor_get(x_207, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_207);
x_216 = lean_ptr_addr(x_206);
lean_dec(x_206);
x_217 = lean_ptr_addr(x_214);
x_218 = lean_usize_dec_eq(x_216, x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_5);
x_219 = l_Lean_Expr_mdata___override(x_205, x_214);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_215);
return x_220;
}
else
{
lean_object* x_221; 
lean_dec(x_214);
lean_dec(x_205);
x_221 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_221, 0, x_5);
lean_ctor_set(x_221, 1, x_215);
return x_221;
}
}
}
else
{
uint8_t x_222; 
lean_dec(x_206);
lean_dec(x_205);
lean_dec(x_5);
x_222 = !lean_is_exclusive(x_207);
if (x_222 == 0)
{
return x_207;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_207, 0);
x_224 = lean_ctor_get(x_207, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_207);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
case 11:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_226 = lean_ctor_get(x_5, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_5, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_5, 2);
lean_inc(x_228);
lean_inc(x_228);
x_229 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_228, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_229) == 0)
{
uint8_t x_230; 
x_230 = !lean_is_exclusive(x_229);
if (x_230 == 0)
{
lean_object* x_231; size_t x_232; size_t x_233; uint8_t x_234; 
x_231 = lean_ctor_get(x_229, 0);
x_232 = lean_ptr_addr(x_228);
lean_dec(x_228);
x_233 = lean_ptr_addr(x_231);
x_234 = lean_usize_dec_eq(x_232, x_233);
if (x_234 == 0)
{
lean_object* x_235; 
lean_dec(x_5);
x_235 = l_Lean_Expr_proj___override(x_226, x_227, x_231);
lean_ctor_set(x_229, 0, x_235);
return x_229;
}
else
{
lean_dec(x_231);
lean_dec(x_227);
lean_dec(x_226);
lean_ctor_set(x_229, 0, x_5);
return x_229;
}
}
else
{
lean_object* x_236; lean_object* x_237; size_t x_238; size_t x_239; uint8_t x_240; 
x_236 = lean_ctor_get(x_229, 0);
x_237 = lean_ctor_get(x_229, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_229);
x_238 = lean_ptr_addr(x_228);
lean_dec(x_228);
x_239 = lean_ptr_addr(x_236);
x_240 = lean_usize_dec_eq(x_238, x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; 
lean_dec(x_5);
x_241 = l_Lean_Expr_proj___override(x_226, x_227, x_236);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set(x_242, 1, x_237);
return x_242;
}
else
{
lean_object* x_243; 
lean_dec(x_236);
lean_dec(x_227);
lean_dec(x_226);
x_243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_243, 0, x_5);
lean_ctor_set(x_243, 1, x_237);
return x_243;
}
}
}
else
{
uint8_t x_244; 
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_5);
x_244 = !lean_is_exclusive(x_229);
if (x_244 == 0)
{
return x_229;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_229, 0);
x_246 = lean_ctor_get(x_229, 1);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_229);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
return x_247;
}
}
}
default: 
{
lean_object* x_248; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_5);
lean_ctor_set(x_248, 1, x_12);
return x_248;
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
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(x_1, x_4, x_5, x_6, x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = l_Lean_Expr_isFVar(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_9);
lean_inc(x_2);
x_14 = l_Lean_Expr_toHeadIndex(x_2);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Expr_headNumArgs_go(x_2, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_st_mk_ref(x_17, x_12);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_14, x_16, x_11, x_15, x_19, x_4, x_5, x_6, x_7, x_20);
lean_dec(x_16);
lean_dec(x_14);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_get(x_19, x_23);
lean_dec(x_19);
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
uint8_t x_29; 
lean_dec(x_19);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
return x_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = lean_ctor_get(x_21, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_21);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_box(0);
x_34 = l___private_Init_MetaTypes_0__Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1231_(x_3, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_9);
lean_inc(x_2);
x_35 = l_Lean_Expr_toHeadIndex(x_2);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_Expr_headNumArgs_go(x_2, x_36);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_st_mk_ref(x_38, x_12);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_35, x_37, x_11, x_36, x_40, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_37);
lean_dec(x_35);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_st_ref_get(x_40, x_44);
lean_dec(x_40);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_43);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_43);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
lean_dec(x_40);
x_50 = !lean_is_exclusive(x_42);
if (x_50 == 0)
{
return x_42;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_42, 0);
x_52 = lean_ctor_get(x_42, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_42);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_54 = lean_box(0);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_2);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_array_mk(x_55);
x_57 = lean_expr_abstract(x_11, x_56);
lean_dec(x_56);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_57);
return x_9;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_9, 0);
x_59 = lean_ctor_get(x_9, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_9);
x_60 = l_Lean_Expr_isFVar(x_2);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_inc(x_2);
x_61 = l_Lean_Expr_toHeadIndex(x_2);
x_62 = lean_unsigned_to_nat(0u);
x_63 = l_Lean_Expr_headNumArgs_go(x_2, x_62);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_st_mk_ref(x_64, x_59);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_61, x_63, x_58, x_62, x_66, x_4, x_5, x_6, x_7, x_67);
lean_dec(x_63);
lean_dec(x_61);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_st_ref_get(x_66, x_70);
lean_dec(x_66);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_69);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_66);
x_75 = lean_ctor_get(x_68, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_68, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_77 = x_68;
} else {
 lean_dec_ref(x_68);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_box(0);
x_80 = l___private_Init_MetaTypes_0__Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1231_(x_3, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_inc(x_2);
x_81 = l_Lean_Expr_toHeadIndex(x_2);
x_82 = lean_unsigned_to_nat(0u);
x_83 = l_Lean_Expr_headNumArgs_go(x_2, x_82);
x_84 = lean_unsigned_to_nat(1u);
x_85 = lean_st_mk_ref(x_84, x_59);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_81, x_83, x_58, x_82, x_86, x_4, x_5, x_6, x_7, x_87);
lean_dec(x_83);
lean_dec(x_81);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_st_ref_get(x_86, x_90);
lean_dec(x_86);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_93 = x_91;
} else {
 lean_dec_ref(x_91);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_89);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_86);
x_95 = lean_ctor_get(x_88, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_88, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_97 = x_88;
} else {
 lean_dec_ref(x_88);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_2);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_array_mk(x_100);
x_102 = lean_expr_abstract(x_58, x_101);
lean_dec(x_101);
lean_dec(x_58);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_59);
return x_103;
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
