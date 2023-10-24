// Lean compiler output
// Module: Lean.Meta.KAbstract
// Imports: Init Lean.HeadIndex Lean.Meta.Basic
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_headNumArgs_go(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f___spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_67_(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(uint8_t, uint8_t);
static lean_object* l_Lean_Meta_kabstract___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Occurrences_contains(lean_object*, lean_object*);
uint8_t l___private_Init_Meta_0__Lean_Meta_beqOccurrences____x40_Init_Meta___hyg_14366_(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isFVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_267; 
x_267 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_267 == 0)
{
lean_object* x_268; uint8_t x_269; 
lean_inc(x_5);
x_268 = l_Lean_Expr_toHeadIndex(x_5);
x_269 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_67_(x_268, x_3);
lean_dec(x_268);
if (x_269 == 0)
{
lean_object* x_270; 
x_270 = lean_box(0);
x_13 = x_270;
goto block_266;
}
else
{
lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_271 = lean_unsigned_to_nat(0u);
x_272 = l_Lean_Expr_headNumArgs_go(x_5, x_271);
x_273 = lean_nat_dec_eq(x_272, x_4);
lean_dec(x_272);
if (x_273 == 0)
{
lean_object* x_274; 
x_274 = lean_box(0);
x_13 = x_274;
goto block_266;
}
else
{
lean_object* x_275; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_5);
x_275 = l_Lean_Meta_isExprDefEq(x_5, x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; uint8_t x_277; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_unbox(x_276);
lean_dec(x_276);
if (x_277 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_278 = lean_ctor_get(x_275, 1);
lean_inc(x_278);
lean_dec(x_275);
x_279 = lean_ctor_get(x_5, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_5, 1);
lean_inc(x_280);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_279);
lean_inc(x_1);
x_281 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_279, x_6, x_7, x_8, x_9, x_10, x_11, x_278);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
lean_inc(x_280);
x_284 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_280, x_6, x_7, x_8, x_9, x_10, x_11, x_283);
if (lean_obj_tag(x_284) == 0)
{
uint8_t x_285; 
x_285 = !lean_is_exclusive(x_284);
if (x_285 == 0)
{
lean_object* x_286; size_t x_287; size_t x_288; uint8_t x_289; 
x_286 = lean_ctor_get(x_284, 0);
x_287 = lean_ptr_addr(x_279);
lean_dec(x_279);
x_288 = lean_ptr_addr(x_282);
x_289 = lean_usize_dec_eq(x_287, x_288);
if (x_289 == 0)
{
lean_object* x_290; 
lean_dec(x_280);
lean_dec(x_5);
x_290 = l_Lean_Expr_app___override(x_282, x_286);
lean_ctor_set(x_284, 0, x_290);
return x_284;
}
else
{
size_t x_291; size_t x_292; uint8_t x_293; 
x_291 = lean_ptr_addr(x_280);
lean_dec(x_280);
x_292 = lean_ptr_addr(x_286);
x_293 = lean_usize_dec_eq(x_291, x_292);
if (x_293 == 0)
{
lean_object* x_294; 
lean_dec(x_5);
x_294 = l_Lean_Expr_app___override(x_282, x_286);
lean_ctor_set(x_284, 0, x_294);
return x_284;
}
else
{
lean_dec(x_286);
lean_dec(x_282);
lean_ctor_set(x_284, 0, x_5);
return x_284;
}
}
}
else
{
lean_object* x_295; lean_object* x_296; size_t x_297; size_t x_298; uint8_t x_299; 
x_295 = lean_ctor_get(x_284, 0);
x_296 = lean_ctor_get(x_284, 1);
lean_inc(x_296);
lean_inc(x_295);
lean_dec(x_284);
x_297 = lean_ptr_addr(x_279);
lean_dec(x_279);
x_298 = lean_ptr_addr(x_282);
x_299 = lean_usize_dec_eq(x_297, x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; 
lean_dec(x_280);
lean_dec(x_5);
x_300 = l_Lean_Expr_app___override(x_282, x_295);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_296);
return x_301;
}
else
{
size_t x_302; size_t x_303; uint8_t x_304; 
x_302 = lean_ptr_addr(x_280);
lean_dec(x_280);
x_303 = lean_ptr_addr(x_295);
x_304 = lean_usize_dec_eq(x_302, x_303);
if (x_304 == 0)
{
lean_object* x_305; lean_object* x_306; 
lean_dec(x_5);
x_305 = l_Lean_Expr_app___override(x_282, x_295);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_296);
return x_306;
}
else
{
lean_object* x_307; 
lean_dec(x_295);
lean_dec(x_282);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_5);
lean_ctor_set(x_307, 1, x_296);
return x_307;
}
}
}
}
else
{
uint8_t x_308; 
lean_dec(x_282);
lean_dec(x_280);
lean_dec(x_279);
lean_dec(x_5);
x_308 = !lean_is_exclusive(x_284);
if (x_308 == 0)
{
return x_284;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_284, 0);
x_310 = lean_ctor_get(x_284, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_284);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
else
{
uint8_t x_312; 
lean_dec(x_280);
lean_dec(x_279);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_312 = !lean_is_exclusive(x_281);
if (x_312 == 0)
{
return x_281;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_281, 0);
x_314 = lean_ctor_get(x_281, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_281);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
return x_315;
}
}
}
case 6:
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; 
x_316 = lean_ctor_get(x_275, 1);
lean_inc(x_316);
lean_dec(x_275);
x_317 = lean_ctor_get(x_5, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_5, 1);
lean_inc(x_318);
x_319 = lean_ctor_get(x_5, 2);
lean_inc(x_319);
x_320 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_318);
lean_inc(x_1);
x_321 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_318, x_6, x_7, x_8, x_9, x_10, x_11, x_316);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_321, 1);
lean_inc(x_323);
lean_dec(x_321);
x_324 = lean_unsigned_to_nat(1u);
x_325 = lean_nat_add(x_6, x_324);
lean_dec(x_6);
lean_inc(x_319);
x_326 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_319, x_325, x_7, x_8, x_9, x_10, x_11, x_323);
if (lean_obj_tag(x_326) == 0)
{
uint8_t x_327; 
x_327 = !lean_is_exclusive(x_326);
if (x_327 == 0)
{
lean_object* x_328; lean_object* x_329; size_t x_330; size_t x_331; uint8_t x_332; 
x_328 = lean_ctor_get(x_326, 0);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
x_329 = l_Lean_Expr_lam___override(x_317, x_318, x_319, x_320);
x_330 = lean_ptr_addr(x_318);
lean_dec(x_318);
x_331 = lean_ptr_addr(x_322);
x_332 = lean_usize_dec_eq(x_330, x_331);
if (x_332 == 0)
{
lean_object* x_333; 
lean_dec(x_329);
lean_dec(x_319);
x_333 = l_Lean_Expr_lam___override(x_317, x_322, x_328, x_320);
lean_ctor_set(x_326, 0, x_333);
return x_326;
}
else
{
size_t x_334; size_t x_335; uint8_t x_336; 
x_334 = lean_ptr_addr(x_319);
lean_dec(x_319);
x_335 = lean_ptr_addr(x_328);
x_336 = lean_usize_dec_eq(x_334, x_335);
if (x_336 == 0)
{
lean_object* x_337; 
lean_dec(x_329);
x_337 = l_Lean_Expr_lam___override(x_317, x_322, x_328, x_320);
lean_ctor_set(x_326, 0, x_337);
return x_326;
}
else
{
uint8_t x_338; 
x_338 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_320, x_320);
if (x_338 == 0)
{
lean_object* x_339; 
lean_dec(x_329);
x_339 = l_Lean_Expr_lam___override(x_317, x_322, x_328, x_320);
lean_ctor_set(x_326, 0, x_339);
return x_326;
}
else
{
lean_dec(x_328);
lean_dec(x_322);
lean_dec(x_317);
lean_ctor_set(x_326, 0, x_329);
return x_326;
}
}
}
}
else
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; size_t x_343; size_t x_344; uint8_t x_345; 
x_340 = lean_ctor_get(x_326, 0);
x_341 = lean_ctor_get(x_326, 1);
lean_inc(x_341);
lean_inc(x_340);
lean_dec(x_326);
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
x_342 = l_Lean_Expr_lam___override(x_317, x_318, x_319, x_320);
x_343 = lean_ptr_addr(x_318);
lean_dec(x_318);
x_344 = lean_ptr_addr(x_322);
x_345 = lean_usize_dec_eq(x_343, x_344);
if (x_345 == 0)
{
lean_object* x_346; lean_object* x_347; 
lean_dec(x_342);
lean_dec(x_319);
x_346 = l_Lean_Expr_lam___override(x_317, x_322, x_340, x_320);
x_347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set(x_347, 1, x_341);
return x_347;
}
else
{
size_t x_348; size_t x_349; uint8_t x_350; 
x_348 = lean_ptr_addr(x_319);
lean_dec(x_319);
x_349 = lean_ptr_addr(x_340);
x_350 = lean_usize_dec_eq(x_348, x_349);
if (x_350 == 0)
{
lean_object* x_351; lean_object* x_352; 
lean_dec(x_342);
x_351 = l_Lean_Expr_lam___override(x_317, x_322, x_340, x_320);
x_352 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_352, 0, x_351);
lean_ctor_set(x_352, 1, x_341);
return x_352;
}
else
{
uint8_t x_353; 
x_353 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_320, x_320);
if (x_353 == 0)
{
lean_object* x_354; lean_object* x_355; 
lean_dec(x_342);
x_354 = l_Lean_Expr_lam___override(x_317, x_322, x_340, x_320);
x_355 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_355, 0, x_354);
lean_ctor_set(x_355, 1, x_341);
return x_355;
}
else
{
lean_object* x_356; 
lean_dec(x_340);
lean_dec(x_322);
lean_dec(x_317);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_342);
lean_ctor_set(x_356, 1, x_341);
return x_356;
}
}
}
}
}
else
{
uint8_t x_357; 
lean_dec(x_322);
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_317);
x_357 = !lean_is_exclusive(x_326);
if (x_357 == 0)
{
return x_326;
}
else
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_326, 0);
x_359 = lean_ctor_get(x_326, 1);
lean_inc(x_359);
lean_inc(x_358);
lean_dec(x_326);
x_360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_360, 0, x_358);
lean_ctor_set(x_360, 1, x_359);
return x_360;
}
}
}
else
{
uint8_t x_361; 
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_361 = !lean_is_exclusive(x_321);
if (x_361 == 0)
{
return x_321;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_321, 0);
x_363 = lean_ctor_get(x_321, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_321);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
return x_364;
}
}
}
case 7:
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; uint8_t x_369; lean_object* x_370; 
x_365 = lean_ctor_get(x_275, 1);
lean_inc(x_365);
lean_dec(x_275);
x_366 = lean_ctor_get(x_5, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_5, 1);
lean_inc(x_367);
x_368 = lean_ctor_get(x_5, 2);
lean_inc(x_368);
x_369 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_367);
lean_inc(x_1);
x_370 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_367, x_6, x_7, x_8, x_9, x_10, x_11, x_365);
if (lean_obj_tag(x_370) == 0)
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_371 = lean_ctor_get(x_370, 0);
lean_inc(x_371);
x_372 = lean_ctor_get(x_370, 1);
lean_inc(x_372);
lean_dec(x_370);
x_373 = lean_unsigned_to_nat(1u);
x_374 = lean_nat_add(x_6, x_373);
lean_dec(x_6);
lean_inc(x_368);
x_375 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_368, x_374, x_7, x_8, x_9, x_10, x_11, x_372);
if (lean_obj_tag(x_375) == 0)
{
uint8_t x_376; 
x_376 = !lean_is_exclusive(x_375);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; size_t x_379; size_t x_380; uint8_t x_381; 
x_377 = lean_ctor_get(x_375, 0);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
x_378 = l_Lean_Expr_forallE___override(x_366, x_367, x_368, x_369);
x_379 = lean_ptr_addr(x_367);
lean_dec(x_367);
x_380 = lean_ptr_addr(x_371);
x_381 = lean_usize_dec_eq(x_379, x_380);
if (x_381 == 0)
{
lean_object* x_382; 
lean_dec(x_378);
lean_dec(x_368);
x_382 = l_Lean_Expr_forallE___override(x_366, x_371, x_377, x_369);
lean_ctor_set(x_375, 0, x_382);
return x_375;
}
else
{
size_t x_383; size_t x_384; uint8_t x_385; 
x_383 = lean_ptr_addr(x_368);
lean_dec(x_368);
x_384 = lean_ptr_addr(x_377);
x_385 = lean_usize_dec_eq(x_383, x_384);
if (x_385 == 0)
{
lean_object* x_386; 
lean_dec(x_378);
x_386 = l_Lean_Expr_forallE___override(x_366, x_371, x_377, x_369);
lean_ctor_set(x_375, 0, x_386);
return x_375;
}
else
{
uint8_t x_387; 
x_387 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_369, x_369);
if (x_387 == 0)
{
lean_object* x_388; 
lean_dec(x_378);
x_388 = l_Lean_Expr_forallE___override(x_366, x_371, x_377, x_369);
lean_ctor_set(x_375, 0, x_388);
return x_375;
}
else
{
lean_dec(x_377);
lean_dec(x_371);
lean_dec(x_366);
lean_ctor_set(x_375, 0, x_378);
return x_375;
}
}
}
}
else
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; size_t x_392; size_t x_393; uint8_t x_394; 
x_389 = lean_ctor_get(x_375, 0);
x_390 = lean_ctor_get(x_375, 1);
lean_inc(x_390);
lean_inc(x_389);
lean_dec(x_375);
lean_inc(x_368);
lean_inc(x_367);
lean_inc(x_366);
x_391 = l_Lean_Expr_forallE___override(x_366, x_367, x_368, x_369);
x_392 = lean_ptr_addr(x_367);
lean_dec(x_367);
x_393 = lean_ptr_addr(x_371);
x_394 = lean_usize_dec_eq(x_392, x_393);
if (x_394 == 0)
{
lean_object* x_395; lean_object* x_396; 
lean_dec(x_391);
lean_dec(x_368);
x_395 = l_Lean_Expr_forallE___override(x_366, x_371, x_389, x_369);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_390);
return x_396;
}
else
{
size_t x_397; size_t x_398; uint8_t x_399; 
x_397 = lean_ptr_addr(x_368);
lean_dec(x_368);
x_398 = lean_ptr_addr(x_389);
x_399 = lean_usize_dec_eq(x_397, x_398);
if (x_399 == 0)
{
lean_object* x_400; lean_object* x_401; 
lean_dec(x_391);
x_400 = l_Lean_Expr_forallE___override(x_366, x_371, x_389, x_369);
x_401 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_401, 0, x_400);
lean_ctor_set(x_401, 1, x_390);
return x_401;
}
else
{
uint8_t x_402; 
x_402 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_369, x_369);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; 
lean_dec(x_391);
x_403 = l_Lean_Expr_forallE___override(x_366, x_371, x_389, x_369);
x_404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_390);
return x_404;
}
else
{
lean_object* x_405; 
lean_dec(x_389);
lean_dec(x_371);
lean_dec(x_366);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_391);
lean_ctor_set(x_405, 1, x_390);
return x_405;
}
}
}
}
}
else
{
uint8_t x_406; 
lean_dec(x_371);
lean_dec(x_368);
lean_dec(x_367);
lean_dec(x_366);
x_406 = !lean_is_exclusive(x_375);
if (x_406 == 0)
{
return x_375;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; 
x_407 = lean_ctor_get(x_375, 0);
x_408 = lean_ctor_get(x_375, 1);
lean_inc(x_408);
lean_inc(x_407);
lean_dec(x_375);
x_409 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
return x_409;
}
}
}
else
{
uint8_t x_410; 
lean_dec(x_368);
lean_dec(x_367);
lean_dec(x_366);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_410 = !lean_is_exclusive(x_370);
if (x_410 == 0)
{
return x_370;
}
else
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; 
x_411 = lean_ctor_get(x_370, 0);
x_412 = lean_ctor_get(x_370, 1);
lean_inc(x_412);
lean_inc(x_411);
lean_dec(x_370);
x_413 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_413, 0, x_411);
lean_ctor_set(x_413, 1, x_412);
return x_413;
}
}
}
case 8:
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; lean_object* x_420; 
x_414 = lean_ctor_get(x_275, 1);
lean_inc(x_414);
lean_dec(x_275);
x_415 = lean_ctor_get(x_5, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_5, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_5, 2);
lean_inc(x_417);
x_418 = lean_ctor_get(x_5, 3);
lean_inc(x_418);
x_419 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_416);
lean_inc(x_1);
x_420 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_416, x_6, x_7, x_8, x_9, x_10, x_11, x_414);
if (lean_obj_tag(x_420) == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_421 = lean_ctor_get(x_420, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_420, 1);
lean_inc(x_422);
lean_dec(x_420);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_417);
lean_inc(x_1);
x_423 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_417, x_6, x_7, x_8, x_9, x_10, x_11, x_422);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
lean_dec(x_423);
x_426 = lean_unsigned_to_nat(1u);
x_427 = lean_nat_add(x_6, x_426);
lean_dec(x_6);
lean_inc(x_418);
x_428 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_418, x_427, x_7, x_8, x_9, x_10, x_11, x_425);
if (lean_obj_tag(x_428) == 0)
{
uint8_t x_429; 
x_429 = !lean_is_exclusive(x_428);
if (x_429 == 0)
{
lean_object* x_430; size_t x_431; size_t x_432; uint8_t x_433; 
x_430 = lean_ctor_get(x_428, 0);
x_431 = lean_ptr_addr(x_416);
lean_dec(x_416);
x_432 = lean_ptr_addr(x_421);
x_433 = lean_usize_dec_eq(x_431, x_432);
if (x_433 == 0)
{
lean_object* x_434; 
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_5);
x_434 = l_Lean_Expr_letE___override(x_415, x_421, x_424, x_430, x_419);
lean_ctor_set(x_428, 0, x_434);
return x_428;
}
else
{
size_t x_435; size_t x_436; uint8_t x_437; 
x_435 = lean_ptr_addr(x_417);
lean_dec(x_417);
x_436 = lean_ptr_addr(x_424);
x_437 = lean_usize_dec_eq(x_435, x_436);
if (x_437 == 0)
{
lean_object* x_438; 
lean_dec(x_418);
lean_dec(x_5);
x_438 = l_Lean_Expr_letE___override(x_415, x_421, x_424, x_430, x_419);
lean_ctor_set(x_428, 0, x_438);
return x_428;
}
else
{
size_t x_439; size_t x_440; uint8_t x_441; 
x_439 = lean_ptr_addr(x_418);
lean_dec(x_418);
x_440 = lean_ptr_addr(x_430);
x_441 = lean_usize_dec_eq(x_439, x_440);
if (x_441 == 0)
{
lean_object* x_442; 
lean_dec(x_5);
x_442 = l_Lean_Expr_letE___override(x_415, x_421, x_424, x_430, x_419);
lean_ctor_set(x_428, 0, x_442);
return x_428;
}
else
{
lean_dec(x_430);
lean_dec(x_424);
lean_dec(x_421);
lean_dec(x_415);
lean_ctor_set(x_428, 0, x_5);
return x_428;
}
}
}
}
else
{
lean_object* x_443; lean_object* x_444; size_t x_445; size_t x_446; uint8_t x_447; 
x_443 = lean_ctor_get(x_428, 0);
x_444 = lean_ctor_get(x_428, 1);
lean_inc(x_444);
lean_inc(x_443);
lean_dec(x_428);
x_445 = lean_ptr_addr(x_416);
lean_dec(x_416);
x_446 = lean_ptr_addr(x_421);
x_447 = lean_usize_dec_eq(x_445, x_446);
if (x_447 == 0)
{
lean_object* x_448; lean_object* x_449; 
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_5);
x_448 = l_Lean_Expr_letE___override(x_415, x_421, x_424, x_443, x_419);
x_449 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_449, 0, x_448);
lean_ctor_set(x_449, 1, x_444);
return x_449;
}
else
{
size_t x_450; size_t x_451; uint8_t x_452; 
x_450 = lean_ptr_addr(x_417);
lean_dec(x_417);
x_451 = lean_ptr_addr(x_424);
x_452 = lean_usize_dec_eq(x_450, x_451);
if (x_452 == 0)
{
lean_object* x_453; lean_object* x_454; 
lean_dec(x_418);
lean_dec(x_5);
x_453 = l_Lean_Expr_letE___override(x_415, x_421, x_424, x_443, x_419);
x_454 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_454, 0, x_453);
lean_ctor_set(x_454, 1, x_444);
return x_454;
}
else
{
size_t x_455; size_t x_456; uint8_t x_457; 
x_455 = lean_ptr_addr(x_418);
lean_dec(x_418);
x_456 = lean_ptr_addr(x_443);
x_457 = lean_usize_dec_eq(x_455, x_456);
if (x_457 == 0)
{
lean_object* x_458; lean_object* x_459; 
lean_dec(x_5);
x_458 = l_Lean_Expr_letE___override(x_415, x_421, x_424, x_443, x_419);
x_459 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_459, 0, x_458);
lean_ctor_set(x_459, 1, x_444);
return x_459;
}
else
{
lean_object* x_460; 
lean_dec(x_443);
lean_dec(x_424);
lean_dec(x_421);
lean_dec(x_415);
x_460 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_460, 0, x_5);
lean_ctor_set(x_460, 1, x_444);
return x_460;
}
}
}
}
}
else
{
uint8_t x_461; 
lean_dec(x_424);
lean_dec(x_421);
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_5);
x_461 = !lean_is_exclusive(x_428);
if (x_461 == 0)
{
return x_428;
}
else
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_462 = lean_ctor_get(x_428, 0);
x_463 = lean_ctor_get(x_428, 1);
lean_inc(x_463);
lean_inc(x_462);
lean_dec(x_428);
x_464 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_464, 0, x_462);
lean_ctor_set(x_464, 1, x_463);
return x_464;
}
}
}
else
{
uint8_t x_465; 
lean_dec(x_421);
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_465 = !lean_is_exclusive(x_423);
if (x_465 == 0)
{
return x_423;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_466 = lean_ctor_get(x_423, 0);
x_467 = lean_ctor_get(x_423, 1);
lean_inc(x_467);
lean_inc(x_466);
lean_dec(x_423);
x_468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_468, 0, x_466);
lean_ctor_set(x_468, 1, x_467);
return x_468;
}
}
}
else
{
uint8_t x_469; 
lean_dec(x_418);
lean_dec(x_417);
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_469 = !lean_is_exclusive(x_420);
if (x_469 == 0)
{
return x_420;
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; 
x_470 = lean_ctor_get(x_420, 0);
x_471 = lean_ctor_get(x_420, 1);
lean_inc(x_471);
lean_inc(x_470);
lean_dec(x_420);
x_472 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_472, 0, x_470);
lean_ctor_set(x_472, 1, x_471);
return x_472;
}
}
}
case 10:
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
x_473 = lean_ctor_get(x_275, 1);
lean_inc(x_473);
lean_dec(x_275);
x_474 = lean_ctor_get(x_5, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_5, 1);
lean_inc(x_475);
lean_inc(x_475);
x_476 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_475, x_6, x_7, x_8, x_9, x_10, x_11, x_473);
if (lean_obj_tag(x_476) == 0)
{
uint8_t x_477; 
x_477 = !lean_is_exclusive(x_476);
if (x_477 == 0)
{
lean_object* x_478; size_t x_479; size_t x_480; uint8_t x_481; 
x_478 = lean_ctor_get(x_476, 0);
x_479 = lean_ptr_addr(x_475);
lean_dec(x_475);
x_480 = lean_ptr_addr(x_478);
x_481 = lean_usize_dec_eq(x_479, x_480);
if (x_481 == 0)
{
lean_object* x_482; 
lean_dec(x_5);
x_482 = l_Lean_Expr_mdata___override(x_474, x_478);
lean_ctor_set(x_476, 0, x_482);
return x_476;
}
else
{
lean_dec(x_478);
lean_dec(x_474);
lean_ctor_set(x_476, 0, x_5);
return x_476;
}
}
else
{
lean_object* x_483; lean_object* x_484; size_t x_485; size_t x_486; uint8_t x_487; 
x_483 = lean_ctor_get(x_476, 0);
x_484 = lean_ctor_get(x_476, 1);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_476);
x_485 = lean_ptr_addr(x_475);
lean_dec(x_475);
x_486 = lean_ptr_addr(x_483);
x_487 = lean_usize_dec_eq(x_485, x_486);
if (x_487 == 0)
{
lean_object* x_488; lean_object* x_489; 
lean_dec(x_5);
x_488 = l_Lean_Expr_mdata___override(x_474, x_483);
x_489 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_489, 0, x_488);
lean_ctor_set(x_489, 1, x_484);
return x_489;
}
else
{
lean_object* x_490; 
lean_dec(x_483);
lean_dec(x_474);
x_490 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_490, 0, x_5);
lean_ctor_set(x_490, 1, x_484);
return x_490;
}
}
}
else
{
uint8_t x_491; 
lean_dec(x_475);
lean_dec(x_474);
lean_dec(x_5);
x_491 = !lean_is_exclusive(x_476);
if (x_491 == 0)
{
return x_476;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_ctor_get(x_476, 0);
x_493 = lean_ctor_get(x_476, 1);
lean_inc(x_493);
lean_inc(x_492);
lean_dec(x_476);
x_494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_493);
return x_494;
}
}
}
case 11:
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_495 = lean_ctor_get(x_275, 1);
lean_inc(x_495);
lean_dec(x_275);
x_496 = lean_ctor_get(x_5, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_5, 1);
lean_inc(x_497);
x_498 = lean_ctor_get(x_5, 2);
lean_inc(x_498);
x_499 = lean_ctor_get(x_5, 3);
lean_inc(x_499);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_498);
lean_inc(x_1);
x_500 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_498, x_6, x_7, x_8, x_9, x_10, x_11, x_495);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
lean_dec(x_500);
lean_inc(x_499);
x_503 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_499, x_6, x_7, x_8, x_9, x_10, x_11, x_502);
if (lean_obj_tag(x_503) == 0)
{
uint8_t x_504; 
x_504 = !lean_is_exclusive(x_503);
if (x_504 == 0)
{
lean_object* x_505; size_t x_506; size_t x_507; uint8_t x_508; 
x_505 = lean_ctor_get(x_503, 0);
x_506 = lean_ptr_addr(x_498);
lean_dec(x_498);
x_507 = lean_ptr_addr(x_501);
x_508 = lean_usize_dec_eq(x_506, x_507);
if (x_508 == 0)
{
lean_object* x_509; 
lean_dec(x_499);
lean_dec(x_5);
x_509 = l_Lean_Expr_proj___override(x_496, x_497, x_501, x_505);
lean_ctor_set(x_503, 0, x_509);
return x_503;
}
else
{
size_t x_510; size_t x_511; uint8_t x_512; 
x_510 = lean_ptr_addr(x_499);
lean_dec(x_499);
x_511 = lean_ptr_addr(x_505);
x_512 = lean_usize_dec_eq(x_510, x_511);
if (x_512 == 0)
{
lean_object* x_513; 
lean_dec(x_5);
x_513 = l_Lean_Expr_proj___override(x_496, x_497, x_501, x_505);
lean_ctor_set(x_503, 0, x_513);
return x_503;
}
else
{
lean_dec(x_505);
lean_dec(x_501);
lean_dec(x_497);
lean_dec(x_496);
lean_ctor_set(x_503, 0, x_5);
return x_503;
}
}
}
else
{
lean_object* x_514; lean_object* x_515; size_t x_516; size_t x_517; uint8_t x_518; 
x_514 = lean_ctor_get(x_503, 0);
x_515 = lean_ctor_get(x_503, 1);
lean_inc(x_515);
lean_inc(x_514);
lean_dec(x_503);
x_516 = lean_ptr_addr(x_498);
lean_dec(x_498);
x_517 = lean_ptr_addr(x_501);
x_518 = lean_usize_dec_eq(x_516, x_517);
if (x_518 == 0)
{
lean_object* x_519; lean_object* x_520; 
lean_dec(x_499);
lean_dec(x_5);
x_519 = l_Lean_Expr_proj___override(x_496, x_497, x_501, x_514);
x_520 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_520, 0, x_519);
lean_ctor_set(x_520, 1, x_515);
return x_520;
}
else
{
size_t x_521; size_t x_522; uint8_t x_523; 
x_521 = lean_ptr_addr(x_499);
lean_dec(x_499);
x_522 = lean_ptr_addr(x_514);
x_523 = lean_usize_dec_eq(x_521, x_522);
if (x_523 == 0)
{
lean_object* x_524; lean_object* x_525; 
lean_dec(x_5);
x_524 = l_Lean_Expr_proj___override(x_496, x_497, x_501, x_514);
x_525 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_525, 0, x_524);
lean_ctor_set(x_525, 1, x_515);
return x_525;
}
else
{
lean_object* x_526; 
lean_dec(x_514);
lean_dec(x_501);
lean_dec(x_497);
lean_dec(x_496);
x_526 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_526, 0, x_5);
lean_ctor_set(x_526, 1, x_515);
return x_526;
}
}
}
}
else
{
uint8_t x_527; 
lean_dec(x_501);
lean_dec(x_499);
lean_dec(x_498);
lean_dec(x_497);
lean_dec(x_496);
lean_dec(x_5);
x_527 = !lean_is_exclusive(x_503);
if (x_527 == 0)
{
return x_503;
}
else
{
lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_528 = lean_ctor_get(x_503, 0);
x_529 = lean_ctor_get(x_503, 1);
lean_inc(x_529);
lean_inc(x_528);
lean_dec(x_503);
x_530 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_530, 0, x_528);
lean_ctor_set(x_530, 1, x_529);
return x_530;
}
}
}
else
{
uint8_t x_531; 
lean_dec(x_499);
lean_dec(x_498);
lean_dec(x_497);
lean_dec(x_496);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_531 = !lean_is_exclusive(x_500);
if (x_531 == 0)
{
return x_500;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_532 = lean_ctor_get(x_500, 0);
x_533 = lean_ctor_get(x_500, 1);
lean_inc(x_533);
lean_inc(x_532);
lean_dec(x_500);
x_534 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_534, 0, x_532);
lean_ctor_set(x_534, 1, x_533);
return x_534;
}
}
}
default: 
{
uint8_t x_535; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_535 = !lean_is_exclusive(x_275);
if (x_535 == 0)
{
lean_object* x_536; 
x_536 = lean_ctor_get(x_275, 0);
lean_dec(x_536);
lean_ctor_set(x_275, 0, x_5);
return x_275;
}
else
{
lean_object* x_537; lean_object* x_538; 
x_537 = lean_ctor_get(x_275, 1);
lean_inc(x_537);
lean_dec(x_275);
x_538 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_538, 0, x_5);
lean_ctor_set(x_538, 1, x_537);
return x_538;
}
}
}
}
else
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; uint8_t x_546; 
x_539 = lean_ctor_get(x_275, 1);
lean_inc(x_539);
lean_dec(x_275);
x_540 = lean_st_ref_get(x_7, x_539);
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
x_542 = lean_ctor_get(x_540, 1);
lean_inc(x_542);
lean_dec(x_540);
x_543 = lean_unsigned_to_nat(1u);
x_544 = lean_nat_add(x_541, x_543);
x_545 = lean_st_ref_set(x_7, x_544, x_542);
x_546 = !lean_is_exclusive(x_545);
if (x_546 == 0)
{
lean_object* x_547; lean_object* x_548; uint8_t x_549; 
x_547 = lean_ctor_get(x_545, 1);
x_548 = lean_ctor_get(x_545, 0);
lean_dec(x_548);
x_549 = l_Lean_Meta_Occurrences_contains(x_2, x_541);
lean_dec(x_541);
if (x_549 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_free_object(x_545);
x_550 = lean_ctor_get(x_5, 0);
lean_inc(x_550);
x_551 = lean_ctor_get(x_5, 1);
lean_inc(x_551);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_550);
lean_inc(x_1);
x_552 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_550, x_6, x_7, x_8, x_9, x_10, x_11, x_547);
if (lean_obj_tag(x_552) == 0)
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_553 = lean_ctor_get(x_552, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_552, 1);
lean_inc(x_554);
lean_dec(x_552);
lean_inc(x_551);
x_555 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_551, x_6, x_7, x_8, x_9, x_10, x_11, x_554);
if (lean_obj_tag(x_555) == 0)
{
uint8_t x_556; 
x_556 = !lean_is_exclusive(x_555);
if (x_556 == 0)
{
lean_object* x_557; size_t x_558; size_t x_559; uint8_t x_560; 
x_557 = lean_ctor_get(x_555, 0);
x_558 = lean_ptr_addr(x_550);
lean_dec(x_550);
x_559 = lean_ptr_addr(x_553);
x_560 = lean_usize_dec_eq(x_558, x_559);
if (x_560 == 0)
{
lean_object* x_561; 
lean_dec(x_551);
lean_dec(x_5);
x_561 = l_Lean_Expr_app___override(x_553, x_557);
lean_ctor_set(x_555, 0, x_561);
return x_555;
}
else
{
size_t x_562; size_t x_563; uint8_t x_564; 
x_562 = lean_ptr_addr(x_551);
lean_dec(x_551);
x_563 = lean_ptr_addr(x_557);
x_564 = lean_usize_dec_eq(x_562, x_563);
if (x_564 == 0)
{
lean_object* x_565; 
lean_dec(x_5);
x_565 = l_Lean_Expr_app___override(x_553, x_557);
lean_ctor_set(x_555, 0, x_565);
return x_555;
}
else
{
lean_dec(x_557);
lean_dec(x_553);
lean_ctor_set(x_555, 0, x_5);
return x_555;
}
}
}
else
{
lean_object* x_566; lean_object* x_567; size_t x_568; size_t x_569; uint8_t x_570; 
x_566 = lean_ctor_get(x_555, 0);
x_567 = lean_ctor_get(x_555, 1);
lean_inc(x_567);
lean_inc(x_566);
lean_dec(x_555);
x_568 = lean_ptr_addr(x_550);
lean_dec(x_550);
x_569 = lean_ptr_addr(x_553);
x_570 = lean_usize_dec_eq(x_568, x_569);
if (x_570 == 0)
{
lean_object* x_571; lean_object* x_572; 
lean_dec(x_551);
lean_dec(x_5);
x_571 = l_Lean_Expr_app___override(x_553, x_566);
x_572 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_572, 0, x_571);
lean_ctor_set(x_572, 1, x_567);
return x_572;
}
else
{
size_t x_573; size_t x_574; uint8_t x_575; 
x_573 = lean_ptr_addr(x_551);
lean_dec(x_551);
x_574 = lean_ptr_addr(x_566);
x_575 = lean_usize_dec_eq(x_573, x_574);
if (x_575 == 0)
{
lean_object* x_576; lean_object* x_577; 
lean_dec(x_5);
x_576 = l_Lean_Expr_app___override(x_553, x_566);
x_577 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_577, 0, x_576);
lean_ctor_set(x_577, 1, x_567);
return x_577;
}
else
{
lean_object* x_578; 
lean_dec(x_566);
lean_dec(x_553);
x_578 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_578, 0, x_5);
lean_ctor_set(x_578, 1, x_567);
return x_578;
}
}
}
}
else
{
uint8_t x_579; 
lean_dec(x_553);
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_5);
x_579 = !lean_is_exclusive(x_555);
if (x_579 == 0)
{
return x_555;
}
else
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_580 = lean_ctor_get(x_555, 0);
x_581 = lean_ctor_get(x_555, 1);
lean_inc(x_581);
lean_inc(x_580);
lean_dec(x_555);
x_582 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_582, 0, x_580);
lean_ctor_set(x_582, 1, x_581);
return x_582;
}
}
}
else
{
uint8_t x_583; 
lean_dec(x_551);
lean_dec(x_550);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_583 = !lean_is_exclusive(x_552);
if (x_583 == 0)
{
return x_552;
}
else
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; 
x_584 = lean_ctor_get(x_552, 0);
x_585 = lean_ctor_get(x_552, 1);
lean_inc(x_585);
lean_inc(x_584);
lean_dec(x_552);
x_586 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_586, 0, x_584);
lean_ctor_set(x_586, 1, x_585);
return x_586;
}
}
}
case 6:
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; uint8_t x_590; lean_object* x_591; 
lean_free_object(x_545);
x_587 = lean_ctor_get(x_5, 0);
lean_inc(x_587);
x_588 = lean_ctor_get(x_5, 1);
lean_inc(x_588);
x_589 = lean_ctor_get(x_5, 2);
lean_inc(x_589);
x_590 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_588);
lean_inc(x_1);
x_591 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_588, x_6, x_7, x_8, x_9, x_10, x_11, x_547);
if (lean_obj_tag(x_591) == 0)
{
lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_592 = lean_ctor_get(x_591, 0);
lean_inc(x_592);
x_593 = lean_ctor_get(x_591, 1);
lean_inc(x_593);
lean_dec(x_591);
x_594 = lean_nat_add(x_6, x_543);
lean_dec(x_6);
lean_inc(x_589);
x_595 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_589, x_594, x_7, x_8, x_9, x_10, x_11, x_593);
if (lean_obj_tag(x_595) == 0)
{
uint8_t x_596; 
x_596 = !lean_is_exclusive(x_595);
if (x_596 == 0)
{
lean_object* x_597; lean_object* x_598; size_t x_599; size_t x_600; uint8_t x_601; 
x_597 = lean_ctor_get(x_595, 0);
lean_inc(x_589);
lean_inc(x_588);
lean_inc(x_587);
x_598 = l_Lean_Expr_lam___override(x_587, x_588, x_589, x_590);
x_599 = lean_ptr_addr(x_588);
lean_dec(x_588);
x_600 = lean_ptr_addr(x_592);
x_601 = lean_usize_dec_eq(x_599, x_600);
if (x_601 == 0)
{
lean_object* x_602; 
lean_dec(x_598);
lean_dec(x_589);
x_602 = l_Lean_Expr_lam___override(x_587, x_592, x_597, x_590);
lean_ctor_set(x_595, 0, x_602);
return x_595;
}
else
{
size_t x_603; size_t x_604; uint8_t x_605; 
x_603 = lean_ptr_addr(x_589);
lean_dec(x_589);
x_604 = lean_ptr_addr(x_597);
x_605 = lean_usize_dec_eq(x_603, x_604);
if (x_605 == 0)
{
lean_object* x_606; 
lean_dec(x_598);
x_606 = l_Lean_Expr_lam___override(x_587, x_592, x_597, x_590);
lean_ctor_set(x_595, 0, x_606);
return x_595;
}
else
{
uint8_t x_607; 
x_607 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_590, x_590);
if (x_607 == 0)
{
lean_object* x_608; 
lean_dec(x_598);
x_608 = l_Lean_Expr_lam___override(x_587, x_592, x_597, x_590);
lean_ctor_set(x_595, 0, x_608);
return x_595;
}
else
{
lean_dec(x_597);
lean_dec(x_592);
lean_dec(x_587);
lean_ctor_set(x_595, 0, x_598);
return x_595;
}
}
}
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; size_t x_612; size_t x_613; uint8_t x_614; 
x_609 = lean_ctor_get(x_595, 0);
x_610 = lean_ctor_get(x_595, 1);
lean_inc(x_610);
lean_inc(x_609);
lean_dec(x_595);
lean_inc(x_589);
lean_inc(x_588);
lean_inc(x_587);
x_611 = l_Lean_Expr_lam___override(x_587, x_588, x_589, x_590);
x_612 = lean_ptr_addr(x_588);
lean_dec(x_588);
x_613 = lean_ptr_addr(x_592);
x_614 = lean_usize_dec_eq(x_612, x_613);
if (x_614 == 0)
{
lean_object* x_615; lean_object* x_616; 
lean_dec(x_611);
lean_dec(x_589);
x_615 = l_Lean_Expr_lam___override(x_587, x_592, x_609, x_590);
x_616 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_616, 0, x_615);
lean_ctor_set(x_616, 1, x_610);
return x_616;
}
else
{
size_t x_617; size_t x_618; uint8_t x_619; 
x_617 = lean_ptr_addr(x_589);
lean_dec(x_589);
x_618 = lean_ptr_addr(x_609);
x_619 = lean_usize_dec_eq(x_617, x_618);
if (x_619 == 0)
{
lean_object* x_620; lean_object* x_621; 
lean_dec(x_611);
x_620 = l_Lean_Expr_lam___override(x_587, x_592, x_609, x_590);
x_621 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_621, 0, x_620);
lean_ctor_set(x_621, 1, x_610);
return x_621;
}
else
{
uint8_t x_622; 
x_622 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_590, x_590);
if (x_622 == 0)
{
lean_object* x_623; lean_object* x_624; 
lean_dec(x_611);
x_623 = l_Lean_Expr_lam___override(x_587, x_592, x_609, x_590);
x_624 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_624, 0, x_623);
lean_ctor_set(x_624, 1, x_610);
return x_624;
}
else
{
lean_object* x_625; 
lean_dec(x_609);
lean_dec(x_592);
lean_dec(x_587);
x_625 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_625, 0, x_611);
lean_ctor_set(x_625, 1, x_610);
return x_625;
}
}
}
}
}
else
{
uint8_t x_626; 
lean_dec(x_592);
lean_dec(x_589);
lean_dec(x_588);
lean_dec(x_587);
x_626 = !lean_is_exclusive(x_595);
if (x_626 == 0)
{
return x_595;
}
else
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; 
x_627 = lean_ctor_get(x_595, 0);
x_628 = lean_ctor_get(x_595, 1);
lean_inc(x_628);
lean_inc(x_627);
lean_dec(x_595);
x_629 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_629, 0, x_627);
lean_ctor_set(x_629, 1, x_628);
return x_629;
}
}
}
else
{
uint8_t x_630; 
lean_dec(x_589);
lean_dec(x_588);
lean_dec(x_587);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_630 = !lean_is_exclusive(x_591);
if (x_630 == 0)
{
return x_591;
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; 
x_631 = lean_ctor_get(x_591, 0);
x_632 = lean_ctor_get(x_591, 1);
lean_inc(x_632);
lean_inc(x_631);
lean_dec(x_591);
x_633 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_633, 0, x_631);
lean_ctor_set(x_633, 1, x_632);
return x_633;
}
}
}
case 7:
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; uint8_t x_637; lean_object* x_638; 
lean_free_object(x_545);
x_634 = lean_ctor_get(x_5, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_5, 1);
lean_inc(x_635);
x_636 = lean_ctor_get(x_5, 2);
lean_inc(x_636);
x_637 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_635);
lean_inc(x_1);
x_638 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_635, x_6, x_7, x_8, x_9, x_10, x_11, x_547);
if (lean_obj_tag(x_638) == 0)
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_639 = lean_ctor_get(x_638, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_638, 1);
lean_inc(x_640);
lean_dec(x_638);
x_641 = lean_nat_add(x_6, x_543);
lean_dec(x_6);
lean_inc(x_636);
x_642 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_636, x_641, x_7, x_8, x_9, x_10, x_11, x_640);
if (lean_obj_tag(x_642) == 0)
{
uint8_t x_643; 
x_643 = !lean_is_exclusive(x_642);
if (x_643 == 0)
{
lean_object* x_644; lean_object* x_645; size_t x_646; size_t x_647; uint8_t x_648; 
x_644 = lean_ctor_get(x_642, 0);
lean_inc(x_636);
lean_inc(x_635);
lean_inc(x_634);
x_645 = l_Lean_Expr_forallE___override(x_634, x_635, x_636, x_637);
x_646 = lean_ptr_addr(x_635);
lean_dec(x_635);
x_647 = lean_ptr_addr(x_639);
x_648 = lean_usize_dec_eq(x_646, x_647);
if (x_648 == 0)
{
lean_object* x_649; 
lean_dec(x_645);
lean_dec(x_636);
x_649 = l_Lean_Expr_forallE___override(x_634, x_639, x_644, x_637);
lean_ctor_set(x_642, 0, x_649);
return x_642;
}
else
{
size_t x_650; size_t x_651; uint8_t x_652; 
x_650 = lean_ptr_addr(x_636);
lean_dec(x_636);
x_651 = lean_ptr_addr(x_644);
x_652 = lean_usize_dec_eq(x_650, x_651);
if (x_652 == 0)
{
lean_object* x_653; 
lean_dec(x_645);
x_653 = l_Lean_Expr_forallE___override(x_634, x_639, x_644, x_637);
lean_ctor_set(x_642, 0, x_653);
return x_642;
}
else
{
uint8_t x_654; 
x_654 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_637, x_637);
if (x_654 == 0)
{
lean_object* x_655; 
lean_dec(x_645);
x_655 = l_Lean_Expr_forallE___override(x_634, x_639, x_644, x_637);
lean_ctor_set(x_642, 0, x_655);
return x_642;
}
else
{
lean_dec(x_644);
lean_dec(x_639);
lean_dec(x_634);
lean_ctor_set(x_642, 0, x_645);
return x_642;
}
}
}
}
else
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; size_t x_659; size_t x_660; uint8_t x_661; 
x_656 = lean_ctor_get(x_642, 0);
x_657 = lean_ctor_get(x_642, 1);
lean_inc(x_657);
lean_inc(x_656);
lean_dec(x_642);
lean_inc(x_636);
lean_inc(x_635);
lean_inc(x_634);
x_658 = l_Lean_Expr_forallE___override(x_634, x_635, x_636, x_637);
x_659 = lean_ptr_addr(x_635);
lean_dec(x_635);
x_660 = lean_ptr_addr(x_639);
x_661 = lean_usize_dec_eq(x_659, x_660);
if (x_661 == 0)
{
lean_object* x_662; lean_object* x_663; 
lean_dec(x_658);
lean_dec(x_636);
x_662 = l_Lean_Expr_forallE___override(x_634, x_639, x_656, x_637);
x_663 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_663, 0, x_662);
lean_ctor_set(x_663, 1, x_657);
return x_663;
}
else
{
size_t x_664; size_t x_665; uint8_t x_666; 
x_664 = lean_ptr_addr(x_636);
lean_dec(x_636);
x_665 = lean_ptr_addr(x_656);
x_666 = lean_usize_dec_eq(x_664, x_665);
if (x_666 == 0)
{
lean_object* x_667; lean_object* x_668; 
lean_dec(x_658);
x_667 = l_Lean_Expr_forallE___override(x_634, x_639, x_656, x_637);
x_668 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_668, 0, x_667);
lean_ctor_set(x_668, 1, x_657);
return x_668;
}
else
{
uint8_t x_669; 
x_669 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_637, x_637);
if (x_669 == 0)
{
lean_object* x_670; lean_object* x_671; 
lean_dec(x_658);
x_670 = l_Lean_Expr_forallE___override(x_634, x_639, x_656, x_637);
x_671 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_671, 0, x_670);
lean_ctor_set(x_671, 1, x_657);
return x_671;
}
else
{
lean_object* x_672; 
lean_dec(x_656);
lean_dec(x_639);
lean_dec(x_634);
x_672 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_672, 0, x_658);
lean_ctor_set(x_672, 1, x_657);
return x_672;
}
}
}
}
}
else
{
uint8_t x_673; 
lean_dec(x_639);
lean_dec(x_636);
lean_dec(x_635);
lean_dec(x_634);
x_673 = !lean_is_exclusive(x_642);
if (x_673 == 0)
{
return x_642;
}
else
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; 
x_674 = lean_ctor_get(x_642, 0);
x_675 = lean_ctor_get(x_642, 1);
lean_inc(x_675);
lean_inc(x_674);
lean_dec(x_642);
x_676 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_676, 0, x_674);
lean_ctor_set(x_676, 1, x_675);
return x_676;
}
}
}
else
{
uint8_t x_677; 
lean_dec(x_636);
lean_dec(x_635);
lean_dec(x_634);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_677 = !lean_is_exclusive(x_638);
if (x_677 == 0)
{
return x_638;
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_678 = lean_ctor_get(x_638, 0);
x_679 = lean_ctor_get(x_638, 1);
lean_inc(x_679);
lean_inc(x_678);
lean_dec(x_638);
x_680 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_680, 0, x_678);
lean_ctor_set(x_680, 1, x_679);
return x_680;
}
}
}
case 8:
{
lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; uint8_t x_685; lean_object* x_686; 
lean_free_object(x_545);
x_681 = lean_ctor_get(x_5, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_5, 1);
lean_inc(x_682);
x_683 = lean_ctor_get(x_5, 2);
lean_inc(x_683);
x_684 = lean_ctor_get(x_5, 3);
lean_inc(x_684);
x_685 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_682);
lean_inc(x_1);
x_686 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_682, x_6, x_7, x_8, x_9, x_10, x_11, x_547);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; 
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_686, 1);
lean_inc(x_688);
lean_dec(x_686);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_683);
lean_inc(x_1);
x_689 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_683, x_6, x_7, x_8, x_9, x_10, x_11, x_688);
if (lean_obj_tag(x_689) == 0)
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_690 = lean_ctor_get(x_689, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_689, 1);
lean_inc(x_691);
lean_dec(x_689);
x_692 = lean_nat_add(x_6, x_543);
lean_dec(x_6);
lean_inc(x_684);
x_693 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_684, x_692, x_7, x_8, x_9, x_10, x_11, x_691);
if (lean_obj_tag(x_693) == 0)
{
uint8_t x_694; 
x_694 = !lean_is_exclusive(x_693);
if (x_694 == 0)
{
lean_object* x_695; size_t x_696; size_t x_697; uint8_t x_698; 
x_695 = lean_ctor_get(x_693, 0);
x_696 = lean_ptr_addr(x_682);
lean_dec(x_682);
x_697 = lean_ptr_addr(x_687);
x_698 = lean_usize_dec_eq(x_696, x_697);
if (x_698 == 0)
{
lean_object* x_699; 
lean_dec(x_684);
lean_dec(x_683);
lean_dec(x_5);
x_699 = l_Lean_Expr_letE___override(x_681, x_687, x_690, x_695, x_685);
lean_ctor_set(x_693, 0, x_699);
return x_693;
}
else
{
size_t x_700; size_t x_701; uint8_t x_702; 
x_700 = lean_ptr_addr(x_683);
lean_dec(x_683);
x_701 = lean_ptr_addr(x_690);
x_702 = lean_usize_dec_eq(x_700, x_701);
if (x_702 == 0)
{
lean_object* x_703; 
lean_dec(x_684);
lean_dec(x_5);
x_703 = l_Lean_Expr_letE___override(x_681, x_687, x_690, x_695, x_685);
lean_ctor_set(x_693, 0, x_703);
return x_693;
}
else
{
size_t x_704; size_t x_705; uint8_t x_706; 
x_704 = lean_ptr_addr(x_684);
lean_dec(x_684);
x_705 = lean_ptr_addr(x_695);
x_706 = lean_usize_dec_eq(x_704, x_705);
if (x_706 == 0)
{
lean_object* x_707; 
lean_dec(x_5);
x_707 = l_Lean_Expr_letE___override(x_681, x_687, x_690, x_695, x_685);
lean_ctor_set(x_693, 0, x_707);
return x_693;
}
else
{
lean_dec(x_695);
lean_dec(x_690);
lean_dec(x_687);
lean_dec(x_681);
lean_ctor_set(x_693, 0, x_5);
return x_693;
}
}
}
}
else
{
lean_object* x_708; lean_object* x_709; size_t x_710; size_t x_711; uint8_t x_712; 
x_708 = lean_ctor_get(x_693, 0);
x_709 = lean_ctor_get(x_693, 1);
lean_inc(x_709);
lean_inc(x_708);
lean_dec(x_693);
x_710 = lean_ptr_addr(x_682);
lean_dec(x_682);
x_711 = lean_ptr_addr(x_687);
x_712 = lean_usize_dec_eq(x_710, x_711);
if (x_712 == 0)
{
lean_object* x_713; lean_object* x_714; 
lean_dec(x_684);
lean_dec(x_683);
lean_dec(x_5);
x_713 = l_Lean_Expr_letE___override(x_681, x_687, x_690, x_708, x_685);
x_714 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_714, 0, x_713);
lean_ctor_set(x_714, 1, x_709);
return x_714;
}
else
{
size_t x_715; size_t x_716; uint8_t x_717; 
x_715 = lean_ptr_addr(x_683);
lean_dec(x_683);
x_716 = lean_ptr_addr(x_690);
x_717 = lean_usize_dec_eq(x_715, x_716);
if (x_717 == 0)
{
lean_object* x_718; lean_object* x_719; 
lean_dec(x_684);
lean_dec(x_5);
x_718 = l_Lean_Expr_letE___override(x_681, x_687, x_690, x_708, x_685);
x_719 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_719, 0, x_718);
lean_ctor_set(x_719, 1, x_709);
return x_719;
}
else
{
size_t x_720; size_t x_721; uint8_t x_722; 
x_720 = lean_ptr_addr(x_684);
lean_dec(x_684);
x_721 = lean_ptr_addr(x_708);
x_722 = lean_usize_dec_eq(x_720, x_721);
if (x_722 == 0)
{
lean_object* x_723; lean_object* x_724; 
lean_dec(x_5);
x_723 = l_Lean_Expr_letE___override(x_681, x_687, x_690, x_708, x_685);
x_724 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_724, 0, x_723);
lean_ctor_set(x_724, 1, x_709);
return x_724;
}
else
{
lean_object* x_725; 
lean_dec(x_708);
lean_dec(x_690);
lean_dec(x_687);
lean_dec(x_681);
x_725 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_725, 0, x_5);
lean_ctor_set(x_725, 1, x_709);
return x_725;
}
}
}
}
}
else
{
uint8_t x_726; 
lean_dec(x_690);
lean_dec(x_687);
lean_dec(x_684);
lean_dec(x_683);
lean_dec(x_682);
lean_dec(x_681);
lean_dec(x_5);
x_726 = !lean_is_exclusive(x_693);
if (x_726 == 0)
{
return x_693;
}
else
{
lean_object* x_727; lean_object* x_728; lean_object* x_729; 
x_727 = lean_ctor_get(x_693, 0);
x_728 = lean_ctor_get(x_693, 1);
lean_inc(x_728);
lean_inc(x_727);
lean_dec(x_693);
x_729 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_729, 0, x_727);
lean_ctor_set(x_729, 1, x_728);
return x_729;
}
}
}
else
{
uint8_t x_730; 
lean_dec(x_687);
lean_dec(x_684);
lean_dec(x_683);
lean_dec(x_682);
lean_dec(x_681);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_730 = !lean_is_exclusive(x_689);
if (x_730 == 0)
{
return x_689;
}
else
{
lean_object* x_731; lean_object* x_732; lean_object* x_733; 
x_731 = lean_ctor_get(x_689, 0);
x_732 = lean_ctor_get(x_689, 1);
lean_inc(x_732);
lean_inc(x_731);
lean_dec(x_689);
x_733 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_733, 0, x_731);
lean_ctor_set(x_733, 1, x_732);
return x_733;
}
}
}
else
{
uint8_t x_734; 
lean_dec(x_684);
lean_dec(x_683);
lean_dec(x_682);
lean_dec(x_681);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_734 = !lean_is_exclusive(x_686);
if (x_734 == 0)
{
return x_686;
}
else
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; 
x_735 = lean_ctor_get(x_686, 0);
x_736 = lean_ctor_get(x_686, 1);
lean_inc(x_736);
lean_inc(x_735);
lean_dec(x_686);
x_737 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_737, 0, x_735);
lean_ctor_set(x_737, 1, x_736);
return x_737;
}
}
}
case 10:
{
lean_object* x_738; lean_object* x_739; lean_object* x_740; 
lean_free_object(x_545);
x_738 = lean_ctor_get(x_5, 0);
lean_inc(x_738);
x_739 = lean_ctor_get(x_5, 1);
lean_inc(x_739);
lean_inc(x_739);
x_740 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_739, x_6, x_7, x_8, x_9, x_10, x_11, x_547);
if (lean_obj_tag(x_740) == 0)
{
uint8_t x_741; 
x_741 = !lean_is_exclusive(x_740);
if (x_741 == 0)
{
lean_object* x_742; size_t x_743; size_t x_744; uint8_t x_745; 
x_742 = lean_ctor_get(x_740, 0);
x_743 = lean_ptr_addr(x_739);
lean_dec(x_739);
x_744 = lean_ptr_addr(x_742);
x_745 = lean_usize_dec_eq(x_743, x_744);
if (x_745 == 0)
{
lean_object* x_746; 
lean_dec(x_5);
x_746 = l_Lean_Expr_mdata___override(x_738, x_742);
lean_ctor_set(x_740, 0, x_746);
return x_740;
}
else
{
lean_dec(x_742);
lean_dec(x_738);
lean_ctor_set(x_740, 0, x_5);
return x_740;
}
}
else
{
lean_object* x_747; lean_object* x_748; size_t x_749; size_t x_750; uint8_t x_751; 
x_747 = lean_ctor_get(x_740, 0);
x_748 = lean_ctor_get(x_740, 1);
lean_inc(x_748);
lean_inc(x_747);
lean_dec(x_740);
x_749 = lean_ptr_addr(x_739);
lean_dec(x_739);
x_750 = lean_ptr_addr(x_747);
x_751 = lean_usize_dec_eq(x_749, x_750);
if (x_751 == 0)
{
lean_object* x_752; lean_object* x_753; 
lean_dec(x_5);
x_752 = l_Lean_Expr_mdata___override(x_738, x_747);
x_753 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_753, 0, x_752);
lean_ctor_set(x_753, 1, x_748);
return x_753;
}
else
{
lean_object* x_754; 
lean_dec(x_747);
lean_dec(x_738);
x_754 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_754, 0, x_5);
lean_ctor_set(x_754, 1, x_748);
return x_754;
}
}
}
else
{
uint8_t x_755; 
lean_dec(x_739);
lean_dec(x_738);
lean_dec(x_5);
x_755 = !lean_is_exclusive(x_740);
if (x_755 == 0)
{
return x_740;
}
else
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; 
x_756 = lean_ctor_get(x_740, 0);
x_757 = lean_ctor_get(x_740, 1);
lean_inc(x_757);
lean_inc(x_756);
lean_dec(x_740);
x_758 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_758, 0, x_756);
lean_ctor_set(x_758, 1, x_757);
return x_758;
}
}
}
case 11:
{
lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; lean_object* x_763; 
lean_free_object(x_545);
x_759 = lean_ctor_get(x_5, 0);
lean_inc(x_759);
x_760 = lean_ctor_get(x_5, 1);
lean_inc(x_760);
x_761 = lean_ctor_get(x_5, 2);
lean_inc(x_761);
x_762 = lean_ctor_get(x_5, 3);
lean_inc(x_762);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_761);
lean_inc(x_1);
x_763 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_761, x_6, x_7, x_8, x_9, x_10, x_11, x_547);
if (lean_obj_tag(x_763) == 0)
{
lean_object* x_764; lean_object* x_765; lean_object* x_766; 
x_764 = lean_ctor_get(x_763, 0);
lean_inc(x_764);
x_765 = lean_ctor_get(x_763, 1);
lean_inc(x_765);
lean_dec(x_763);
lean_inc(x_762);
x_766 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_762, x_6, x_7, x_8, x_9, x_10, x_11, x_765);
if (lean_obj_tag(x_766) == 0)
{
uint8_t x_767; 
x_767 = !lean_is_exclusive(x_766);
if (x_767 == 0)
{
lean_object* x_768; size_t x_769; size_t x_770; uint8_t x_771; 
x_768 = lean_ctor_get(x_766, 0);
x_769 = lean_ptr_addr(x_761);
lean_dec(x_761);
x_770 = lean_ptr_addr(x_764);
x_771 = lean_usize_dec_eq(x_769, x_770);
if (x_771 == 0)
{
lean_object* x_772; 
lean_dec(x_762);
lean_dec(x_5);
x_772 = l_Lean_Expr_proj___override(x_759, x_760, x_764, x_768);
lean_ctor_set(x_766, 0, x_772);
return x_766;
}
else
{
size_t x_773; size_t x_774; uint8_t x_775; 
x_773 = lean_ptr_addr(x_762);
lean_dec(x_762);
x_774 = lean_ptr_addr(x_768);
x_775 = lean_usize_dec_eq(x_773, x_774);
if (x_775 == 0)
{
lean_object* x_776; 
lean_dec(x_5);
x_776 = l_Lean_Expr_proj___override(x_759, x_760, x_764, x_768);
lean_ctor_set(x_766, 0, x_776);
return x_766;
}
else
{
lean_dec(x_768);
lean_dec(x_764);
lean_dec(x_760);
lean_dec(x_759);
lean_ctor_set(x_766, 0, x_5);
return x_766;
}
}
}
else
{
lean_object* x_777; lean_object* x_778; size_t x_779; size_t x_780; uint8_t x_781; 
x_777 = lean_ctor_get(x_766, 0);
x_778 = lean_ctor_get(x_766, 1);
lean_inc(x_778);
lean_inc(x_777);
lean_dec(x_766);
x_779 = lean_ptr_addr(x_761);
lean_dec(x_761);
x_780 = lean_ptr_addr(x_764);
x_781 = lean_usize_dec_eq(x_779, x_780);
if (x_781 == 0)
{
lean_object* x_782; lean_object* x_783; 
lean_dec(x_762);
lean_dec(x_5);
x_782 = l_Lean_Expr_proj___override(x_759, x_760, x_764, x_777);
x_783 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_783, 0, x_782);
lean_ctor_set(x_783, 1, x_778);
return x_783;
}
else
{
size_t x_784; size_t x_785; uint8_t x_786; 
x_784 = lean_ptr_addr(x_762);
lean_dec(x_762);
x_785 = lean_ptr_addr(x_777);
x_786 = lean_usize_dec_eq(x_784, x_785);
if (x_786 == 0)
{
lean_object* x_787; lean_object* x_788; 
lean_dec(x_5);
x_787 = l_Lean_Expr_proj___override(x_759, x_760, x_764, x_777);
x_788 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_788, 0, x_787);
lean_ctor_set(x_788, 1, x_778);
return x_788;
}
else
{
lean_object* x_789; 
lean_dec(x_777);
lean_dec(x_764);
lean_dec(x_760);
lean_dec(x_759);
x_789 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_789, 0, x_5);
lean_ctor_set(x_789, 1, x_778);
return x_789;
}
}
}
}
else
{
uint8_t x_790; 
lean_dec(x_764);
lean_dec(x_762);
lean_dec(x_761);
lean_dec(x_760);
lean_dec(x_759);
lean_dec(x_5);
x_790 = !lean_is_exclusive(x_766);
if (x_790 == 0)
{
return x_766;
}
else
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; 
x_791 = lean_ctor_get(x_766, 0);
x_792 = lean_ctor_get(x_766, 1);
lean_inc(x_792);
lean_inc(x_791);
lean_dec(x_766);
x_793 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_793, 0, x_791);
lean_ctor_set(x_793, 1, x_792);
return x_793;
}
}
}
else
{
uint8_t x_794; 
lean_dec(x_762);
lean_dec(x_761);
lean_dec(x_760);
lean_dec(x_759);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_794 = !lean_is_exclusive(x_763);
if (x_794 == 0)
{
return x_763;
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; 
x_795 = lean_ctor_get(x_763, 0);
x_796 = lean_ctor_get(x_763, 1);
lean_inc(x_796);
lean_inc(x_795);
lean_dec(x_763);
x_797 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_797, 0, x_795);
lean_ctor_set(x_797, 1, x_796);
return x_797;
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
lean_ctor_set(x_545, 0, x_5);
return x_545;
}
}
}
else
{
lean_object* x_798; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_798 = l_Lean_Expr_bvar___override(x_6);
lean_ctor_set(x_545, 0, x_798);
return x_545;
}
}
else
{
lean_object* x_799; uint8_t x_800; 
x_799 = lean_ctor_get(x_545, 1);
lean_inc(x_799);
lean_dec(x_545);
x_800 = l_Lean_Meta_Occurrences_contains(x_2, x_541);
lean_dec(x_541);
if (x_800 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_801; lean_object* x_802; lean_object* x_803; 
x_801 = lean_ctor_get(x_5, 0);
lean_inc(x_801);
x_802 = lean_ctor_get(x_5, 1);
lean_inc(x_802);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_801);
lean_inc(x_1);
x_803 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_801, x_6, x_7, x_8, x_9, x_10, x_11, x_799);
if (lean_obj_tag(x_803) == 0)
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; 
x_804 = lean_ctor_get(x_803, 0);
lean_inc(x_804);
x_805 = lean_ctor_get(x_803, 1);
lean_inc(x_805);
lean_dec(x_803);
lean_inc(x_802);
x_806 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_802, x_6, x_7, x_8, x_9, x_10, x_11, x_805);
if (lean_obj_tag(x_806) == 0)
{
lean_object* x_807; lean_object* x_808; lean_object* x_809; size_t x_810; size_t x_811; uint8_t x_812; 
x_807 = lean_ctor_get(x_806, 0);
lean_inc(x_807);
x_808 = lean_ctor_get(x_806, 1);
lean_inc(x_808);
if (lean_is_exclusive(x_806)) {
 lean_ctor_release(x_806, 0);
 lean_ctor_release(x_806, 1);
 x_809 = x_806;
} else {
 lean_dec_ref(x_806);
 x_809 = lean_box(0);
}
x_810 = lean_ptr_addr(x_801);
lean_dec(x_801);
x_811 = lean_ptr_addr(x_804);
x_812 = lean_usize_dec_eq(x_810, x_811);
if (x_812 == 0)
{
lean_object* x_813; lean_object* x_814; 
lean_dec(x_802);
lean_dec(x_5);
x_813 = l_Lean_Expr_app___override(x_804, x_807);
if (lean_is_scalar(x_809)) {
 x_814 = lean_alloc_ctor(0, 2, 0);
} else {
 x_814 = x_809;
}
lean_ctor_set(x_814, 0, x_813);
lean_ctor_set(x_814, 1, x_808);
return x_814;
}
else
{
size_t x_815; size_t x_816; uint8_t x_817; 
x_815 = lean_ptr_addr(x_802);
lean_dec(x_802);
x_816 = lean_ptr_addr(x_807);
x_817 = lean_usize_dec_eq(x_815, x_816);
if (x_817 == 0)
{
lean_object* x_818; lean_object* x_819; 
lean_dec(x_5);
x_818 = l_Lean_Expr_app___override(x_804, x_807);
if (lean_is_scalar(x_809)) {
 x_819 = lean_alloc_ctor(0, 2, 0);
} else {
 x_819 = x_809;
}
lean_ctor_set(x_819, 0, x_818);
lean_ctor_set(x_819, 1, x_808);
return x_819;
}
else
{
lean_object* x_820; 
lean_dec(x_807);
lean_dec(x_804);
if (lean_is_scalar(x_809)) {
 x_820 = lean_alloc_ctor(0, 2, 0);
} else {
 x_820 = x_809;
}
lean_ctor_set(x_820, 0, x_5);
lean_ctor_set(x_820, 1, x_808);
return x_820;
}
}
}
else
{
lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; 
lean_dec(x_804);
lean_dec(x_802);
lean_dec(x_801);
lean_dec(x_5);
x_821 = lean_ctor_get(x_806, 0);
lean_inc(x_821);
x_822 = lean_ctor_get(x_806, 1);
lean_inc(x_822);
if (lean_is_exclusive(x_806)) {
 lean_ctor_release(x_806, 0);
 lean_ctor_release(x_806, 1);
 x_823 = x_806;
} else {
 lean_dec_ref(x_806);
 x_823 = lean_box(0);
}
if (lean_is_scalar(x_823)) {
 x_824 = lean_alloc_ctor(1, 2, 0);
} else {
 x_824 = x_823;
}
lean_ctor_set(x_824, 0, x_821);
lean_ctor_set(x_824, 1, x_822);
return x_824;
}
}
else
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; 
lean_dec(x_802);
lean_dec(x_801);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_825 = lean_ctor_get(x_803, 0);
lean_inc(x_825);
x_826 = lean_ctor_get(x_803, 1);
lean_inc(x_826);
if (lean_is_exclusive(x_803)) {
 lean_ctor_release(x_803, 0);
 lean_ctor_release(x_803, 1);
 x_827 = x_803;
} else {
 lean_dec_ref(x_803);
 x_827 = lean_box(0);
}
if (lean_is_scalar(x_827)) {
 x_828 = lean_alloc_ctor(1, 2, 0);
} else {
 x_828 = x_827;
}
lean_ctor_set(x_828, 0, x_825);
lean_ctor_set(x_828, 1, x_826);
return x_828;
}
}
case 6:
{
lean_object* x_829; lean_object* x_830; lean_object* x_831; uint8_t x_832; lean_object* x_833; 
x_829 = lean_ctor_get(x_5, 0);
lean_inc(x_829);
x_830 = lean_ctor_get(x_5, 1);
lean_inc(x_830);
x_831 = lean_ctor_get(x_5, 2);
lean_inc(x_831);
x_832 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_830);
lean_inc(x_1);
x_833 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_830, x_6, x_7, x_8, x_9, x_10, x_11, x_799);
if (lean_obj_tag(x_833) == 0)
{
lean_object* x_834; lean_object* x_835; lean_object* x_836; lean_object* x_837; 
x_834 = lean_ctor_get(x_833, 0);
lean_inc(x_834);
x_835 = lean_ctor_get(x_833, 1);
lean_inc(x_835);
lean_dec(x_833);
x_836 = lean_nat_add(x_6, x_543);
lean_dec(x_6);
lean_inc(x_831);
x_837 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_831, x_836, x_7, x_8, x_9, x_10, x_11, x_835);
if (lean_obj_tag(x_837) == 0)
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; size_t x_842; size_t x_843; uint8_t x_844; 
x_838 = lean_ctor_get(x_837, 0);
lean_inc(x_838);
x_839 = lean_ctor_get(x_837, 1);
lean_inc(x_839);
if (lean_is_exclusive(x_837)) {
 lean_ctor_release(x_837, 0);
 lean_ctor_release(x_837, 1);
 x_840 = x_837;
} else {
 lean_dec_ref(x_837);
 x_840 = lean_box(0);
}
lean_inc(x_831);
lean_inc(x_830);
lean_inc(x_829);
x_841 = l_Lean_Expr_lam___override(x_829, x_830, x_831, x_832);
x_842 = lean_ptr_addr(x_830);
lean_dec(x_830);
x_843 = lean_ptr_addr(x_834);
x_844 = lean_usize_dec_eq(x_842, x_843);
if (x_844 == 0)
{
lean_object* x_845; lean_object* x_846; 
lean_dec(x_841);
lean_dec(x_831);
x_845 = l_Lean_Expr_lam___override(x_829, x_834, x_838, x_832);
if (lean_is_scalar(x_840)) {
 x_846 = lean_alloc_ctor(0, 2, 0);
} else {
 x_846 = x_840;
}
lean_ctor_set(x_846, 0, x_845);
lean_ctor_set(x_846, 1, x_839);
return x_846;
}
else
{
size_t x_847; size_t x_848; uint8_t x_849; 
x_847 = lean_ptr_addr(x_831);
lean_dec(x_831);
x_848 = lean_ptr_addr(x_838);
x_849 = lean_usize_dec_eq(x_847, x_848);
if (x_849 == 0)
{
lean_object* x_850; lean_object* x_851; 
lean_dec(x_841);
x_850 = l_Lean_Expr_lam___override(x_829, x_834, x_838, x_832);
if (lean_is_scalar(x_840)) {
 x_851 = lean_alloc_ctor(0, 2, 0);
} else {
 x_851 = x_840;
}
lean_ctor_set(x_851, 0, x_850);
lean_ctor_set(x_851, 1, x_839);
return x_851;
}
else
{
uint8_t x_852; 
x_852 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_832, x_832);
if (x_852 == 0)
{
lean_object* x_853; lean_object* x_854; 
lean_dec(x_841);
x_853 = l_Lean_Expr_lam___override(x_829, x_834, x_838, x_832);
if (lean_is_scalar(x_840)) {
 x_854 = lean_alloc_ctor(0, 2, 0);
} else {
 x_854 = x_840;
}
lean_ctor_set(x_854, 0, x_853);
lean_ctor_set(x_854, 1, x_839);
return x_854;
}
else
{
lean_object* x_855; 
lean_dec(x_838);
lean_dec(x_834);
lean_dec(x_829);
if (lean_is_scalar(x_840)) {
 x_855 = lean_alloc_ctor(0, 2, 0);
} else {
 x_855 = x_840;
}
lean_ctor_set(x_855, 0, x_841);
lean_ctor_set(x_855, 1, x_839);
return x_855;
}
}
}
}
else
{
lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; 
lean_dec(x_834);
lean_dec(x_831);
lean_dec(x_830);
lean_dec(x_829);
x_856 = lean_ctor_get(x_837, 0);
lean_inc(x_856);
x_857 = lean_ctor_get(x_837, 1);
lean_inc(x_857);
if (lean_is_exclusive(x_837)) {
 lean_ctor_release(x_837, 0);
 lean_ctor_release(x_837, 1);
 x_858 = x_837;
} else {
 lean_dec_ref(x_837);
 x_858 = lean_box(0);
}
if (lean_is_scalar(x_858)) {
 x_859 = lean_alloc_ctor(1, 2, 0);
} else {
 x_859 = x_858;
}
lean_ctor_set(x_859, 0, x_856);
lean_ctor_set(x_859, 1, x_857);
return x_859;
}
}
else
{
lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; 
lean_dec(x_831);
lean_dec(x_830);
lean_dec(x_829);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_860 = lean_ctor_get(x_833, 0);
lean_inc(x_860);
x_861 = lean_ctor_get(x_833, 1);
lean_inc(x_861);
if (lean_is_exclusive(x_833)) {
 lean_ctor_release(x_833, 0);
 lean_ctor_release(x_833, 1);
 x_862 = x_833;
} else {
 lean_dec_ref(x_833);
 x_862 = lean_box(0);
}
if (lean_is_scalar(x_862)) {
 x_863 = lean_alloc_ctor(1, 2, 0);
} else {
 x_863 = x_862;
}
lean_ctor_set(x_863, 0, x_860);
lean_ctor_set(x_863, 1, x_861);
return x_863;
}
}
case 7:
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; uint8_t x_867; lean_object* x_868; 
x_864 = lean_ctor_get(x_5, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_5, 1);
lean_inc(x_865);
x_866 = lean_ctor_get(x_5, 2);
lean_inc(x_866);
x_867 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_865);
lean_inc(x_1);
x_868 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_865, x_6, x_7, x_8, x_9, x_10, x_11, x_799);
if (lean_obj_tag(x_868) == 0)
{
lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; 
x_869 = lean_ctor_get(x_868, 0);
lean_inc(x_869);
x_870 = lean_ctor_get(x_868, 1);
lean_inc(x_870);
lean_dec(x_868);
x_871 = lean_nat_add(x_6, x_543);
lean_dec(x_6);
lean_inc(x_866);
x_872 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_866, x_871, x_7, x_8, x_9, x_10, x_11, x_870);
if (lean_obj_tag(x_872) == 0)
{
lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; size_t x_877; size_t x_878; uint8_t x_879; 
x_873 = lean_ctor_get(x_872, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_872, 1);
lean_inc(x_874);
if (lean_is_exclusive(x_872)) {
 lean_ctor_release(x_872, 0);
 lean_ctor_release(x_872, 1);
 x_875 = x_872;
} else {
 lean_dec_ref(x_872);
 x_875 = lean_box(0);
}
lean_inc(x_866);
lean_inc(x_865);
lean_inc(x_864);
x_876 = l_Lean_Expr_forallE___override(x_864, x_865, x_866, x_867);
x_877 = lean_ptr_addr(x_865);
lean_dec(x_865);
x_878 = lean_ptr_addr(x_869);
x_879 = lean_usize_dec_eq(x_877, x_878);
if (x_879 == 0)
{
lean_object* x_880; lean_object* x_881; 
lean_dec(x_876);
lean_dec(x_866);
x_880 = l_Lean_Expr_forallE___override(x_864, x_869, x_873, x_867);
if (lean_is_scalar(x_875)) {
 x_881 = lean_alloc_ctor(0, 2, 0);
} else {
 x_881 = x_875;
}
lean_ctor_set(x_881, 0, x_880);
lean_ctor_set(x_881, 1, x_874);
return x_881;
}
else
{
size_t x_882; size_t x_883; uint8_t x_884; 
x_882 = lean_ptr_addr(x_866);
lean_dec(x_866);
x_883 = lean_ptr_addr(x_873);
x_884 = lean_usize_dec_eq(x_882, x_883);
if (x_884 == 0)
{
lean_object* x_885; lean_object* x_886; 
lean_dec(x_876);
x_885 = l_Lean_Expr_forallE___override(x_864, x_869, x_873, x_867);
if (lean_is_scalar(x_875)) {
 x_886 = lean_alloc_ctor(0, 2, 0);
} else {
 x_886 = x_875;
}
lean_ctor_set(x_886, 0, x_885);
lean_ctor_set(x_886, 1, x_874);
return x_886;
}
else
{
uint8_t x_887; 
x_887 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_867, x_867);
if (x_887 == 0)
{
lean_object* x_888; lean_object* x_889; 
lean_dec(x_876);
x_888 = l_Lean_Expr_forallE___override(x_864, x_869, x_873, x_867);
if (lean_is_scalar(x_875)) {
 x_889 = lean_alloc_ctor(0, 2, 0);
} else {
 x_889 = x_875;
}
lean_ctor_set(x_889, 0, x_888);
lean_ctor_set(x_889, 1, x_874);
return x_889;
}
else
{
lean_object* x_890; 
lean_dec(x_873);
lean_dec(x_869);
lean_dec(x_864);
if (lean_is_scalar(x_875)) {
 x_890 = lean_alloc_ctor(0, 2, 0);
} else {
 x_890 = x_875;
}
lean_ctor_set(x_890, 0, x_876);
lean_ctor_set(x_890, 1, x_874);
return x_890;
}
}
}
}
else
{
lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
lean_dec(x_869);
lean_dec(x_866);
lean_dec(x_865);
lean_dec(x_864);
x_891 = lean_ctor_get(x_872, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_872, 1);
lean_inc(x_892);
if (lean_is_exclusive(x_872)) {
 lean_ctor_release(x_872, 0);
 lean_ctor_release(x_872, 1);
 x_893 = x_872;
} else {
 lean_dec_ref(x_872);
 x_893 = lean_box(0);
}
if (lean_is_scalar(x_893)) {
 x_894 = lean_alloc_ctor(1, 2, 0);
} else {
 x_894 = x_893;
}
lean_ctor_set(x_894, 0, x_891);
lean_ctor_set(x_894, 1, x_892);
return x_894;
}
}
else
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; 
lean_dec(x_866);
lean_dec(x_865);
lean_dec(x_864);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_895 = lean_ctor_get(x_868, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_868, 1);
lean_inc(x_896);
if (lean_is_exclusive(x_868)) {
 lean_ctor_release(x_868, 0);
 lean_ctor_release(x_868, 1);
 x_897 = x_868;
} else {
 lean_dec_ref(x_868);
 x_897 = lean_box(0);
}
if (lean_is_scalar(x_897)) {
 x_898 = lean_alloc_ctor(1, 2, 0);
} else {
 x_898 = x_897;
}
lean_ctor_set(x_898, 0, x_895);
lean_ctor_set(x_898, 1, x_896);
return x_898;
}
}
case 8:
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; uint8_t x_903; lean_object* x_904; 
x_899 = lean_ctor_get(x_5, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_5, 1);
lean_inc(x_900);
x_901 = lean_ctor_get(x_5, 2);
lean_inc(x_901);
x_902 = lean_ctor_get(x_5, 3);
lean_inc(x_902);
x_903 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_900);
lean_inc(x_1);
x_904 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_900, x_6, x_7, x_8, x_9, x_10, x_11, x_799);
if (lean_obj_tag(x_904) == 0)
{
lean_object* x_905; lean_object* x_906; lean_object* x_907; 
x_905 = lean_ctor_get(x_904, 0);
lean_inc(x_905);
x_906 = lean_ctor_get(x_904, 1);
lean_inc(x_906);
lean_dec(x_904);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_901);
lean_inc(x_1);
x_907 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_901, x_6, x_7, x_8, x_9, x_10, x_11, x_906);
if (lean_obj_tag(x_907) == 0)
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; 
x_908 = lean_ctor_get(x_907, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_907, 1);
lean_inc(x_909);
lean_dec(x_907);
x_910 = lean_nat_add(x_6, x_543);
lean_dec(x_6);
lean_inc(x_902);
x_911 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_902, x_910, x_7, x_8, x_9, x_10, x_11, x_909);
if (lean_obj_tag(x_911) == 0)
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; size_t x_915; size_t x_916; uint8_t x_917; 
x_912 = lean_ctor_get(x_911, 0);
lean_inc(x_912);
x_913 = lean_ctor_get(x_911, 1);
lean_inc(x_913);
if (lean_is_exclusive(x_911)) {
 lean_ctor_release(x_911, 0);
 lean_ctor_release(x_911, 1);
 x_914 = x_911;
} else {
 lean_dec_ref(x_911);
 x_914 = lean_box(0);
}
x_915 = lean_ptr_addr(x_900);
lean_dec(x_900);
x_916 = lean_ptr_addr(x_905);
x_917 = lean_usize_dec_eq(x_915, x_916);
if (x_917 == 0)
{
lean_object* x_918; lean_object* x_919; 
lean_dec(x_902);
lean_dec(x_901);
lean_dec(x_5);
x_918 = l_Lean_Expr_letE___override(x_899, x_905, x_908, x_912, x_903);
if (lean_is_scalar(x_914)) {
 x_919 = lean_alloc_ctor(0, 2, 0);
} else {
 x_919 = x_914;
}
lean_ctor_set(x_919, 0, x_918);
lean_ctor_set(x_919, 1, x_913);
return x_919;
}
else
{
size_t x_920; size_t x_921; uint8_t x_922; 
x_920 = lean_ptr_addr(x_901);
lean_dec(x_901);
x_921 = lean_ptr_addr(x_908);
x_922 = lean_usize_dec_eq(x_920, x_921);
if (x_922 == 0)
{
lean_object* x_923; lean_object* x_924; 
lean_dec(x_902);
lean_dec(x_5);
x_923 = l_Lean_Expr_letE___override(x_899, x_905, x_908, x_912, x_903);
if (lean_is_scalar(x_914)) {
 x_924 = lean_alloc_ctor(0, 2, 0);
} else {
 x_924 = x_914;
}
lean_ctor_set(x_924, 0, x_923);
lean_ctor_set(x_924, 1, x_913);
return x_924;
}
else
{
size_t x_925; size_t x_926; uint8_t x_927; 
x_925 = lean_ptr_addr(x_902);
lean_dec(x_902);
x_926 = lean_ptr_addr(x_912);
x_927 = lean_usize_dec_eq(x_925, x_926);
if (x_927 == 0)
{
lean_object* x_928; lean_object* x_929; 
lean_dec(x_5);
x_928 = l_Lean_Expr_letE___override(x_899, x_905, x_908, x_912, x_903);
if (lean_is_scalar(x_914)) {
 x_929 = lean_alloc_ctor(0, 2, 0);
} else {
 x_929 = x_914;
}
lean_ctor_set(x_929, 0, x_928);
lean_ctor_set(x_929, 1, x_913);
return x_929;
}
else
{
lean_object* x_930; 
lean_dec(x_912);
lean_dec(x_908);
lean_dec(x_905);
lean_dec(x_899);
if (lean_is_scalar(x_914)) {
 x_930 = lean_alloc_ctor(0, 2, 0);
} else {
 x_930 = x_914;
}
lean_ctor_set(x_930, 0, x_5);
lean_ctor_set(x_930, 1, x_913);
return x_930;
}
}
}
}
else
{
lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
lean_dec(x_908);
lean_dec(x_905);
lean_dec(x_902);
lean_dec(x_901);
lean_dec(x_900);
lean_dec(x_899);
lean_dec(x_5);
x_931 = lean_ctor_get(x_911, 0);
lean_inc(x_931);
x_932 = lean_ctor_get(x_911, 1);
lean_inc(x_932);
if (lean_is_exclusive(x_911)) {
 lean_ctor_release(x_911, 0);
 lean_ctor_release(x_911, 1);
 x_933 = x_911;
} else {
 lean_dec_ref(x_911);
 x_933 = lean_box(0);
}
if (lean_is_scalar(x_933)) {
 x_934 = lean_alloc_ctor(1, 2, 0);
} else {
 x_934 = x_933;
}
lean_ctor_set(x_934, 0, x_931);
lean_ctor_set(x_934, 1, x_932);
return x_934;
}
}
else
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
lean_dec(x_905);
lean_dec(x_902);
lean_dec(x_901);
lean_dec(x_900);
lean_dec(x_899);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_935 = lean_ctor_get(x_907, 0);
lean_inc(x_935);
x_936 = lean_ctor_get(x_907, 1);
lean_inc(x_936);
if (lean_is_exclusive(x_907)) {
 lean_ctor_release(x_907, 0);
 lean_ctor_release(x_907, 1);
 x_937 = x_907;
} else {
 lean_dec_ref(x_907);
 x_937 = lean_box(0);
}
if (lean_is_scalar(x_937)) {
 x_938 = lean_alloc_ctor(1, 2, 0);
} else {
 x_938 = x_937;
}
lean_ctor_set(x_938, 0, x_935);
lean_ctor_set(x_938, 1, x_936);
return x_938;
}
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; 
lean_dec(x_902);
lean_dec(x_901);
lean_dec(x_900);
lean_dec(x_899);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_939 = lean_ctor_get(x_904, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_904, 1);
lean_inc(x_940);
if (lean_is_exclusive(x_904)) {
 lean_ctor_release(x_904, 0);
 lean_ctor_release(x_904, 1);
 x_941 = x_904;
} else {
 lean_dec_ref(x_904);
 x_941 = lean_box(0);
}
if (lean_is_scalar(x_941)) {
 x_942 = lean_alloc_ctor(1, 2, 0);
} else {
 x_942 = x_941;
}
lean_ctor_set(x_942, 0, x_939);
lean_ctor_set(x_942, 1, x_940);
return x_942;
}
}
case 10:
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; 
x_943 = lean_ctor_get(x_5, 0);
lean_inc(x_943);
x_944 = lean_ctor_get(x_5, 1);
lean_inc(x_944);
lean_inc(x_944);
x_945 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_944, x_6, x_7, x_8, x_9, x_10, x_11, x_799);
if (lean_obj_tag(x_945) == 0)
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; size_t x_949; size_t x_950; uint8_t x_951; 
x_946 = lean_ctor_get(x_945, 0);
lean_inc(x_946);
x_947 = lean_ctor_get(x_945, 1);
lean_inc(x_947);
if (lean_is_exclusive(x_945)) {
 lean_ctor_release(x_945, 0);
 lean_ctor_release(x_945, 1);
 x_948 = x_945;
} else {
 lean_dec_ref(x_945);
 x_948 = lean_box(0);
}
x_949 = lean_ptr_addr(x_944);
lean_dec(x_944);
x_950 = lean_ptr_addr(x_946);
x_951 = lean_usize_dec_eq(x_949, x_950);
if (x_951 == 0)
{
lean_object* x_952; lean_object* x_953; 
lean_dec(x_5);
x_952 = l_Lean_Expr_mdata___override(x_943, x_946);
if (lean_is_scalar(x_948)) {
 x_953 = lean_alloc_ctor(0, 2, 0);
} else {
 x_953 = x_948;
}
lean_ctor_set(x_953, 0, x_952);
lean_ctor_set(x_953, 1, x_947);
return x_953;
}
else
{
lean_object* x_954; 
lean_dec(x_946);
lean_dec(x_943);
if (lean_is_scalar(x_948)) {
 x_954 = lean_alloc_ctor(0, 2, 0);
} else {
 x_954 = x_948;
}
lean_ctor_set(x_954, 0, x_5);
lean_ctor_set(x_954, 1, x_947);
return x_954;
}
}
else
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; 
lean_dec(x_944);
lean_dec(x_943);
lean_dec(x_5);
x_955 = lean_ctor_get(x_945, 0);
lean_inc(x_955);
x_956 = lean_ctor_get(x_945, 1);
lean_inc(x_956);
if (lean_is_exclusive(x_945)) {
 lean_ctor_release(x_945, 0);
 lean_ctor_release(x_945, 1);
 x_957 = x_945;
} else {
 lean_dec_ref(x_945);
 x_957 = lean_box(0);
}
if (lean_is_scalar(x_957)) {
 x_958 = lean_alloc_ctor(1, 2, 0);
} else {
 x_958 = x_957;
}
lean_ctor_set(x_958, 0, x_955);
lean_ctor_set(x_958, 1, x_956);
return x_958;
}
}
case 11:
{
lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; lean_object* x_963; 
x_959 = lean_ctor_get(x_5, 0);
lean_inc(x_959);
x_960 = lean_ctor_get(x_5, 1);
lean_inc(x_960);
x_961 = lean_ctor_get(x_5, 2);
lean_inc(x_961);
x_962 = lean_ctor_get(x_5, 3);
lean_inc(x_962);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_961);
lean_inc(x_1);
x_963 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_961, x_6, x_7, x_8, x_9, x_10, x_11, x_799);
if (lean_obj_tag(x_963) == 0)
{
lean_object* x_964; lean_object* x_965; lean_object* x_966; 
x_964 = lean_ctor_get(x_963, 0);
lean_inc(x_964);
x_965 = lean_ctor_get(x_963, 1);
lean_inc(x_965);
lean_dec(x_963);
lean_inc(x_962);
x_966 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_962, x_6, x_7, x_8, x_9, x_10, x_11, x_965);
if (lean_obj_tag(x_966) == 0)
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; size_t x_970; size_t x_971; uint8_t x_972; 
x_967 = lean_ctor_get(x_966, 0);
lean_inc(x_967);
x_968 = lean_ctor_get(x_966, 1);
lean_inc(x_968);
if (lean_is_exclusive(x_966)) {
 lean_ctor_release(x_966, 0);
 lean_ctor_release(x_966, 1);
 x_969 = x_966;
} else {
 lean_dec_ref(x_966);
 x_969 = lean_box(0);
}
x_970 = lean_ptr_addr(x_961);
lean_dec(x_961);
x_971 = lean_ptr_addr(x_964);
x_972 = lean_usize_dec_eq(x_970, x_971);
if (x_972 == 0)
{
lean_object* x_973; lean_object* x_974; 
lean_dec(x_962);
lean_dec(x_5);
x_973 = l_Lean_Expr_proj___override(x_959, x_960, x_964, x_967);
if (lean_is_scalar(x_969)) {
 x_974 = lean_alloc_ctor(0, 2, 0);
} else {
 x_974 = x_969;
}
lean_ctor_set(x_974, 0, x_973);
lean_ctor_set(x_974, 1, x_968);
return x_974;
}
else
{
size_t x_975; size_t x_976; uint8_t x_977; 
x_975 = lean_ptr_addr(x_962);
lean_dec(x_962);
x_976 = lean_ptr_addr(x_967);
x_977 = lean_usize_dec_eq(x_975, x_976);
if (x_977 == 0)
{
lean_object* x_978; lean_object* x_979; 
lean_dec(x_5);
x_978 = l_Lean_Expr_proj___override(x_959, x_960, x_964, x_967);
if (lean_is_scalar(x_969)) {
 x_979 = lean_alloc_ctor(0, 2, 0);
} else {
 x_979 = x_969;
}
lean_ctor_set(x_979, 0, x_978);
lean_ctor_set(x_979, 1, x_968);
return x_979;
}
else
{
lean_object* x_980; 
lean_dec(x_967);
lean_dec(x_964);
lean_dec(x_960);
lean_dec(x_959);
if (lean_is_scalar(x_969)) {
 x_980 = lean_alloc_ctor(0, 2, 0);
} else {
 x_980 = x_969;
}
lean_ctor_set(x_980, 0, x_5);
lean_ctor_set(x_980, 1, x_968);
return x_980;
}
}
}
else
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; 
lean_dec(x_964);
lean_dec(x_962);
lean_dec(x_961);
lean_dec(x_960);
lean_dec(x_959);
lean_dec(x_5);
x_981 = lean_ctor_get(x_966, 0);
lean_inc(x_981);
x_982 = lean_ctor_get(x_966, 1);
lean_inc(x_982);
if (lean_is_exclusive(x_966)) {
 lean_ctor_release(x_966, 0);
 lean_ctor_release(x_966, 1);
 x_983 = x_966;
} else {
 lean_dec_ref(x_966);
 x_983 = lean_box(0);
}
if (lean_is_scalar(x_983)) {
 x_984 = lean_alloc_ctor(1, 2, 0);
} else {
 x_984 = x_983;
}
lean_ctor_set(x_984, 0, x_981);
lean_ctor_set(x_984, 1, x_982);
return x_984;
}
}
else
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; 
lean_dec(x_962);
lean_dec(x_961);
lean_dec(x_960);
lean_dec(x_959);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_985 = lean_ctor_get(x_963, 0);
lean_inc(x_985);
x_986 = lean_ctor_get(x_963, 1);
lean_inc(x_986);
if (lean_is_exclusive(x_963)) {
 lean_ctor_release(x_963, 0);
 lean_ctor_release(x_963, 1);
 x_987 = x_963;
} else {
 lean_dec_ref(x_963);
 x_987 = lean_box(0);
}
if (lean_is_scalar(x_987)) {
 x_988 = lean_alloc_ctor(1, 2, 0);
} else {
 x_988 = x_987;
}
lean_ctor_set(x_988, 0, x_985);
lean_ctor_set(x_988, 1, x_986);
return x_988;
}
}
default: 
{
lean_object* x_989; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_989 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_989, 0, x_5);
lean_ctor_set(x_989, 1, x_799);
return x_989;
}
}
}
else
{
lean_object* x_990; lean_object* x_991; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_990 = l_Lean_Expr_bvar___override(x_6);
x_991 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_991, 0, x_990);
lean_ctor_set(x_991, 1, x_799);
return x_991;
}
}
}
}
else
{
uint8_t x_992; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_992 = !lean_is_exclusive(x_275);
if (x_992 == 0)
{
return x_275;
}
else
{
lean_object* x_993; lean_object* x_994; lean_object* x_995; 
x_993 = lean_ctor_get(x_275, 0);
x_994 = lean_ctor_get(x_275, 1);
lean_inc(x_994);
lean_inc(x_993);
lean_dec(x_275);
x_995 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_995, 0, x_993);
lean_ctor_set(x_995, 1, x_994);
return x_995;
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
lean_object* x_996; lean_object* x_997; lean_object* x_998; 
x_996 = lean_ctor_get(x_5, 0);
lean_inc(x_996);
x_997 = lean_ctor_get(x_5, 1);
lean_inc(x_997);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_996);
lean_inc(x_1);
x_998 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_996, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_998) == 0)
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
x_999 = lean_ctor_get(x_998, 0);
lean_inc(x_999);
x_1000 = lean_ctor_get(x_998, 1);
lean_inc(x_1000);
lean_dec(x_998);
lean_inc(x_997);
x_1001 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_997, x_6, x_7, x_8, x_9, x_10, x_11, x_1000);
if (lean_obj_tag(x_1001) == 0)
{
uint8_t x_1002; 
x_1002 = !lean_is_exclusive(x_1001);
if (x_1002 == 0)
{
lean_object* x_1003; size_t x_1004; size_t x_1005; uint8_t x_1006; 
x_1003 = lean_ctor_get(x_1001, 0);
x_1004 = lean_ptr_addr(x_996);
lean_dec(x_996);
x_1005 = lean_ptr_addr(x_999);
x_1006 = lean_usize_dec_eq(x_1004, x_1005);
if (x_1006 == 0)
{
lean_object* x_1007; 
lean_dec(x_997);
lean_dec(x_5);
x_1007 = l_Lean_Expr_app___override(x_999, x_1003);
lean_ctor_set(x_1001, 0, x_1007);
return x_1001;
}
else
{
size_t x_1008; size_t x_1009; uint8_t x_1010; 
x_1008 = lean_ptr_addr(x_997);
lean_dec(x_997);
x_1009 = lean_ptr_addr(x_1003);
x_1010 = lean_usize_dec_eq(x_1008, x_1009);
if (x_1010 == 0)
{
lean_object* x_1011; 
lean_dec(x_5);
x_1011 = l_Lean_Expr_app___override(x_999, x_1003);
lean_ctor_set(x_1001, 0, x_1011);
return x_1001;
}
else
{
lean_dec(x_1003);
lean_dec(x_999);
lean_ctor_set(x_1001, 0, x_5);
return x_1001;
}
}
}
else
{
lean_object* x_1012; lean_object* x_1013; size_t x_1014; size_t x_1015; uint8_t x_1016; 
x_1012 = lean_ctor_get(x_1001, 0);
x_1013 = lean_ctor_get(x_1001, 1);
lean_inc(x_1013);
lean_inc(x_1012);
lean_dec(x_1001);
x_1014 = lean_ptr_addr(x_996);
lean_dec(x_996);
x_1015 = lean_ptr_addr(x_999);
x_1016 = lean_usize_dec_eq(x_1014, x_1015);
if (x_1016 == 0)
{
lean_object* x_1017; lean_object* x_1018; 
lean_dec(x_997);
lean_dec(x_5);
x_1017 = l_Lean_Expr_app___override(x_999, x_1012);
x_1018 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1018, 0, x_1017);
lean_ctor_set(x_1018, 1, x_1013);
return x_1018;
}
else
{
size_t x_1019; size_t x_1020; uint8_t x_1021; 
x_1019 = lean_ptr_addr(x_997);
lean_dec(x_997);
x_1020 = lean_ptr_addr(x_1012);
x_1021 = lean_usize_dec_eq(x_1019, x_1020);
if (x_1021 == 0)
{
lean_object* x_1022; lean_object* x_1023; 
lean_dec(x_5);
x_1022 = l_Lean_Expr_app___override(x_999, x_1012);
x_1023 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1023, 0, x_1022);
lean_ctor_set(x_1023, 1, x_1013);
return x_1023;
}
else
{
lean_object* x_1024; 
lean_dec(x_1012);
lean_dec(x_999);
x_1024 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1024, 0, x_5);
lean_ctor_set(x_1024, 1, x_1013);
return x_1024;
}
}
}
}
else
{
uint8_t x_1025; 
lean_dec(x_999);
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_5);
x_1025 = !lean_is_exclusive(x_1001);
if (x_1025 == 0)
{
return x_1001;
}
else
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; 
x_1026 = lean_ctor_get(x_1001, 0);
x_1027 = lean_ctor_get(x_1001, 1);
lean_inc(x_1027);
lean_inc(x_1026);
lean_dec(x_1001);
x_1028 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1028, 0, x_1026);
lean_ctor_set(x_1028, 1, x_1027);
return x_1028;
}
}
}
else
{
uint8_t x_1029; 
lean_dec(x_997);
lean_dec(x_996);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1029 = !lean_is_exclusive(x_998);
if (x_1029 == 0)
{
return x_998;
}
else
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; 
x_1030 = lean_ctor_get(x_998, 0);
x_1031 = lean_ctor_get(x_998, 1);
lean_inc(x_1031);
lean_inc(x_1030);
lean_dec(x_998);
x_1032 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1032, 0, x_1030);
lean_ctor_set(x_1032, 1, x_1031);
return x_1032;
}
}
}
case 6:
{
lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; uint8_t x_1036; lean_object* x_1037; 
x_1033 = lean_ctor_get(x_5, 0);
lean_inc(x_1033);
x_1034 = lean_ctor_get(x_5, 1);
lean_inc(x_1034);
x_1035 = lean_ctor_get(x_5, 2);
lean_inc(x_1035);
x_1036 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1034);
lean_inc(x_1);
x_1037 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1034, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1037) == 0)
{
lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; 
x_1038 = lean_ctor_get(x_1037, 0);
lean_inc(x_1038);
x_1039 = lean_ctor_get(x_1037, 1);
lean_inc(x_1039);
lean_dec(x_1037);
x_1040 = lean_unsigned_to_nat(1u);
x_1041 = lean_nat_add(x_6, x_1040);
lean_dec(x_6);
lean_inc(x_1035);
x_1042 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1035, x_1041, x_7, x_8, x_9, x_10, x_11, x_1039);
if (lean_obj_tag(x_1042) == 0)
{
uint8_t x_1043; 
x_1043 = !lean_is_exclusive(x_1042);
if (x_1043 == 0)
{
lean_object* x_1044; lean_object* x_1045; size_t x_1046; size_t x_1047; uint8_t x_1048; 
x_1044 = lean_ctor_get(x_1042, 0);
lean_inc(x_1035);
lean_inc(x_1034);
lean_inc(x_1033);
x_1045 = l_Lean_Expr_lam___override(x_1033, x_1034, x_1035, x_1036);
x_1046 = lean_ptr_addr(x_1034);
lean_dec(x_1034);
x_1047 = lean_ptr_addr(x_1038);
x_1048 = lean_usize_dec_eq(x_1046, x_1047);
if (x_1048 == 0)
{
lean_object* x_1049; 
lean_dec(x_1045);
lean_dec(x_1035);
x_1049 = l_Lean_Expr_lam___override(x_1033, x_1038, x_1044, x_1036);
lean_ctor_set(x_1042, 0, x_1049);
return x_1042;
}
else
{
size_t x_1050; size_t x_1051; uint8_t x_1052; 
x_1050 = lean_ptr_addr(x_1035);
lean_dec(x_1035);
x_1051 = lean_ptr_addr(x_1044);
x_1052 = lean_usize_dec_eq(x_1050, x_1051);
if (x_1052 == 0)
{
lean_object* x_1053; 
lean_dec(x_1045);
x_1053 = l_Lean_Expr_lam___override(x_1033, x_1038, x_1044, x_1036);
lean_ctor_set(x_1042, 0, x_1053);
return x_1042;
}
else
{
uint8_t x_1054; 
x_1054 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_1036, x_1036);
if (x_1054 == 0)
{
lean_object* x_1055; 
lean_dec(x_1045);
x_1055 = l_Lean_Expr_lam___override(x_1033, x_1038, x_1044, x_1036);
lean_ctor_set(x_1042, 0, x_1055);
return x_1042;
}
else
{
lean_dec(x_1044);
lean_dec(x_1038);
lean_dec(x_1033);
lean_ctor_set(x_1042, 0, x_1045);
return x_1042;
}
}
}
}
else
{
lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; size_t x_1059; size_t x_1060; uint8_t x_1061; 
x_1056 = lean_ctor_get(x_1042, 0);
x_1057 = lean_ctor_get(x_1042, 1);
lean_inc(x_1057);
lean_inc(x_1056);
lean_dec(x_1042);
lean_inc(x_1035);
lean_inc(x_1034);
lean_inc(x_1033);
x_1058 = l_Lean_Expr_lam___override(x_1033, x_1034, x_1035, x_1036);
x_1059 = lean_ptr_addr(x_1034);
lean_dec(x_1034);
x_1060 = lean_ptr_addr(x_1038);
x_1061 = lean_usize_dec_eq(x_1059, x_1060);
if (x_1061 == 0)
{
lean_object* x_1062; lean_object* x_1063; 
lean_dec(x_1058);
lean_dec(x_1035);
x_1062 = l_Lean_Expr_lam___override(x_1033, x_1038, x_1056, x_1036);
x_1063 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1063, 0, x_1062);
lean_ctor_set(x_1063, 1, x_1057);
return x_1063;
}
else
{
size_t x_1064; size_t x_1065; uint8_t x_1066; 
x_1064 = lean_ptr_addr(x_1035);
lean_dec(x_1035);
x_1065 = lean_ptr_addr(x_1056);
x_1066 = lean_usize_dec_eq(x_1064, x_1065);
if (x_1066 == 0)
{
lean_object* x_1067; lean_object* x_1068; 
lean_dec(x_1058);
x_1067 = l_Lean_Expr_lam___override(x_1033, x_1038, x_1056, x_1036);
x_1068 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1068, 0, x_1067);
lean_ctor_set(x_1068, 1, x_1057);
return x_1068;
}
else
{
uint8_t x_1069; 
x_1069 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_1036, x_1036);
if (x_1069 == 0)
{
lean_object* x_1070; lean_object* x_1071; 
lean_dec(x_1058);
x_1070 = l_Lean_Expr_lam___override(x_1033, x_1038, x_1056, x_1036);
x_1071 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1071, 0, x_1070);
lean_ctor_set(x_1071, 1, x_1057);
return x_1071;
}
else
{
lean_object* x_1072; 
lean_dec(x_1056);
lean_dec(x_1038);
lean_dec(x_1033);
x_1072 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1072, 0, x_1058);
lean_ctor_set(x_1072, 1, x_1057);
return x_1072;
}
}
}
}
}
else
{
uint8_t x_1073; 
lean_dec(x_1038);
lean_dec(x_1035);
lean_dec(x_1034);
lean_dec(x_1033);
x_1073 = !lean_is_exclusive(x_1042);
if (x_1073 == 0)
{
return x_1042;
}
else
{
lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; 
x_1074 = lean_ctor_get(x_1042, 0);
x_1075 = lean_ctor_get(x_1042, 1);
lean_inc(x_1075);
lean_inc(x_1074);
lean_dec(x_1042);
x_1076 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1076, 0, x_1074);
lean_ctor_set(x_1076, 1, x_1075);
return x_1076;
}
}
}
else
{
uint8_t x_1077; 
lean_dec(x_1035);
lean_dec(x_1034);
lean_dec(x_1033);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1077 = !lean_is_exclusive(x_1037);
if (x_1077 == 0)
{
return x_1037;
}
else
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; 
x_1078 = lean_ctor_get(x_1037, 0);
x_1079 = lean_ctor_get(x_1037, 1);
lean_inc(x_1079);
lean_inc(x_1078);
lean_dec(x_1037);
x_1080 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1080, 0, x_1078);
lean_ctor_set(x_1080, 1, x_1079);
return x_1080;
}
}
}
case 7:
{
lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; uint8_t x_1084; lean_object* x_1085; 
x_1081 = lean_ctor_get(x_5, 0);
lean_inc(x_1081);
x_1082 = lean_ctor_get(x_5, 1);
lean_inc(x_1082);
x_1083 = lean_ctor_get(x_5, 2);
lean_inc(x_1083);
x_1084 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1082);
lean_inc(x_1);
x_1085 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1082, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1085) == 0)
{
lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; 
x_1086 = lean_ctor_get(x_1085, 0);
lean_inc(x_1086);
x_1087 = lean_ctor_get(x_1085, 1);
lean_inc(x_1087);
lean_dec(x_1085);
x_1088 = lean_unsigned_to_nat(1u);
x_1089 = lean_nat_add(x_6, x_1088);
lean_dec(x_6);
lean_inc(x_1083);
x_1090 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1083, x_1089, x_7, x_8, x_9, x_10, x_11, x_1087);
if (lean_obj_tag(x_1090) == 0)
{
uint8_t x_1091; 
x_1091 = !lean_is_exclusive(x_1090);
if (x_1091 == 0)
{
lean_object* x_1092; lean_object* x_1093; size_t x_1094; size_t x_1095; uint8_t x_1096; 
x_1092 = lean_ctor_get(x_1090, 0);
lean_inc(x_1083);
lean_inc(x_1082);
lean_inc(x_1081);
x_1093 = l_Lean_Expr_forallE___override(x_1081, x_1082, x_1083, x_1084);
x_1094 = lean_ptr_addr(x_1082);
lean_dec(x_1082);
x_1095 = lean_ptr_addr(x_1086);
x_1096 = lean_usize_dec_eq(x_1094, x_1095);
if (x_1096 == 0)
{
lean_object* x_1097; 
lean_dec(x_1093);
lean_dec(x_1083);
x_1097 = l_Lean_Expr_forallE___override(x_1081, x_1086, x_1092, x_1084);
lean_ctor_set(x_1090, 0, x_1097);
return x_1090;
}
else
{
size_t x_1098; size_t x_1099; uint8_t x_1100; 
x_1098 = lean_ptr_addr(x_1083);
lean_dec(x_1083);
x_1099 = lean_ptr_addr(x_1092);
x_1100 = lean_usize_dec_eq(x_1098, x_1099);
if (x_1100 == 0)
{
lean_object* x_1101; 
lean_dec(x_1093);
x_1101 = l_Lean_Expr_forallE___override(x_1081, x_1086, x_1092, x_1084);
lean_ctor_set(x_1090, 0, x_1101);
return x_1090;
}
else
{
uint8_t x_1102; 
x_1102 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_1084, x_1084);
if (x_1102 == 0)
{
lean_object* x_1103; 
lean_dec(x_1093);
x_1103 = l_Lean_Expr_forallE___override(x_1081, x_1086, x_1092, x_1084);
lean_ctor_set(x_1090, 0, x_1103);
return x_1090;
}
else
{
lean_dec(x_1092);
lean_dec(x_1086);
lean_dec(x_1081);
lean_ctor_set(x_1090, 0, x_1093);
return x_1090;
}
}
}
}
else
{
lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; size_t x_1107; size_t x_1108; uint8_t x_1109; 
x_1104 = lean_ctor_get(x_1090, 0);
x_1105 = lean_ctor_get(x_1090, 1);
lean_inc(x_1105);
lean_inc(x_1104);
lean_dec(x_1090);
lean_inc(x_1083);
lean_inc(x_1082);
lean_inc(x_1081);
x_1106 = l_Lean_Expr_forallE___override(x_1081, x_1082, x_1083, x_1084);
x_1107 = lean_ptr_addr(x_1082);
lean_dec(x_1082);
x_1108 = lean_ptr_addr(x_1086);
x_1109 = lean_usize_dec_eq(x_1107, x_1108);
if (x_1109 == 0)
{
lean_object* x_1110; lean_object* x_1111; 
lean_dec(x_1106);
lean_dec(x_1083);
x_1110 = l_Lean_Expr_forallE___override(x_1081, x_1086, x_1104, x_1084);
x_1111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1111, 0, x_1110);
lean_ctor_set(x_1111, 1, x_1105);
return x_1111;
}
else
{
size_t x_1112; size_t x_1113; uint8_t x_1114; 
x_1112 = lean_ptr_addr(x_1083);
lean_dec(x_1083);
x_1113 = lean_ptr_addr(x_1104);
x_1114 = lean_usize_dec_eq(x_1112, x_1113);
if (x_1114 == 0)
{
lean_object* x_1115; lean_object* x_1116; 
lean_dec(x_1106);
x_1115 = l_Lean_Expr_forallE___override(x_1081, x_1086, x_1104, x_1084);
x_1116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1116, 0, x_1115);
lean_ctor_set(x_1116, 1, x_1105);
return x_1116;
}
else
{
uint8_t x_1117; 
x_1117 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_1084, x_1084);
if (x_1117 == 0)
{
lean_object* x_1118; lean_object* x_1119; 
lean_dec(x_1106);
x_1118 = l_Lean_Expr_forallE___override(x_1081, x_1086, x_1104, x_1084);
x_1119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1119, 0, x_1118);
lean_ctor_set(x_1119, 1, x_1105);
return x_1119;
}
else
{
lean_object* x_1120; 
lean_dec(x_1104);
lean_dec(x_1086);
lean_dec(x_1081);
x_1120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1120, 0, x_1106);
lean_ctor_set(x_1120, 1, x_1105);
return x_1120;
}
}
}
}
}
else
{
uint8_t x_1121; 
lean_dec(x_1086);
lean_dec(x_1083);
lean_dec(x_1082);
lean_dec(x_1081);
x_1121 = !lean_is_exclusive(x_1090);
if (x_1121 == 0)
{
return x_1090;
}
else
{
lean_object* x_1122; lean_object* x_1123; lean_object* x_1124; 
x_1122 = lean_ctor_get(x_1090, 0);
x_1123 = lean_ctor_get(x_1090, 1);
lean_inc(x_1123);
lean_inc(x_1122);
lean_dec(x_1090);
x_1124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1124, 0, x_1122);
lean_ctor_set(x_1124, 1, x_1123);
return x_1124;
}
}
}
else
{
uint8_t x_1125; 
lean_dec(x_1083);
lean_dec(x_1082);
lean_dec(x_1081);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1125 = !lean_is_exclusive(x_1085);
if (x_1125 == 0)
{
return x_1085;
}
else
{
lean_object* x_1126; lean_object* x_1127; lean_object* x_1128; 
x_1126 = lean_ctor_get(x_1085, 0);
x_1127 = lean_ctor_get(x_1085, 1);
lean_inc(x_1127);
lean_inc(x_1126);
lean_dec(x_1085);
x_1128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1128, 0, x_1126);
lean_ctor_set(x_1128, 1, x_1127);
return x_1128;
}
}
}
case 8:
{
lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; uint8_t x_1133; lean_object* x_1134; 
x_1129 = lean_ctor_get(x_5, 0);
lean_inc(x_1129);
x_1130 = lean_ctor_get(x_5, 1);
lean_inc(x_1130);
x_1131 = lean_ctor_get(x_5, 2);
lean_inc(x_1131);
x_1132 = lean_ctor_get(x_5, 3);
lean_inc(x_1132);
x_1133 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1130);
lean_inc(x_1);
x_1134 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1130, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1134) == 0)
{
lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; 
x_1135 = lean_ctor_get(x_1134, 0);
lean_inc(x_1135);
x_1136 = lean_ctor_get(x_1134, 1);
lean_inc(x_1136);
lean_dec(x_1134);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1131);
lean_inc(x_1);
x_1137 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1131, x_6, x_7, x_8, x_9, x_10, x_11, x_1136);
if (lean_obj_tag(x_1137) == 0)
{
lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; lean_object* x_1141; lean_object* x_1142; 
x_1138 = lean_ctor_get(x_1137, 0);
lean_inc(x_1138);
x_1139 = lean_ctor_get(x_1137, 1);
lean_inc(x_1139);
lean_dec(x_1137);
x_1140 = lean_unsigned_to_nat(1u);
x_1141 = lean_nat_add(x_6, x_1140);
lean_dec(x_6);
lean_inc(x_1132);
x_1142 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1132, x_1141, x_7, x_8, x_9, x_10, x_11, x_1139);
if (lean_obj_tag(x_1142) == 0)
{
uint8_t x_1143; 
x_1143 = !lean_is_exclusive(x_1142);
if (x_1143 == 0)
{
lean_object* x_1144; size_t x_1145; size_t x_1146; uint8_t x_1147; 
x_1144 = lean_ctor_get(x_1142, 0);
x_1145 = lean_ptr_addr(x_1130);
lean_dec(x_1130);
x_1146 = lean_ptr_addr(x_1135);
x_1147 = lean_usize_dec_eq(x_1145, x_1146);
if (x_1147 == 0)
{
lean_object* x_1148; 
lean_dec(x_1132);
lean_dec(x_1131);
lean_dec(x_5);
x_1148 = l_Lean_Expr_letE___override(x_1129, x_1135, x_1138, x_1144, x_1133);
lean_ctor_set(x_1142, 0, x_1148);
return x_1142;
}
else
{
size_t x_1149; size_t x_1150; uint8_t x_1151; 
x_1149 = lean_ptr_addr(x_1131);
lean_dec(x_1131);
x_1150 = lean_ptr_addr(x_1138);
x_1151 = lean_usize_dec_eq(x_1149, x_1150);
if (x_1151 == 0)
{
lean_object* x_1152; 
lean_dec(x_1132);
lean_dec(x_5);
x_1152 = l_Lean_Expr_letE___override(x_1129, x_1135, x_1138, x_1144, x_1133);
lean_ctor_set(x_1142, 0, x_1152);
return x_1142;
}
else
{
size_t x_1153; size_t x_1154; uint8_t x_1155; 
x_1153 = lean_ptr_addr(x_1132);
lean_dec(x_1132);
x_1154 = lean_ptr_addr(x_1144);
x_1155 = lean_usize_dec_eq(x_1153, x_1154);
if (x_1155 == 0)
{
lean_object* x_1156; 
lean_dec(x_5);
x_1156 = l_Lean_Expr_letE___override(x_1129, x_1135, x_1138, x_1144, x_1133);
lean_ctor_set(x_1142, 0, x_1156);
return x_1142;
}
else
{
lean_dec(x_1144);
lean_dec(x_1138);
lean_dec(x_1135);
lean_dec(x_1129);
lean_ctor_set(x_1142, 0, x_5);
return x_1142;
}
}
}
}
else
{
lean_object* x_1157; lean_object* x_1158; size_t x_1159; size_t x_1160; uint8_t x_1161; 
x_1157 = lean_ctor_get(x_1142, 0);
x_1158 = lean_ctor_get(x_1142, 1);
lean_inc(x_1158);
lean_inc(x_1157);
lean_dec(x_1142);
x_1159 = lean_ptr_addr(x_1130);
lean_dec(x_1130);
x_1160 = lean_ptr_addr(x_1135);
x_1161 = lean_usize_dec_eq(x_1159, x_1160);
if (x_1161 == 0)
{
lean_object* x_1162; lean_object* x_1163; 
lean_dec(x_1132);
lean_dec(x_1131);
lean_dec(x_5);
x_1162 = l_Lean_Expr_letE___override(x_1129, x_1135, x_1138, x_1157, x_1133);
x_1163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1163, 0, x_1162);
lean_ctor_set(x_1163, 1, x_1158);
return x_1163;
}
else
{
size_t x_1164; size_t x_1165; uint8_t x_1166; 
x_1164 = lean_ptr_addr(x_1131);
lean_dec(x_1131);
x_1165 = lean_ptr_addr(x_1138);
x_1166 = lean_usize_dec_eq(x_1164, x_1165);
if (x_1166 == 0)
{
lean_object* x_1167; lean_object* x_1168; 
lean_dec(x_1132);
lean_dec(x_5);
x_1167 = l_Lean_Expr_letE___override(x_1129, x_1135, x_1138, x_1157, x_1133);
x_1168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1168, 0, x_1167);
lean_ctor_set(x_1168, 1, x_1158);
return x_1168;
}
else
{
size_t x_1169; size_t x_1170; uint8_t x_1171; 
x_1169 = lean_ptr_addr(x_1132);
lean_dec(x_1132);
x_1170 = lean_ptr_addr(x_1157);
x_1171 = lean_usize_dec_eq(x_1169, x_1170);
if (x_1171 == 0)
{
lean_object* x_1172; lean_object* x_1173; 
lean_dec(x_5);
x_1172 = l_Lean_Expr_letE___override(x_1129, x_1135, x_1138, x_1157, x_1133);
x_1173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1173, 0, x_1172);
lean_ctor_set(x_1173, 1, x_1158);
return x_1173;
}
else
{
lean_object* x_1174; 
lean_dec(x_1157);
lean_dec(x_1138);
lean_dec(x_1135);
lean_dec(x_1129);
x_1174 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1174, 0, x_5);
lean_ctor_set(x_1174, 1, x_1158);
return x_1174;
}
}
}
}
}
else
{
uint8_t x_1175; 
lean_dec(x_1138);
lean_dec(x_1135);
lean_dec(x_1132);
lean_dec(x_1131);
lean_dec(x_1130);
lean_dec(x_1129);
lean_dec(x_5);
x_1175 = !lean_is_exclusive(x_1142);
if (x_1175 == 0)
{
return x_1142;
}
else
{
lean_object* x_1176; lean_object* x_1177; lean_object* x_1178; 
x_1176 = lean_ctor_get(x_1142, 0);
x_1177 = lean_ctor_get(x_1142, 1);
lean_inc(x_1177);
lean_inc(x_1176);
lean_dec(x_1142);
x_1178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1178, 0, x_1176);
lean_ctor_set(x_1178, 1, x_1177);
return x_1178;
}
}
}
else
{
uint8_t x_1179; 
lean_dec(x_1135);
lean_dec(x_1132);
lean_dec(x_1131);
lean_dec(x_1130);
lean_dec(x_1129);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1179 = !lean_is_exclusive(x_1137);
if (x_1179 == 0)
{
return x_1137;
}
else
{
lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; 
x_1180 = lean_ctor_get(x_1137, 0);
x_1181 = lean_ctor_get(x_1137, 1);
lean_inc(x_1181);
lean_inc(x_1180);
lean_dec(x_1137);
x_1182 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1182, 0, x_1180);
lean_ctor_set(x_1182, 1, x_1181);
return x_1182;
}
}
}
else
{
uint8_t x_1183; 
lean_dec(x_1132);
lean_dec(x_1131);
lean_dec(x_1130);
lean_dec(x_1129);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1183 = !lean_is_exclusive(x_1134);
if (x_1183 == 0)
{
return x_1134;
}
else
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
x_1184 = lean_ctor_get(x_1134, 0);
x_1185 = lean_ctor_get(x_1134, 1);
lean_inc(x_1185);
lean_inc(x_1184);
lean_dec(x_1134);
x_1186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1186, 0, x_1184);
lean_ctor_set(x_1186, 1, x_1185);
return x_1186;
}
}
}
case 10:
{
lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; 
x_1187 = lean_ctor_get(x_5, 0);
lean_inc(x_1187);
x_1188 = lean_ctor_get(x_5, 1);
lean_inc(x_1188);
lean_inc(x_1188);
x_1189 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1188, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1189) == 0)
{
uint8_t x_1190; 
x_1190 = !lean_is_exclusive(x_1189);
if (x_1190 == 0)
{
lean_object* x_1191; size_t x_1192; size_t x_1193; uint8_t x_1194; 
x_1191 = lean_ctor_get(x_1189, 0);
x_1192 = lean_ptr_addr(x_1188);
lean_dec(x_1188);
x_1193 = lean_ptr_addr(x_1191);
x_1194 = lean_usize_dec_eq(x_1192, x_1193);
if (x_1194 == 0)
{
lean_object* x_1195; 
lean_dec(x_5);
x_1195 = l_Lean_Expr_mdata___override(x_1187, x_1191);
lean_ctor_set(x_1189, 0, x_1195);
return x_1189;
}
else
{
lean_dec(x_1191);
lean_dec(x_1187);
lean_ctor_set(x_1189, 0, x_5);
return x_1189;
}
}
else
{
lean_object* x_1196; lean_object* x_1197; size_t x_1198; size_t x_1199; uint8_t x_1200; 
x_1196 = lean_ctor_get(x_1189, 0);
x_1197 = lean_ctor_get(x_1189, 1);
lean_inc(x_1197);
lean_inc(x_1196);
lean_dec(x_1189);
x_1198 = lean_ptr_addr(x_1188);
lean_dec(x_1188);
x_1199 = lean_ptr_addr(x_1196);
x_1200 = lean_usize_dec_eq(x_1198, x_1199);
if (x_1200 == 0)
{
lean_object* x_1201; lean_object* x_1202; 
lean_dec(x_5);
x_1201 = l_Lean_Expr_mdata___override(x_1187, x_1196);
x_1202 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1202, 0, x_1201);
lean_ctor_set(x_1202, 1, x_1197);
return x_1202;
}
else
{
lean_object* x_1203; 
lean_dec(x_1196);
lean_dec(x_1187);
x_1203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1203, 0, x_5);
lean_ctor_set(x_1203, 1, x_1197);
return x_1203;
}
}
}
else
{
uint8_t x_1204; 
lean_dec(x_1188);
lean_dec(x_1187);
lean_dec(x_5);
x_1204 = !lean_is_exclusive(x_1189);
if (x_1204 == 0)
{
return x_1189;
}
else
{
lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; 
x_1205 = lean_ctor_get(x_1189, 0);
x_1206 = lean_ctor_get(x_1189, 1);
lean_inc(x_1206);
lean_inc(x_1205);
lean_dec(x_1189);
x_1207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1207, 0, x_1205);
lean_ctor_set(x_1207, 1, x_1206);
return x_1207;
}
}
}
case 11:
{
lean_object* x_1208; lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; 
x_1208 = lean_ctor_get(x_5, 0);
lean_inc(x_1208);
x_1209 = lean_ctor_get(x_5, 1);
lean_inc(x_1209);
x_1210 = lean_ctor_get(x_5, 2);
lean_inc(x_1210);
x_1211 = lean_ctor_get(x_5, 3);
lean_inc(x_1211);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1210);
lean_inc(x_1);
x_1212 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1210, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1212) == 0)
{
lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; 
x_1213 = lean_ctor_get(x_1212, 0);
lean_inc(x_1213);
x_1214 = lean_ctor_get(x_1212, 1);
lean_inc(x_1214);
lean_dec(x_1212);
lean_inc(x_1211);
x_1215 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1211, x_6, x_7, x_8, x_9, x_10, x_11, x_1214);
if (lean_obj_tag(x_1215) == 0)
{
uint8_t x_1216; 
x_1216 = !lean_is_exclusive(x_1215);
if (x_1216 == 0)
{
lean_object* x_1217; size_t x_1218; size_t x_1219; uint8_t x_1220; 
x_1217 = lean_ctor_get(x_1215, 0);
x_1218 = lean_ptr_addr(x_1210);
lean_dec(x_1210);
x_1219 = lean_ptr_addr(x_1213);
x_1220 = lean_usize_dec_eq(x_1218, x_1219);
if (x_1220 == 0)
{
lean_object* x_1221; 
lean_dec(x_1211);
lean_dec(x_5);
x_1221 = l_Lean_Expr_proj___override(x_1208, x_1209, x_1213, x_1217);
lean_ctor_set(x_1215, 0, x_1221);
return x_1215;
}
else
{
size_t x_1222; size_t x_1223; uint8_t x_1224; 
x_1222 = lean_ptr_addr(x_1211);
lean_dec(x_1211);
x_1223 = lean_ptr_addr(x_1217);
x_1224 = lean_usize_dec_eq(x_1222, x_1223);
if (x_1224 == 0)
{
lean_object* x_1225; 
lean_dec(x_5);
x_1225 = l_Lean_Expr_proj___override(x_1208, x_1209, x_1213, x_1217);
lean_ctor_set(x_1215, 0, x_1225);
return x_1215;
}
else
{
lean_dec(x_1217);
lean_dec(x_1213);
lean_dec(x_1209);
lean_dec(x_1208);
lean_ctor_set(x_1215, 0, x_5);
return x_1215;
}
}
}
else
{
lean_object* x_1226; lean_object* x_1227; size_t x_1228; size_t x_1229; uint8_t x_1230; 
x_1226 = lean_ctor_get(x_1215, 0);
x_1227 = lean_ctor_get(x_1215, 1);
lean_inc(x_1227);
lean_inc(x_1226);
lean_dec(x_1215);
x_1228 = lean_ptr_addr(x_1210);
lean_dec(x_1210);
x_1229 = lean_ptr_addr(x_1213);
x_1230 = lean_usize_dec_eq(x_1228, x_1229);
if (x_1230 == 0)
{
lean_object* x_1231; lean_object* x_1232; 
lean_dec(x_1211);
lean_dec(x_5);
x_1231 = l_Lean_Expr_proj___override(x_1208, x_1209, x_1213, x_1226);
x_1232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1232, 0, x_1231);
lean_ctor_set(x_1232, 1, x_1227);
return x_1232;
}
else
{
size_t x_1233; size_t x_1234; uint8_t x_1235; 
x_1233 = lean_ptr_addr(x_1211);
lean_dec(x_1211);
x_1234 = lean_ptr_addr(x_1226);
x_1235 = lean_usize_dec_eq(x_1233, x_1234);
if (x_1235 == 0)
{
lean_object* x_1236; lean_object* x_1237; 
lean_dec(x_5);
x_1236 = l_Lean_Expr_proj___override(x_1208, x_1209, x_1213, x_1226);
x_1237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1237, 0, x_1236);
lean_ctor_set(x_1237, 1, x_1227);
return x_1237;
}
else
{
lean_object* x_1238; 
lean_dec(x_1226);
lean_dec(x_1213);
lean_dec(x_1209);
lean_dec(x_1208);
x_1238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1238, 0, x_5);
lean_ctor_set(x_1238, 1, x_1227);
return x_1238;
}
}
}
}
else
{
uint8_t x_1239; 
lean_dec(x_1213);
lean_dec(x_1211);
lean_dec(x_1210);
lean_dec(x_1209);
lean_dec(x_1208);
lean_dec(x_5);
x_1239 = !lean_is_exclusive(x_1215);
if (x_1239 == 0)
{
return x_1215;
}
else
{
lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; 
x_1240 = lean_ctor_get(x_1215, 0);
x_1241 = lean_ctor_get(x_1215, 1);
lean_inc(x_1241);
lean_inc(x_1240);
lean_dec(x_1215);
x_1242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1242, 0, x_1240);
lean_ctor_set(x_1242, 1, x_1241);
return x_1242;
}
}
}
else
{
uint8_t x_1243; 
lean_dec(x_1211);
lean_dec(x_1210);
lean_dec(x_1209);
lean_dec(x_1208);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1243 = !lean_is_exclusive(x_1212);
if (x_1243 == 0)
{
return x_1212;
}
else
{
lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; 
x_1244 = lean_ctor_get(x_1212, 0);
x_1245 = lean_ctor_get(x_1212, 1);
lean_inc(x_1245);
lean_inc(x_1244);
lean_dec(x_1212);
x_1246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1246, 0, x_1244);
lean_ctor_set(x_1246, 1, x_1245);
return x_1246;
}
}
}
default: 
{
lean_object* x_1247; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1247 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1247, 0, x_5);
lean_ctor_set(x_1247, 1, x_12);
return x_1247;
}
}
}
block_266:
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
x_72 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_54, x_54);
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
x_87 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_54, x_54);
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
x_120 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_102, x_102);
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
x_135 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_102, x_102);
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
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_226 = lean_ctor_get(x_5, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_5, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_5, 2);
lean_inc(x_228);
x_229 = lean_ctor_get(x_5, 3);
lean_inc(x_229);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_228);
lean_inc(x_1);
x_230 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_228, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
lean_inc(x_229);
x_233 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_229, x_6, x_7, x_8, x_9, x_10, x_11, x_232);
if (lean_obj_tag(x_233) == 0)
{
uint8_t x_234; 
x_234 = !lean_is_exclusive(x_233);
if (x_234 == 0)
{
lean_object* x_235; size_t x_236; size_t x_237; uint8_t x_238; 
x_235 = lean_ctor_get(x_233, 0);
x_236 = lean_ptr_addr(x_228);
lean_dec(x_228);
x_237 = lean_ptr_addr(x_231);
x_238 = lean_usize_dec_eq(x_236, x_237);
if (x_238 == 0)
{
lean_object* x_239; 
lean_dec(x_229);
lean_dec(x_5);
x_239 = l_Lean_Expr_proj___override(x_226, x_227, x_231, x_235);
lean_ctor_set(x_233, 0, x_239);
return x_233;
}
else
{
size_t x_240; size_t x_241; uint8_t x_242; 
x_240 = lean_ptr_addr(x_229);
lean_dec(x_229);
x_241 = lean_ptr_addr(x_235);
x_242 = lean_usize_dec_eq(x_240, x_241);
if (x_242 == 0)
{
lean_object* x_243; 
lean_dec(x_5);
x_243 = l_Lean_Expr_proj___override(x_226, x_227, x_231, x_235);
lean_ctor_set(x_233, 0, x_243);
return x_233;
}
else
{
lean_dec(x_235);
lean_dec(x_231);
lean_dec(x_227);
lean_dec(x_226);
lean_ctor_set(x_233, 0, x_5);
return x_233;
}
}
}
else
{
lean_object* x_244; lean_object* x_245; size_t x_246; size_t x_247; uint8_t x_248; 
x_244 = lean_ctor_get(x_233, 0);
x_245 = lean_ctor_get(x_233, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_233);
x_246 = lean_ptr_addr(x_228);
lean_dec(x_228);
x_247 = lean_ptr_addr(x_231);
x_248 = lean_usize_dec_eq(x_246, x_247);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_229);
lean_dec(x_5);
x_249 = l_Lean_Expr_proj___override(x_226, x_227, x_231, x_244);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_245);
return x_250;
}
else
{
size_t x_251; size_t x_252; uint8_t x_253; 
x_251 = lean_ptr_addr(x_229);
lean_dec(x_229);
x_252 = lean_ptr_addr(x_244);
x_253 = lean_usize_dec_eq(x_251, x_252);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_5);
x_254 = l_Lean_Expr_proj___override(x_226, x_227, x_231, x_244);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_245);
return x_255;
}
else
{
lean_object* x_256; 
lean_dec(x_244);
lean_dec(x_231);
lean_dec(x_227);
lean_dec(x_226);
x_256 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_256, 0, x_5);
lean_ctor_set(x_256, 1, x_245);
return x_256;
}
}
}
}
else
{
uint8_t x_257; 
lean_dec(x_231);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_5);
x_257 = !lean_is_exclusive(x_233);
if (x_257 == 0)
{
return x_233;
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_ctor_get(x_233, 0);
x_259 = lean_ctor_get(x_233, 1);
lean_inc(x_259);
lean_inc(x_258);
lean_dec(x_233);
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
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_261 = !lean_is_exclusive(x_230);
if (x_261 == 0)
{
return x_230;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_230, 0);
x_263 = lean_ctor_get(x_230, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_230);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
default: 
{
lean_object* x_265; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_5);
lean_ctor_set(x_265, 1, x_12);
return x_265;
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
x_34 = l___private_Init_Meta_0__Lean_Meta_beqOccurrences____x40_Init_Meta___hyg_14366_(x_3, x_33);
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
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_54 = l_Lean_Meta_kabstract___closed__1;
x_55 = lean_array_push(x_54, x_2);
x_56 = lean_expr_abstract(x_11, x_55);
lean_dec(x_55);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_56);
return x_9;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_57 = lean_ctor_get(x_9, 0);
x_58 = lean_ctor_get(x_9, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_9);
x_59 = l_Lean_Expr_isFVar(x_2);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_inc(x_2);
x_60 = l_Lean_Expr_toHeadIndex(x_2);
x_61 = lean_unsigned_to_nat(0u);
x_62 = l_Lean_Expr_headNumArgs_go(x_2, x_61);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_st_mk_ref(x_63, x_58);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_60, x_62, x_57, x_61, x_65, x_4, x_5, x_6, x_7, x_66);
lean_dec(x_62);
lean_dec(x_60);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_st_ref_get(x_65, x_69);
lean_dec(x_65);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_72 = x_70;
} else {
 lean_dec_ref(x_70);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_65);
x_74 = lean_ctor_get(x_67, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_67, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_76 = x_67;
} else {
 lean_dec_ref(x_67);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(1, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_box(0);
x_79 = l___private_Init_Meta_0__Lean_Meta_beqOccurrences____x40_Init_Meta___hyg_14366_(x_3, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_inc(x_2);
x_80 = l_Lean_Expr_toHeadIndex(x_2);
x_81 = lean_unsigned_to_nat(0u);
x_82 = l_Lean_Expr_headNumArgs_go(x_2, x_81);
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_st_mk_ref(x_83, x_58);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Meta_kabstract_visit(x_2, x_3, x_80, x_82, x_57, x_81, x_85, x_4, x_5, x_6, x_7, x_86);
lean_dec(x_82);
lean_dec(x_80);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_st_ref_get(x_85, x_89);
lean_dec(x_85);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_92 = x_90;
} else {
 lean_dec_ref(x_90);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_88);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_85);
x_94 = lean_ctor_get(x_87, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_87, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 lean_ctor_release(x_87, 1);
 x_96 = x_87;
} else {
 lean_dec_ref(x_87);
 x_96 = lean_box(0);
}
if (lean_is_scalar(x_96)) {
 x_97 = lean_alloc_ctor(1, 2, 0);
} else {
 x_97 = x_96;
}
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_98 = l_Lean_Meta_kabstract___closed__1;
x_99 = lean_array_push(x_98, x_2);
x_100 = lean_expr_abstract(x_57, x_99);
lean_dec(x_99);
lean_dec(x_57);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_58);
return x_101;
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
