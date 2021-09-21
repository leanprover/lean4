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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_expr_update_mdata(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_Occurrences_contains(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
lean_object* lean_expr_update_let(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_Data_binderInfo(uint64_t);
lean_object* lean_expr_update_proj(lean_object*, lean_object*);
lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(lean_object*, lean_object*);
uint8_t l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_65_(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_31_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* lean_expr_update_lambda(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_instantiateMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* lean_expr_update_app(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkBVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_kabstract___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_290; 
x_290 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_290 == 0)
{
lean_object* x_291; uint8_t x_292; 
x_291 = l_Lean_Expr_toHeadIndex(x_5);
x_292 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_65_(x_291, x_3);
lean_dec(x_291);
if (x_292 == 0)
{
lean_object* x_293; 
x_293 = lean_box(0);
x_13 = x_293;
goto block_289;
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; 
x_294 = lean_unsigned_to_nat(0u);
x_295 = l___private_Lean_HeadIndex_0__Lean_Expr_headNumArgsAux(x_5, x_294);
x_296 = lean_nat_dec_eq(x_295, x_4);
lean_dec(x_295);
if (x_296 == 0)
{
lean_object* x_297; 
x_297 = lean_box(0);
x_13 = x_297;
goto block_289;
}
else
{
lean_object* x_298; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_5);
x_298 = l_Lean_Meta_isExprDefEq(x_5, x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; uint8_t x_300; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_unbox(x_299);
lean_dec(x_299);
if (x_300 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_301; uint8_t x_302; 
x_301 = lean_ctor_get(x_298, 1);
lean_inc(x_301);
lean_dec(x_298);
x_302 = !lean_is_exclusive(x_5);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_5, 0);
x_304 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_303);
lean_inc(x_1);
x_305 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_303, x_6, x_7, x_8, x_9, x_10, x_11, x_301);
if (lean_obj_tag(x_305) == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; 
x_306 = lean_ctor_get(x_305, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_305, 1);
lean_inc(x_307);
lean_dec(x_305);
lean_inc(x_304);
x_308 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_304, x_6, x_7, x_8, x_9, x_10, x_11, x_307);
if (lean_obj_tag(x_308) == 0)
{
uint8_t x_309; 
x_309 = !lean_is_exclusive(x_308);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; 
x_310 = lean_ctor_get(x_308, 0);
x_311 = lean_expr_update_app(x_5, x_306, x_310);
lean_ctor_set(x_308, 0, x_311);
return x_308;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_312 = lean_ctor_get(x_308, 0);
x_313 = lean_ctor_get(x_308, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_308);
x_314 = lean_expr_update_app(x_5, x_306, x_312);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_313);
return x_315;
}
}
else
{
uint8_t x_316; 
lean_dec(x_306);
lean_free_object(x_5);
lean_dec(x_304);
lean_dec(x_303);
x_316 = !lean_is_exclusive(x_308);
if (x_316 == 0)
{
return x_308;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_308, 0);
x_318 = lean_ctor_get(x_308, 1);
lean_inc(x_318);
lean_inc(x_317);
lean_dec(x_308);
x_319 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_319, 0, x_317);
lean_ctor_set(x_319, 1, x_318);
return x_319;
}
}
}
else
{
uint8_t x_320; 
lean_free_object(x_5);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_320 = !lean_is_exclusive(x_305);
if (x_320 == 0)
{
return x_305;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_321 = lean_ctor_get(x_305, 0);
x_322 = lean_ctor_get(x_305, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_305);
x_323 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_323, 0, x_321);
lean_ctor_set(x_323, 1, x_322);
return x_323;
}
}
}
else
{
lean_object* x_324; lean_object* x_325; uint64_t x_326; lean_object* x_327; 
x_324 = lean_ctor_get(x_5, 0);
x_325 = lean_ctor_get(x_5, 1);
x_326 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_324);
lean_inc(x_1);
x_327 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_324, x_6, x_7, x_8, x_9, x_10, x_11, x_301);
if (lean_obj_tag(x_327) == 0)
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_327, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_327, 1);
lean_inc(x_329);
lean_dec(x_327);
lean_inc(x_325);
x_330 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_325, x_6, x_7, x_8, x_9, x_10, x_11, x_329);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_330, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_333 = x_330;
} else {
 lean_dec_ref(x_330);
 x_333 = lean_box(0);
}
x_334 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_334, 0, x_324);
lean_ctor_set(x_334, 1, x_325);
lean_ctor_set_uint64(x_334, sizeof(void*)*2, x_326);
x_335 = lean_expr_update_app(x_334, x_328, x_331);
if (lean_is_scalar(x_333)) {
 x_336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_336 = x_333;
}
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_332);
return x_336;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
lean_dec(x_328);
lean_dec(x_325);
lean_dec(x_324);
x_337 = lean_ctor_get(x_330, 0);
lean_inc(x_337);
x_338 = lean_ctor_get(x_330, 1);
lean_inc(x_338);
if (lean_is_exclusive(x_330)) {
 lean_ctor_release(x_330, 0);
 lean_ctor_release(x_330, 1);
 x_339 = x_330;
} else {
 lean_dec_ref(x_330);
 x_339 = lean_box(0);
}
if (lean_is_scalar(x_339)) {
 x_340 = lean_alloc_ctor(1, 2, 0);
} else {
 x_340 = x_339;
}
lean_ctor_set(x_340, 0, x_337);
lean_ctor_set(x_340, 1, x_338);
return x_340;
}
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_341 = lean_ctor_get(x_327, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_327, 1);
lean_inc(x_342);
if (lean_is_exclusive(x_327)) {
 lean_ctor_release(x_327, 0);
 lean_ctor_release(x_327, 1);
 x_343 = x_327;
} else {
 lean_dec_ref(x_327);
 x_343 = lean_box(0);
}
if (lean_is_scalar(x_343)) {
 x_344 = lean_alloc_ctor(1, 2, 0);
} else {
 x_344 = x_343;
}
lean_ctor_set(x_344, 0, x_341);
lean_ctor_set(x_344, 1, x_342);
return x_344;
}
}
}
case 6:
{
lean_object* x_345; uint8_t x_346; 
x_345 = lean_ctor_get(x_298, 1);
lean_inc(x_345);
lean_dec(x_298);
x_346 = !lean_is_exclusive(x_5);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; uint64_t x_350; lean_object* x_351; 
x_347 = lean_ctor_get(x_5, 0);
x_348 = lean_ctor_get(x_5, 1);
x_349 = lean_ctor_get(x_5, 2);
x_350 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_348);
lean_inc(x_1);
x_351 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_348, x_6, x_7, x_8, x_9, x_10, x_11, x_345);
if (lean_obj_tag(x_351) == 0)
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
x_352 = lean_ctor_get(x_351, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_351, 1);
lean_inc(x_353);
lean_dec(x_351);
x_354 = lean_unsigned_to_nat(1u);
x_355 = lean_nat_add(x_6, x_354);
lean_dec(x_6);
lean_inc(x_349);
x_356 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_349, x_355, x_7, x_8, x_9, x_10, x_11, x_353);
if (lean_obj_tag(x_356) == 0)
{
uint8_t x_357; 
x_357 = !lean_is_exclusive(x_356);
if (x_357 == 0)
{
lean_object* x_358; uint8_t x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_356, 0);
x_359 = (uint8_t)((x_350 << 24) >> 61);
x_360 = lean_expr_update_lambda(x_5, x_359, x_352, x_358);
lean_ctor_set(x_356, 0, x_360);
return x_356;
}
else
{
lean_object* x_361; lean_object* x_362; uint8_t x_363; lean_object* x_364; lean_object* x_365; 
x_361 = lean_ctor_get(x_356, 0);
x_362 = lean_ctor_get(x_356, 1);
lean_inc(x_362);
lean_inc(x_361);
lean_dec(x_356);
x_363 = (uint8_t)((x_350 << 24) >> 61);
x_364 = lean_expr_update_lambda(x_5, x_363, x_352, x_361);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_362);
return x_365;
}
}
else
{
uint8_t x_366; 
lean_dec(x_352);
lean_free_object(x_5);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
x_366 = !lean_is_exclusive(x_356);
if (x_366 == 0)
{
return x_356;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_367 = lean_ctor_get(x_356, 0);
x_368 = lean_ctor_get(x_356, 1);
lean_inc(x_368);
lean_inc(x_367);
lean_dec(x_356);
x_369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
return x_369;
}
}
}
else
{
uint8_t x_370; 
lean_free_object(x_5);
lean_dec(x_349);
lean_dec(x_348);
lean_dec(x_347);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_370 = !lean_is_exclusive(x_351);
if (x_370 == 0)
{
return x_351;
}
else
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; 
x_371 = lean_ctor_get(x_351, 0);
x_372 = lean_ctor_get(x_351, 1);
lean_inc(x_372);
lean_inc(x_371);
lean_dec(x_351);
x_373 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_373, 0, x_371);
lean_ctor_set(x_373, 1, x_372);
return x_373;
}
}
}
else
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; uint64_t x_377; lean_object* x_378; 
x_374 = lean_ctor_get(x_5, 0);
x_375 = lean_ctor_get(x_5, 1);
x_376 = lean_ctor_get(x_5, 2);
x_377 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_376);
lean_inc(x_375);
lean_inc(x_374);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_375);
lean_inc(x_1);
x_378 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_375, x_6, x_7, x_8, x_9, x_10, x_11, x_345);
if (lean_obj_tag(x_378) == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_379 = lean_ctor_get(x_378, 0);
lean_inc(x_379);
x_380 = lean_ctor_get(x_378, 1);
lean_inc(x_380);
lean_dec(x_378);
x_381 = lean_unsigned_to_nat(1u);
x_382 = lean_nat_add(x_6, x_381);
lean_dec(x_6);
lean_inc(x_376);
x_383 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_376, x_382, x_7, x_8, x_9, x_10, x_11, x_380);
if (lean_obj_tag(x_383) == 0)
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; lean_object* x_389; lean_object* x_390; 
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_386 = x_383;
} else {
 lean_dec_ref(x_383);
 x_386 = lean_box(0);
}
x_387 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_387, 0, x_374);
lean_ctor_set(x_387, 1, x_375);
lean_ctor_set(x_387, 2, x_376);
lean_ctor_set_uint64(x_387, sizeof(void*)*3, x_377);
x_388 = (uint8_t)((x_377 << 24) >> 61);
x_389 = lean_expr_update_lambda(x_387, x_388, x_379, x_384);
if (lean_is_scalar(x_386)) {
 x_390 = lean_alloc_ctor(0, 2, 0);
} else {
 x_390 = x_386;
}
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_385);
return x_390;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; 
lean_dec(x_379);
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_374);
x_391 = lean_ctor_get(x_383, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_383, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_383)) {
 lean_ctor_release(x_383, 0);
 lean_ctor_release(x_383, 1);
 x_393 = x_383;
} else {
 lean_dec_ref(x_383);
 x_393 = lean_box(0);
}
if (lean_is_scalar(x_393)) {
 x_394 = lean_alloc_ctor(1, 2, 0);
} else {
 x_394 = x_393;
}
lean_ctor_set(x_394, 0, x_391);
lean_ctor_set(x_394, 1, x_392);
return x_394;
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_376);
lean_dec(x_375);
lean_dec(x_374);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_395 = lean_ctor_get(x_378, 0);
lean_inc(x_395);
x_396 = lean_ctor_get(x_378, 1);
lean_inc(x_396);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_397 = x_378;
} else {
 lean_dec_ref(x_378);
 x_397 = lean_box(0);
}
if (lean_is_scalar(x_397)) {
 x_398 = lean_alloc_ctor(1, 2, 0);
} else {
 x_398 = x_397;
}
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_396);
return x_398;
}
}
}
case 7:
{
lean_object* x_399; uint8_t x_400; 
x_399 = lean_ctor_get(x_298, 1);
lean_inc(x_399);
lean_dec(x_298);
x_400 = !lean_is_exclusive(x_5);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; uint64_t x_404; lean_object* x_405; 
x_401 = lean_ctor_get(x_5, 0);
x_402 = lean_ctor_get(x_5, 1);
x_403 = lean_ctor_get(x_5, 2);
x_404 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_402);
lean_inc(x_1);
x_405 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_402, x_6, x_7, x_8, x_9, x_10, x_11, x_399);
if (lean_obj_tag(x_405) == 0)
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_406 = lean_ctor_get(x_405, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_405, 1);
lean_inc(x_407);
lean_dec(x_405);
x_408 = lean_unsigned_to_nat(1u);
x_409 = lean_nat_add(x_6, x_408);
lean_dec(x_6);
lean_inc(x_403);
x_410 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_403, x_409, x_7, x_8, x_9, x_10, x_11, x_407);
if (lean_obj_tag(x_410) == 0)
{
uint8_t x_411; 
x_411 = !lean_is_exclusive(x_410);
if (x_411 == 0)
{
lean_object* x_412; uint8_t x_413; lean_object* x_414; 
x_412 = lean_ctor_get(x_410, 0);
x_413 = (uint8_t)((x_404 << 24) >> 61);
x_414 = lean_expr_update_forall(x_5, x_413, x_406, x_412);
lean_ctor_set(x_410, 0, x_414);
return x_410;
}
else
{
lean_object* x_415; lean_object* x_416; uint8_t x_417; lean_object* x_418; lean_object* x_419; 
x_415 = lean_ctor_get(x_410, 0);
x_416 = lean_ctor_get(x_410, 1);
lean_inc(x_416);
lean_inc(x_415);
lean_dec(x_410);
x_417 = (uint8_t)((x_404 << 24) >> 61);
x_418 = lean_expr_update_forall(x_5, x_417, x_406, x_415);
x_419 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_416);
return x_419;
}
}
else
{
uint8_t x_420; 
lean_dec(x_406);
lean_free_object(x_5);
lean_dec(x_403);
lean_dec(x_402);
lean_dec(x_401);
x_420 = !lean_is_exclusive(x_410);
if (x_420 == 0)
{
return x_410;
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
x_421 = lean_ctor_get(x_410, 0);
x_422 = lean_ctor_get(x_410, 1);
lean_inc(x_422);
lean_inc(x_421);
lean_dec(x_410);
x_423 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_423, 0, x_421);
lean_ctor_set(x_423, 1, x_422);
return x_423;
}
}
}
else
{
uint8_t x_424; 
lean_free_object(x_5);
lean_dec(x_403);
lean_dec(x_402);
lean_dec(x_401);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_424 = !lean_is_exclusive(x_405);
if (x_424 == 0)
{
return x_405;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_ctor_get(x_405, 0);
x_426 = lean_ctor_get(x_405, 1);
lean_inc(x_426);
lean_inc(x_425);
lean_dec(x_405);
x_427 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_427, 0, x_425);
lean_ctor_set(x_427, 1, x_426);
return x_427;
}
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; uint64_t x_431; lean_object* x_432; 
x_428 = lean_ctor_get(x_5, 0);
x_429 = lean_ctor_get(x_5, 1);
x_430 = lean_ctor_get(x_5, 2);
x_431 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_430);
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_429);
lean_inc(x_1);
x_432 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_429, x_6, x_7, x_8, x_9, x_10, x_11, x_399);
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_433 = lean_ctor_get(x_432, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_432, 1);
lean_inc(x_434);
lean_dec(x_432);
x_435 = lean_unsigned_to_nat(1u);
x_436 = lean_nat_add(x_6, x_435);
lean_dec(x_6);
lean_inc(x_430);
x_437 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_430, x_436, x_7, x_8, x_9, x_10, x_11, x_434);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; lean_object* x_444; 
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_437, 1);
lean_inc(x_439);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_440 = x_437;
} else {
 lean_dec_ref(x_437);
 x_440 = lean_box(0);
}
x_441 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_441, 0, x_428);
lean_ctor_set(x_441, 1, x_429);
lean_ctor_set(x_441, 2, x_430);
lean_ctor_set_uint64(x_441, sizeof(void*)*3, x_431);
x_442 = (uint8_t)((x_431 << 24) >> 61);
x_443 = lean_expr_update_forall(x_441, x_442, x_433, x_438);
if (lean_is_scalar(x_440)) {
 x_444 = lean_alloc_ctor(0, 2, 0);
} else {
 x_444 = x_440;
}
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_439);
return x_444;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_433);
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_428);
x_445 = lean_ctor_get(x_437, 0);
lean_inc(x_445);
x_446 = lean_ctor_get(x_437, 1);
lean_inc(x_446);
if (lean_is_exclusive(x_437)) {
 lean_ctor_release(x_437, 0);
 lean_ctor_release(x_437, 1);
 x_447 = x_437;
} else {
 lean_dec_ref(x_437);
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
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; 
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_449 = lean_ctor_get(x_432, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_432, 1);
lean_inc(x_450);
if (lean_is_exclusive(x_432)) {
 lean_ctor_release(x_432, 0);
 lean_ctor_release(x_432, 1);
 x_451 = x_432;
} else {
 lean_dec_ref(x_432);
 x_451 = lean_box(0);
}
if (lean_is_scalar(x_451)) {
 x_452 = lean_alloc_ctor(1, 2, 0);
} else {
 x_452 = x_451;
}
lean_ctor_set(x_452, 0, x_449);
lean_ctor_set(x_452, 1, x_450);
return x_452;
}
}
}
case 8:
{
lean_object* x_453; uint8_t x_454; 
x_453 = lean_ctor_get(x_298, 1);
lean_inc(x_453);
lean_dec(x_298);
x_454 = !lean_is_exclusive(x_5);
if (x_454 == 0)
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_455 = lean_ctor_get(x_5, 0);
x_456 = lean_ctor_get(x_5, 1);
x_457 = lean_ctor_get(x_5, 2);
x_458 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_456);
lean_inc(x_1);
x_459 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_456, x_6, x_7, x_8, x_9, x_10, x_11, x_453);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; 
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_459, 1);
lean_inc(x_461);
lean_dec(x_459);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_457);
lean_inc(x_1);
x_462 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_457, x_6, x_7, x_8, x_9, x_10, x_11, x_461);
if (lean_obj_tag(x_462) == 0)
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_463 = lean_ctor_get(x_462, 0);
lean_inc(x_463);
x_464 = lean_ctor_get(x_462, 1);
lean_inc(x_464);
lean_dec(x_462);
x_465 = lean_unsigned_to_nat(1u);
x_466 = lean_nat_add(x_6, x_465);
lean_dec(x_6);
lean_inc(x_458);
x_467 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_458, x_466, x_7, x_8, x_9, x_10, x_11, x_464);
if (lean_obj_tag(x_467) == 0)
{
uint8_t x_468; 
x_468 = !lean_is_exclusive(x_467);
if (x_468 == 0)
{
lean_object* x_469; lean_object* x_470; 
x_469 = lean_ctor_get(x_467, 0);
x_470 = lean_expr_update_let(x_5, x_460, x_463, x_469);
lean_ctor_set(x_467, 0, x_470);
return x_467;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_471 = lean_ctor_get(x_467, 0);
x_472 = lean_ctor_get(x_467, 1);
lean_inc(x_472);
lean_inc(x_471);
lean_dec(x_467);
x_473 = lean_expr_update_let(x_5, x_460, x_463, x_471);
x_474 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_474, 0, x_473);
lean_ctor_set(x_474, 1, x_472);
return x_474;
}
}
else
{
uint8_t x_475; 
lean_dec(x_463);
lean_dec(x_460);
lean_free_object(x_5);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_455);
x_475 = !lean_is_exclusive(x_467);
if (x_475 == 0)
{
return x_467;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_467, 0);
x_477 = lean_ctor_get(x_467, 1);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_467);
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
lean_dec(x_460);
lean_free_object(x_5);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_479 = !lean_is_exclusive(x_462);
if (x_479 == 0)
{
return x_462;
}
else
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_480 = lean_ctor_get(x_462, 0);
x_481 = lean_ctor_get(x_462, 1);
lean_inc(x_481);
lean_inc(x_480);
lean_dec(x_462);
x_482 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_482, 0, x_480);
lean_ctor_set(x_482, 1, x_481);
return x_482;
}
}
}
else
{
uint8_t x_483; 
lean_free_object(x_5);
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_456);
lean_dec(x_455);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_483 = !lean_is_exclusive(x_459);
if (x_483 == 0)
{
return x_459;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_484 = lean_ctor_get(x_459, 0);
x_485 = lean_ctor_get(x_459, 1);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_459);
x_486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_486, 0, x_484);
lean_ctor_set(x_486, 1, x_485);
return x_486;
}
}
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; uint64_t x_491; lean_object* x_492; 
x_487 = lean_ctor_get(x_5, 0);
x_488 = lean_ctor_get(x_5, 1);
x_489 = lean_ctor_get(x_5, 2);
x_490 = lean_ctor_get(x_5, 3);
x_491 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
lean_inc(x_490);
lean_inc(x_489);
lean_inc(x_488);
lean_inc(x_487);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_488);
lean_inc(x_1);
x_492 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_488, x_6, x_7, x_8, x_9, x_10, x_11, x_453);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_492, 1);
lean_inc(x_494);
lean_dec(x_492);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_489);
lean_inc(x_1);
x_495 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_489, x_6, x_7, x_8, x_9, x_10, x_11, x_494);
if (lean_obj_tag(x_495) == 0)
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
lean_dec(x_495);
x_498 = lean_unsigned_to_nat(1u);
x_499 = lean_nat_add(x_6, x_498);
lean_dec(x_6);
lean_inc(x_490);
x_500 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_490, x_499, x_7, x_8, x_9, x_10, x_11, x_497);
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_501 = lean_ctor_get(x_500, 0);
lean_inc(x_501);
x_502 = lean_ctor_get(x_500, 1);
lean_inc(x_502);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 x_503 = x_500;
} else {
 lean_dec_ref(x_500);
 x_503 = lean_box(0);
}
x_504 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_504, 0, x_487);
lean_ctor_set(x_504, 1, x_488);
lean_ctor_set(x_504, 2, x_489);
lean_ctor_set(x_504, 3, x_490);
lean_ctor_set_uint64(x_504, sizeof(void*)*4, x_491);
x_505 = lean_expr_update_let(x_504, x_493, x_496, x_501);
if (lean_is_scalar(x_503)) {
 x_506 = lean_alloc_ctor(0, 2, 0);
} else {
 x_506 = x_503;
}
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_502);
return x_506;
}
else
{
lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_dec(x_496);
lean_dec(x_493);
lean_dec(x_490);
lean_dec(x_489);
lean_dec(x_488);
lean_dec(x_487);
x_507 = lean_ctor_get(x_500, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_500, 1);
lean_inc(x_508);
if (lean_is_exclusive(x_500)) {
 lean_ctor_release(x_500, 0);
 lean_ctor_release(x_500, 1);
 x_509 = x_500;
} else {
 lean_dec_ref(x_500);
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
lean_dec(x_493);
lean_dec(x_490);
lean_dec(x_489);
lean_dec(x_488);
lean_dec(x_487);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_511 = lean_ctor_get(x_495, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_495, 1);
lean_inc(x_512);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_513 = x_495;
} else {
 lean_dec_ref(x_495);
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
lean_dec(x_490);
lean_dec(x_489);
lean_dec(x_488);
lean_dec(x_487);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_515 = lean_ctor_get(x_492, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_492, 1);
lean_inc(x_516);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 x_517 = x_492;
} else {
 lean_dec_ref(x_492);
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
}
case 10:
{
lean_object* x_519; uint8_t x_520; 
x_519 = lean_ctor_get(x_298, 1);
lean_inc(x_519);
lean_dec(x_298);
x_520 = !lean_is_exclusive(x_5);
if (x_520 == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_521 = lean_ctor_get(x_5, 0);
x_522 = lean_ctor_get(x_5, 1);
lean_inc(x_522);
x_523 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_522, x_6, x_7, x_8, x_9, x_10, x_11, x_519);
if (lean_obj_tag(x_523) == 0)
{
uint8_t x_524; 
x_524 = !lean_is_exclusive(x_523);
if (x_524 == 0)
{
lean_object* x_525; lean_object* x_526; 
x_525 = lean_ctor_get(x_523, 0);
x_526 = lean_expr_update_mdata(x_5, x_525);
lean_ctor_set(x_523, 0, x_526);
return x_523;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
x_527 = lean_ctor_get(x_523, 0);
x_528 = lean_ctor_get(x_523, 1);
lean_inc(x_528);
lean_inc(x_527);
lean_dec(x_523);
x_529 = lean_expr_update_mdata(x_5, x_527);
x_530 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_530, 0, x_529);
lean_ctor_set(x_530, 1, x_528);
return x_530;
}
}
else
{
uint8_t x_531; 
lean_free_object(x_5);
lean_dec(x_522);
lean_dec(x_521);
x_531 = !lean_is_exclusive(x_523);
if (x_531 == 0)
{
return x_523;
}
else
{
lean_object* x_532; lean_object* x_533; lean_object* x_534; 
x_532 = lean_ctor_get(x_523, 0);
x_533 = lean_ctor_get(x_523, 1);
lean_inc(x_533);
lean_inc(x_532);
lean_dec(x_523);
x_534 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_534, 0, x_532);
lean_ctor_set(x_534, 1, x_533);
return x_534;
}
}
}
else
{
lean_object* x_535; lean_object* x_536; uint64_t x_537; lean_object* x_538; 
x_535 = lean_ctor_get(x_5, 0);
x_536 = lean_ctor_get(x_5, 1);
x_537 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_536);
lean_inc(x_535);
lean_dec(x_5);
lean_inc(x_536);
x_538 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_536, x_6, x_7, x_8, x_9, x_10, x_11, x_519);
if (lean_obj_tag(x_538) == 0)
{
lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; 
x_539 = lean_ctor_get(x_538, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_538, 1);
lean_inc(x_540);
if (lean_is_exclusive(x_538)) {
 lean_ctor_release(x_538, 0);
 lean_ctor_release(x_538, 1);
 x_541 = x_538;
} else {
 lean_dec_ref(x_538);
 x_541 = lean_box(0);
}
x_542 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_542, 0, x_535);
lean_ctor_set(x_542, 1, x_536);
lean_ctor_set_uint64(x_542, sizeof(void*)*2, x_537);
x_543 = lean_expr_update_mdata(x_542, x_539);
if (lean_is_scalar(x_541)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_541;
}
lean_ctor_set(x_544, 0, x_543);
lean_ctor_set(x_544, 1, x_540);
return x_544;
}
else
{
lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_dec(x_536);
lean_dec(x_535);
x_545 = lean_ctor_get(x_538, 0);
lean_inc(x_545);
x_546 = lean_ctor_get(x_538, 1);
lean_inc(x_546);
if (lean_is_exclusive(x_538)) {
 lean_ctor_release(x_538, 0);
 lean_ctor_release(x_538, 1);
 x_547 = x_538;
} else {
 lean_dec_ref(x_538);
 x_547 = lean_box(0);
}
if (lean_is_scalar(x_547)) {
 x_548 = lean_alloc_ctor(1, 2, 0);
} else {
 x_548 = x_547;
}
lean_ctor_set(x_548, 0, x_545);
lean_ctor_set(x_548, 1, x_546);
return x_548;
}
}
}
case 11:
{
lean_object* x_549; uint8_t x_550; 
x_549 = lean_ctor_get(x_298, 1);
lean_inc(x_549);
lean_dec(x_298);
x_550 = !lean_is_exclusive(x_5);
if (x_550 == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; 
x_551 = lean_ctor_get(x_5, 0);
x_552 = lean_ctor_get(x_5, 1);
x_553 = lean_ctor_get(x_5, 2);
lean_inc(x_553);
x_554 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_553, x_6, x_7, x_8, x_9, x_10, x_11, x_549);
if (lean_obj_tag(x_554) == 0)
{
uint8_t x_555; 
x_555 = !lean_is_exclusive(x_554);
if (x_555 == 0)
{
lean_object* x_556; lean_object* x_557; 
x_556 = lean_ctor_get(x_554, 0);
x_557 = lean_expr_update_proj(x_5, x_556);
lean_ctor_set(x_554, 0, x_557);
return x_554;
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_558 = lean_ctor_get(x_554, 0);
x_559 = lean_ctor_get(x_554, 1);
lean_inc(x_559);
lean_inc(x_558);
lean_dec(x_554);
x_560 = lean_expr_update_proj(x_5, x_558);
x_561 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_561, 0, x_560);
lean_ctor_set(x_561, 1, x_559);
return x_561;
}
}
else
{
uint8_t x_562; 
lean_free_object(x_5);
lean_dec(x_553);
lean_dec(x_552);
lean_dec(x_551);
x_562 = !lean_is_exclusive(x_554);
if (x_562 == 0)
{
return x_554;
}
else
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_563 = lean_ctor_get(x_554, 0);
x_564 = lean_ctor_get(x_554, 1);
lean_inc(x_564);
lean_inc(x_563);
lean_dec(x_554);
x_565 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_565, 0, x_563);
lean_ctor_set(x_565, 1, x_564);
return x_565;
}
}
}
else
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; uint64_t x_569; lean_object* x_570; 
x_566 = lean_ctor_get(x_5, 0);
x_567 = lean_ctor_get(x_5, 1);
x_568 = lean_ctor_get(x_5, 2);
x_569 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_568);
lean_inc(x_567);
lean_inc(x_566);
lean_dec(x_5);
lean_inc(x_568);
x_570 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_568, x_6, x_7, x_8, x_9, x_10, x_11, x_549);
if (lean_obj_tag(x_570) == 0)
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
x_571 = lean_ctor_get(x_570, 0);
lean_inc(x_571);
x_572 = lean_ctor_get(x_570, 1);
lean_inc(x_572);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 lean_ctor_release(x_570, 1);
 x_573 = x_570;
} else {
 lean_dec_ref(x_570);
 x_573 = lean_box(0);
}
x_574 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_574, 0, x_566);
lean_ctor_set(x_574, 1, x_567);
lean_ctor_set(x_574, 2, x_568);
lean_ctor_set_uint64(x_574, sizeof(void*)*3, x_569);
x_575 = lean_expr_update_proj(x_574, x_571);
if (lean_is_scalar(x_573)) {
 x_576 = lean_alloc_ctor(0, 2, 0);
} else {
 x_576 = x_573;
}
lean_ctor_set(x_576, 0, x_575);
lean_ctor_set(x_576, 1, x_572);
return x_576;
}
else
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; 
lean_dec(x_568);
lean_dec(x_567);
lean_dec(x_566);
x_577 = lean_ctor_get(x_570, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_570, 1);
lean_inc(x_578);
if (lean_is_exclusive(x_570)) {
 lean_ctor_release(x_570, 0);
 lean_ctor_release(x_570, 1);
 x_579 = x_570;
} else {
 lean_dec_ref(x_570);
 x_579 = lean_box(0);
}
if (lean_is_scalar(x_579)) {
 x_580 = lean_alloc_ctor(1, 2, 0);
} else {
 x_580 = x_579;
}
lean_ctor_set(x_580, 0, x_577);
lean_ctor_set(x_580, 1, x_578);
return x_580;
}
}
}
default: 
{
uint8_t x_581; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_581 = !lean_is_exclusive(x_298);
if (x_581 == 0)
{
lean_object* x_582; 
x_582 = lean_ctor_get(x_298, 0);
lean_dec(x_582);
lean_ctor_set(x_298, 0, x_5);
return x_298;
}
else
{
lean_object* x_583; lean_object* x_584; 
x_583 = lean_ctor_get(x_298, 1);
lean_inc(x_583);
lean_dec(x_298);
x_584 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_584, 0, x_5);
lean_ctor_set(x_584, 1, x_583);
return x_584;
}
}
}
}
else
{
lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; uint8_t x_596; 
x_585 = lean_ctor_get(x_298, 1);
lean_inc(x_585);
lean_dec(x_298);
x_586 = lean_st_ref_get(x_11, x_585);
x_587 = lean_ctor_get(x_586, 1);
lean_inc(x_587);
lean_dec(x_586);
x_588 = lean_st_ref_get(x_7, x_587);
x_589 = lean_ctor_get(x_588, 0);
lean_inc(x_589);
x_590 = lean_ctor_get(x_588, 1);
lean_inc(x_590);
lean_dec(x_588);
x_591 = lean_unsigned_to_nat(1u);
x_592 = lean_nat_add(x_589, x_591);
x_593 = lean_st_ref_get(x_11, x_590);
x_594 = lean_ctor_get(x_593, 1);
lean_inc(x_594);
lean_dec(x_593);
x_595 = lean_st_ref_set(x_7, x_592, x_594);
x_596 = !lean_is_exclusive(x_595);
if (x_596 == 0)
{
lean_object* x_597; lean_object* x_598; uint8_t x_599; 
x_597 = lean_ctor_get(x_595, 1);
x_598 = lean_ctor_get(x_595, 0);
lean_dec(x_598);
x_599 = l_Lean_Occurrences_contains(x_2, x_589);
lean_dec(x_589);
if (x_599 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
uint8_t x_600; 
lean_free_object(x_595);
x_600 = !lean_is_exclusive(x_5);
if (x_600 == 0)
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_601 = lean_ctor_get(x_5, 0);
x_602 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_601);
lean_inc(x_1);
x_603 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_601, x_6, x_7, x_8, x_9, x_10, x_11, x_597);
if (lean_obj_tag(x_603) == 0)
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; 
x_604 = lean_ctor_get(x_603, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_603, 1);
lean_inc(x_605);
lean_dec(x_603);
lean_inc(x_602);
x_606 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_602, x_6, x_7, x_8, x_9, x_10, x_11, x_605);
if (lean_obj_tag(x_606) == 0)
{
uint8_t x_607; 
x_607 = !lean_is_exclusive(x_606);
if (x_607 == 0)
{
lean_object* x_608; lean_object* x_609; 
x_608 = lean_ctor_get(x_606, 0);
x_609 = lean_expr_update_app(x_5, x_604, x_608);
lean_ctor_set(x_606, 0, x_609);
return x_606;
}
else
{
lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
x_610 = lean_ctor_get(x_606, 0);
x_611 = lean_ctor_get(x_606, 1);
lean_inc(x_611);
lean_inc(x_610);
lean_dec(x_606);
x_612 = lean_expr_update_app(x_5, x_604, x_610);
x_613 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_613, 0, x_612);
lean_ctor_set(x_613, 1, x_611);
return x_613;
}
}
else
{
uint8_t x_614; 
lean_dec(x_604);
lean_free_object(x_5);
lean_dec(x_602);
lean_dec(x_601);
x_614 = !lean_is_exclusive(x_606);
if (x_614 == 0)
{
return x_606;
}
else
{
lean_object* x_615; lean_object* x_616; lean_object* x_617; 
x_615 = lean_ctor_get(x_606, 0);
x_616 = lean_ctor_get(x_606, 1);
lean_inc(x_616);
lean_inc(x_615);
lean_dec(x_606);
x_617 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_617, 0, x_615);
lean_ctor_set(x_617, 1, x_616);
return x_617;
}
}
}
else
{
uint8_t x_618; 
lean_free_object(x_5);
lean_dec(x_602);
lean_dec(x_601);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_618 = !lean_is_exclusive(x_603);
if (x_618 == 0)
{
return x_603;
}
else
{
lean_object* x_619; lean_object* x_620; lean_object* x_621; 
x_619 = lean_ctor_get(x_603, 0);
x_620 = lean_ctor_get(x_603, 1);
lean_inc(x_620);
lean_inc(x_619);
lean_dec(x_603);
x_621 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_621, 0, x_619);
lean_ctor_set(x_621, 1, x_620);
return x_621;
}
}
}
else
{
lean_object* x_622; lean_object* x_623; uint64_t x_624; lean_object* x_625; 
x_622 = lean_ctor_get(x_5, 0);
x_623 = lean_ctor_get(x_5, 1);
x_624 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_623);
lean_inc(x_622);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_622);
lean_inc(x_1);
x_625 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_622, x_6, x_7, x_8, x_9, x_10, x_11, x_597);
if (lean_obj_tag(x_625) == 0)
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; 
x_626 = lean_ctor_get(x_625, 0);
lean_inc(x_626);
x_627 = lean_ctor_get(x_625, 1);
lean_inc(x_627);
lean_dec(x_625);
lean_inc(x_623);
x_628 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_623, x_6, x_7, x_8, x_9, x_10, x_11, x_627);
if (lean_obj_tag(x_628) == 0)
{
lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
x_629 = lean_ctor_get(x_628, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_628, 1);
lean_inc(x_630);
if (lean_is_exclusive(x_628)) {
 lean_ctor_release(x_628, 0);
 lean_ctor_release(x_628, 1);
 x_631 = x_628;
} else {
 lean_dec_ref(x_628);
 x_631 = lean_box(0);
}
x_632 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_632, 0, x_622);
lean_ctor_set(x_632, 1, x_623);
lean_ctor_set_uint64(x_632, sizeof(void*)*2, x_624);
x_633 = lean_expr_update_app(x_632, x_626, x_629);
if (lean_is_scalar(x_631)) {
 x_634 = lean_alloc_ctor(0, 2, 0);
} else {
 x_634 = x_631;
}
lean_ctor_set(x_634, 0, x_633);
lean_ctor_set(x_634, 1, x_630);
return x_634;
}
else
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; 
lean_dec(x_626);
lean_dec(x_623);
lean_dec(x_622);
x_635 = lean_ctor_get(x_628, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_628, 1);
lean_inc(x_636);
if (lean_is_exclusive(x_628)) {
 lean_ctor_release(x_628, 0);
 lean_ctor_release(x_628, 1);
 x_637 = x_628;
} else {
 lean_dec_ref(x_628);
 x_637 = lean_box(0);
}
if (lean_is_scalar(x_637)) {
 x_638 = lean_alloc_ctor(1, 2, 0);
} else {
 x_638 = x_637;
}
lean_ctor_set(x_638, 0, x_635);
lean_ctor_set(x_638, 1, x_636);
return x_638;
}
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; 
lean_dec(x_623);
lean_dec(x_622);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_639 = lean_ctor_get(x_625, 0);
lean_inc(x_639);
x_640 = lean_ctor_get(x_625, 1);
lean_inc(x_640);
if (lean_is_exclusive(x_625)) {
 lean_ctor_release(x_625, 0);
 lean_ctor_release(x_625, 1);
 x_641 = x_625;
} else {
 lean_dec_ref(x_625);
 x_641 = lean_box(0);
}
if (lean_is_scalar(x_641)) {
 x_642 = lean_alloc_ctor(1, 2, 0);
} else {
 x_642 = x_641;
}
lean_ctor_set(x_642, 0, x_639);
lean_ctor_set(x_642, 1, x_640);
return x_642;
}
}
}
case 6:
{
uint8_t x_643; 
lean_free_object(x_595);
x_643 = !lean_is_exclusive(x_5);
if (x_643 == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; uint64_t x_647; lean_object* x_648; 
x_644 = lean_ctor_get(x_5, 0);
x_645 = lean_ctor_get(x_5, 1);
x_646 = lean_ctor_get(x_5, 2);
x_647 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_645);
lean_inc(x_1);
x_648 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_645, x_6, x_7, x_8, x_9, x_10, x_11, x_597);
if (lean_obj_tag(x_648) == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; 
x_649 = lean_ctor_get(x_648, 0);
lean_inc(x_649);
x_650 = lean_ctor_get(x_648, 1);
lean_inc(x_650);
lean_dec(x_648);
x_651 = lean_nat_add(x_6, x_591);
lean_dec(x_6);
lean_inc(x_646);
x_652 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_646, x_651, x_7, x_8, x_9, x_10, x_11, x_650);
if (lean_obj_tag(x_652) == 0)
{
uint8_t x_653; 
x_653 = !lean_is_exclusive(x_652);
if (x_653 == 0)
{
lean_object* x_654; uint8_t x_655; lean_object* x_656; 
x_654 = lean_ctor_get(x_652, 0);
x_655 = (uint8_t)((x_647 << 24) >> 61);
x_656 = lean_expr_update_lambda(x_5, x_655, x_649, x_654);
lean_ctor_set(x_652, 0, x_656);
return x_652;
}
else
{
lean_object* x_657; lean_object* x_658; uint8_t x_659; lean_object* x_660; lean_object* x_661; 
x_657 = lean_ctor_get(x_652, 0);
x_658 = lean_ctor_get(x_652, 1);
lean_inc(x_658);
lean_inc(x_657);
lean_dec(x_652);
x_659 = (uint8_t)((x_647 << 24) >> 61);
x_660 = lean_expr_update_lambda(x_5, x_659, x_649, x_657);
x_661 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_661, 0, x_660);
lean_ctor_set(x_661, 1, x_658);
return x_661;
}
}
else
{
uint8_t x_662; 
lean_dec(x_649);
lean_free_object(x_5);
lean_dec(x_646);
lean_dec(x_645);
lean_dec(x_644);
x_662 = !lean_is_exclusive(x_652);
if (x_662 == 0)
{
return x_652;
}
else
{
lean_object* x_663; lean_object* x_664; lean_object* x_665; 
x_663 = lean_ctor_get(x_652, 0);
x_664 = lean_ctor_get(x_652, 1);
lean_inc(x_664);
lean_inc(x_663);
lean_dec(x_652);
x_665 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_665, 0, x_663);
lean_ctor_set(x_665, 1, x_664);
return x_665;
}
}
}
else
{
uint8_t x_666; 
lean_free_object(x_5);
lean_dec(x_646);
lean_dec(x_645);
lean_dec(x_644);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_666 = !lean_is_exclusive(x_648);
if (x_666 == 0)
{
return x_648;
}
else
{
lean_object* x_667; lean_object* x_668; lean_object* x_669; 
x_667 = lean_ctor_get(x_648, 0);
x_668 = lean_ctor_get(x_648, 1);
lean_inc(x_668);
lean_inc(x_667);
lean_dec(x_648);
x_669 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_669, 0, x_667);
lean_ctor_set(x_669, 1, x_668);
return x_669;
}
}
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; uint64_t x_673; lean_object* x_674; 
x_670 = lean_ctor_get(x_5, 0);
x_671 = lean_ctor_get(x_5, 1);
x_672 = lean_ctor_get(x_5, 2);
x_673 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_672);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_671);
lean_inc(x_1);
x_674 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_671, x_6, x_7, x_8, x_9, x_10, x_11, x_597);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; 
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
lean_dec(x_674);
x_677 = lean_nat_add(x_6, x_591);
lean_dec(x_6);
lean_inc(x_672);
x_678 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_672, x_677, x_7, x_8, x_9, x_10, x_11, x_676);
if (lean_obj_tag(x_678) == 0)
{
lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; uint8_t x_683; lean_object* x_684; lean_object* x_685; 
x_679 = lean_ctor_get(x_678, 0);
lean_inc(x_679);
x_680 = lean_ctor_get(x_678, 1);
lean_inc(x_680);
if (lean_is_exclusive(x_678)) {
 lean_ctor_release(x_678, 0);
 lean_ctor_release(x_678, 1);
 x_681 = x_678;
} else {
 lean_dec_ref(x_678);
 x_681 = lean_box(0);
}
x_682 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_682, 0, x_670);
lean_ctor_set(x_682, 1, x_671);
lean_ctor_set(x_682, 2, x_672);
lean_ctor_set_uint64(x_682, sizeof(void*)*3, x_673);
x_683 = (uint8_t)((x_673 << 24) >> 61);
x_684 = lean_expr_update_lambda(x_682, x_683, x_675, x_679);
if (lean_is_scalar(x_681)) {
 x_685 = lean_alloc_ctor(0, 2, 0);
} else {
 x_685 = x_681;
}
lean_ctor_set(x_685, 0, x_684);
lean_ctor_set(x_685, 1, x_680);
return x_685;
}
else
{
lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
lean_dec(x_675);
lean_dec(x_672);
lean_dec(x_671);
lean_dec(x_670);
x_686 = lean_ctor_get(x_678, 0);
lean_inc(x_686);
x_687 = lean_ctor_get(x_678, 1);
lean_inc(x_687);
if (lean_is_exclusive(x_678)) {
 lean_ctor_release(x_678, 0);
 lean_ctor_release(x_678, 1);
 x_688 = x_678;
} else {
 lean_dec_ref(x_678);
 x_688 = lean_box(0);
}
if (lean_is_scalar(x_688)) {
 x_689 = lean_alloc_ctor(1, 2, 0);
} else {
 x_689 = x_688;
}
lean_ctor_set(x_689, 0, x_686);
lean_ctor_set(x_689, 1, x_687);
return x_689;
}
}
else
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
lean_dec(x_672);
lean_dec(x_671);
lean_dec(x_670);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_690 = lean_ctor_get(x_674, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_674, 1);
lean_inc(x_691);
if (lean_is_exclusive(x_674)) {
 lean_ctor_release(x_674, 0);
 lean_ctor_release(x_674, 1);
 x_692 = x_674;
} else {
 lean_dec_ref(x_674);
 x_692 = lean_box(0);
}
if (lean_is_scalar(x_692)) {
 x_693 = lean_alloc_ctor(1, 2, 0);
} else {
 x_693 = x_692;
}
lean_ctor_set(x_693, 0, x_690);
lean_ctor_set(x_693, 1, x_691);
return x_693;
}
}
}
case 7:
{
uint8_t x_694; 
lean_free_object(x_595);
x_694 = !lean_is_exclusive(x_5);
if (x_694 == 0)
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; uint64_t x_698; lean_object* x_699; 
x_695 = lean_ctor_get(x_5, 0);
x_696 = lean_ctor_get(x_5, 1);
x_697 = lean_ctor_get(x_5, 2);
x_698 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_696);
lean_inc(x_1);
x_699 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_696, x_6, x_7, x_8, x_9, x_10, x_11, x_597);
if (lean_obj_tag(x_699) == 0)
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; 
x_700 = lean_ctor_get(x_699, 0);
lean_inc(x_700);
x_701 = lean_ctor_get(x_699, 1);
lean_inc(x_701);
lean_dec(x_699);
x_702 = lean_nat_add(x_6, x_591);
lean_dec(x_6);
lean_inc(x_697);
x_703 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_697, x_702, x_7, x_8, x_9, x_10, x_11, x_701);
if (lean_obj_tag(x_703) == 0)
{
uint8_t x_704; 
x_704 = !lean_is_exclusive(x_703);
if (x_704 == 0)
{
lean_object* x_705; uint8_t x_706; lean_object* x_707; 
x_705 = lean_ctor_get(x_703, 0);
x_706 = (uint8_t)((x_698 << 24) >> 61);
x_707 = lean_expr_update_forall(x_5, x_706, x_700, x_705);
lean_ctor_set(x_703, 0, x_707);
return x_703;
}
else
{
lean_object* x_708; lean_object* x_709; uint8_t x_710; lean_object* x_711; lean_object* x_712; 
x_708 = lean_ctor_get(x_703, 0);
x_709 = lean_ctor_get(x_703, 1);
lean_inc(x_709);
lean_inc(x_708);
lean_dec(x_703);
x_710 = (uint8_t)((x_698 << 24) >> 61);
x_711 = lean_expr_update_forall(x_5, x_710, x_700, x_708);
x_712 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_712, 0, x_711);
lean_ctor_set(x_712, 1, x_709);
return x_712;
}
}
else
{
uint8_t x_713; 
lean_dec(x_700);
lean_free_object(x_5);
lean_dec(x_697);
lean_dec(x_696);
lean_dec(x_695);
x_713 = !lean_is_exclusive(x_703);
if (x_713 == 0)
{
return x_703;
}
else
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; 
x_714 = lean_ctor_get(x_703, 0);
x_715 = lean_ctor_get(x_703, 1);
lean_inc(x_715);
lean_inc(x_714);
lean_dec(x_703);
x_716 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_716, 0, x_714);
lean_ctor_set(x_716, 1, x_715);
return x_716;
}
}
}
else
{
uint8_t x_717; 
lean_free_object(x_5);
lean_dec(x_697);
lean_dec(x_696);
lean_dec(x_695);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_717 = !lean_is_exclusive(x_699);
if (x_717 == 0)
{
return x_699;
}
else
{
lean_object* x_718; lean_object* x_719; lean_object* x_720; 
x_718 = lean_ctor_get(x_699, 0);
x_719 = lean_ctor_get(x_699, 1);
lean_inc(x_719);
lean_inc(x_718);
lean_dec(x_699);
x_720 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_720, 0, x_718);
lean_ctor_set(x_720, 1, x_719);
return x_720;
}
}
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; uint64_t x_724; lean_object* x_725; 
x_721 = lean_ctor_get(x_5, 0);
x_722 = lean_ctor_get(x_5, 1);
x_723 = lean_ctor_get(x_5, 2);
x_724 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_723);
lean_inc(x_722);
lean_inc(x_721);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_722);
lean_inc(x_1);
x_725 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_722, x_6, x_7, x_8, x_9, x_10, x_11, x_597);
if (lean_obj_tag(x_725) == 0)
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; 
x_726 = lean_ctor_get(x_725, 0);
lean_inc(x_726);
x_727 = lean_ctor_get(x_725, 1);
lean_inc(x_727);
lean_dec(x_725);
x_728 = lean_nat_add(x_6, x_591);
lean_dec(x_6);
lean_inc(x_723);
x_729 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_723, x_728, x_7, x_8, x_9, x_10, x_11, x_727);
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; uint8_t x_734; lean_object* x_735; lean_object* x_736; 
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_729, 1);
lean_inc(x_731);
if (lean_is_exclusive(x_729)) {
 lean_ctor_release(x_729, 0);
 lean_ctor_release(x_729, 1);
 x_732 = x_729;
} else {
 lean_dec_ref(x_729);
 x_732 = lean_box(0);
}
x_733 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_733, 0, x_721);
lean_ctor_set(x_733, 1, x_722);
lean_ctor_set(x_733, 2, x_723);
lean_ctor_set_uint64(x_733, sizeof(void*)*3, x_724);
x_734 = (uint8_t)((x_724 << 24) >> 61);
x_735 = lean_expr_update_forall(x_733, x_734, x_726, x_730);
if (lean_is_scalar(x_732)) {
 x_736 = lean_alloc_ctor(0, 2, 0);
} else {
 x_736 = x_732;
}
lean_ctor_set(x_736, 0, x_735);
lean_ctor_set(x_736, 1, x_731);
return x_736;
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; 
lean_dec(x_726);
lean_dec(x_723);
lean_dec(x_722);
lean_dec(x_721);
x_737 = lean_ctor_get(x_729, 0);
lean_inc(x_737);
x_738 = lean_ctor_get(x_729, 1);
lean_inc(x_738);
if (lean_is_exclusive(x_729)) {
 lean_ctor_release(x_729, 0);
 lean_ctor_release(x_729, 1);
 x_739 = x_729;
} else {
 lean_dec_ref(x_729);
 x_739 = lean_box(0);
}
if (lean_is_scalar(x_739)) {
 x_740 = lean_alloc_ctor(1, 2, 0);
} else {
 x_740 = x_739;
}
lean_ctor_set(x_740, 0, x_737);
lean_ctor_set(x_740, 1, x_738);
return x_740;
}
}
else
{
lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; 
lean_dec(x_723);
lean_dec(x_722);
lean_dec(x_721);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_741 = lean_ctor_get(x_725, 0);
lean_inc(x_741);
x_742 = lean_ctor_get(x_725, 1);
lean_inc(x_742);
if (lean_is_exclusive(x_725)) {
 lean_ctor_release(x_725, 0);
 lean_ctor_release(x_725, 1);
 x_743 = x_725;
} else {
 lean_dec_ref(x_725);
 x_743 = lean_box(0);
}
if (lean_is_scalar(x_743)) {
 x_744 = lean_alloc_ctor(1, 2, 0);
} else {
 x_744 = x_743;
}
lean_ctor_set(x_744, 0, x_741);
lean_ctor_set(x_744, 1, x_742);
return x_744;
}
}
}
case 8:
{
uint8_t x_745; 
lean_free_object(x_595);
x_745 = !lean_is_exclusive(x_5);
if (x_745 == 0)
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_746 = lean_ctor_get(x_5, 0);
x_747 = lean_ctor_get(x_5, 1);
x_748 = lean_ctor_get(x_5, 2);
x_749 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_747);
lean_inc(x_1);
x_750 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_747, x_6, x_7, x_8, x_9, x_10, x_11, x_597);
if (lean_obj_tag(x_750) == 0)
{
lean_object* x_751; lean_object* x_752; lean_object* x_753; 
x_751 = lean_ctor_get(x_750, 0);
lean_inc(x_751);
x_752 = lean_ctor_get(x_750, 1);
lean_inc(x_752);
lean_dec(x_750);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_748);
lean_inc(x_1);
x_753 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_748, x_6, x_7, x_8, x_9, x_10, x_11, x_752);
if (lean_obj_tag(x_753) == 0)
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; 
x_754 = lean_ctor_get(x_753, 0);
lean_inc(x_754);
x_755 = lean_ctor_get(x_753, 1);
lean_inc(x_755);
lean_dec(x_753);
x_756 = lean_nat_add(x_6, x_591);
lean_dec(x_6);
lean_inc(x_749);
x_757 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_749, x_756, x_7, x_8, x_9, x_10, x_11, x_755);
if (lean_obj_tag(x_757) == 0)
{
uint8_t x_758; 
x_758 = !lean_is_exclusive(x_757);
if (x_758 == 0)
{
lean_object* x_759; lean_object* x_760; 
x_759 = lean_ctor_get(x_757, 0);
x_760 = lean_expr_update_let(x_5, x_751, x_754, x_759);
lean_ctor_set(x_757, 0, x_760);
return x_757;
}
else
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; 
x_761 = lean_ctor_get(x_757, 0);
x_762 = lean_ctor_get(x_757, 1);
lean_inc(x_762);
lean_inc(x_761);
lean_dec(x_757);
x_763 = lean_expr_update_let(x_5, x_751, x_754, x_761);
x_764 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_764, 0, x_763);
lean_ctor_set(x_764, 1, x_762);
return x_764;
}
}
else
{
uint8_t x_765; 
lean_dec(x_754);
lean_dec(x_751);
lean_free_object(x_5);
lean_dec(x_749);
lean_dec(x_748);
lean_dec(x_747);
lean_dec(x_746);
x_765 = !lean_is_exclusive(x_757);
if (x_765 == 0)
{
return x_757;
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; 
x_766 = lean_ctor_get(x_757, 0);
x_767 = lean_ctor_get(x_757, 1);
lean_inc(x_767);
lean_inc(x_766);
lean_dec(x_757);
x_768 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_768, 0, x_766);
lean_ctor_set(x_768, 1, x_767);
return x_768;
}
}
}
else
{
uint8_t x_769; 
lean_dec(x_751);
lean_free_object(x_5);
lean_dec(x_749);
lean_dec(x_748);
lean_dec(x_747);
lean_dec(x_746);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_769 = !lean_is_exclusive(x_753);
if (x_769 == 0)
{
return x_753;
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; 
x_770 = lean_ctor_get(x_753, 0);
x_771 = lean_ctor_get(x_753, 1);
lean_inc(x_771);
lean_inc(x_770);
lean_dec(x_753);
x_772 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_772, 0, x_770);
lean_ctor_set(x_772, 1, x_771);
return x_772;
}
}
}
else
{
uint8_t x_773; 
lean_free_object(x_5);
lean_dec(x_749);
lean_dec(x_748);
lean_dec(x_747);
lean_dec(x_746);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_773 = !lean_is_exclusive(x_750);
if (x_773 == 0)
{
return x_750;
}
else
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; 
x_774 = lean_ctor_get(x_750, 0);
x_775 = lean_ctor_get(x_750, 1);
lean_inc(x_775);
lean_inc(x_774);
lean_dec(x_750);
x_776 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_776, 0, x_774);
lean_ctor_set(x_776, 1, x_775);
return x_776;
}
}
}
else
{
lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; uint64_t x_781; lean_object* x_782; 
x_777 = lean_ctor_get(x_5, 0);
x_778 = lean_ctor_get(x_5, 1);
x_779 = lean_ctor_get(x_5, 2);
x_780 = lean_ctor_get(x_5, 3);
x_781 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
lean_inc(x_780);
lean_inc(x_779);
lean_inc(x_778);
lean_inc(x_777);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_778);
lean_inc(x_1);
x_782 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_778, x_6, x_7, x_8, x_9, x_10, x_11, x_597);
if (lean_obj_tag(x_782) == 0)
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_783 = lean_ctor_get(x_782, 0);
lean_inc(x_783);
x_784 = lean_ctor_get(x_782, 1);
lean_inc(x_784);
lean_dec(x_782);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_779);
lean_inc(x_1);
x_785 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_779, x_6, x_7, x_8, x_9, x_10, x_11, x_784);
if (lean_obj_tag(x_785) == 0)
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; 
x_786 = lean_ctor_get(x_785, 0);
lean_inc(x_786);
x_787 = lean_ctor_get(x_785, 1);
lean_inc(x_787);
lean_dec(x_785);
x_788 = lean_nat_add(x_6, x_591);
lean_dec(x_6);
lean_inc(x_780);
x_789 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_780, x_788, x_7, x_8, x_9, x_10, x_11, x_787);
if (lean_obj_tag(x_789) == 0)
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; 
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
x_793 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_793, 0, x_777);
lean_ctor_set(x_793, 1, x_778);
lean_ctor_set(x_793, 2, x_779);
lean_ctor_set(x_793, 3, x_780);
lean_ctor_set_uint64(x_793, sizeof(void*)*4, x_781);
x_794 = lean_expr_update_let(x_793, x_783, x_786, x_790);
if (lean_is_scalar(x_792)) {
 x_795 = lean_alloc_ctor(0, 2, 0);
} else {
 x_795 = x_792;
}
lean_ctor_set(x_795, 0, x_794);
lean_ctor_set(x_795, 1, x_791);
return x_795;
}
else
{
lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; 
lean_dec(x_786);
lean_dec(x_783);
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_777);
x_796 = lean_ctor_get(x_789, 0);
lean_inc(x_796);
x_797 = lean_ctor_get(x_789, 1);
lean_inc(x_797);
if (lean_is_exclusive(x_789)) {
 lean_ctor_release(x_789, 0);
 lean_ctor_release(x_789, 1);
 x_798 = x_789;
} else {
 lean_dec_ref(x_789);
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
else
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; 
lean_dec(x_783);
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_777);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_800 = lean_ctor_get(x_785, 0);
lean_inc(x_800);
x_801 = lean_ctor_get(x_785, 1);
lean_inc(x_801);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 lean_ctor_release(x_785, 1);
 x_802 = x_785;
} else {
 lean_dec_ref(x_785);
 x_802 = lean_box(0);
}
if (lean_is_scalar(x_802)) {
 x_803 = lean_alloc_ctor(1, 2, 0);
} else {
 x_803 = x_802;
}
lean_ctor_set(x_803, 0, x_800);
lean_ctor_set(x_803, 1, x_801);
return x_803;
}
}
else
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_777);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_804 = lean_ctor_get(x_782, 0);
lean_inc(x_804);
x_805 = lean_ctor_get(x_782, 1);
lean_inc(x_805);
if (lean_is_exclusive(x_782)) {
 lean_ctor_release(x_782, 0);
 lean_ctor_release(x_782, 1);
 x_806 = x_782;
} else {
 lean_dec_ref(x_782);
 x_806 = lean_box(0);
}
if (lean_is_scalar(x_806)) {
 x_807 = lean_alloc_ctor(1, 2, 0);
} else {
 x_807 = x_806;
}
lean_ctor_set(x_807, 0, x_804);
lean_ctor_set(x_807, 1, x_805);
return x_807;
}
}
}
case 10:
{
uint8_t x_808; 
lean_free_object(x_595);
x_808 = !lean_is_exclusive(x_5);
if (x_808 == 0)
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; 
x_809 = lean_ctor_get(x_5, 0);
x_810 = lean_ctor_get(x_5, 1);
lean_inc(x_810);
x_811 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_810, x_6, x_7, x_8, x_9, x_10, x_11, x_597);
if (lean_obj_tag(x_811) == 0)
{
uint8_t x_812; 
x_812 = !lean_is_exclusive(x_811);
if (x_812 == 0)
{
lean_object* x_813; lean_object* x_814; 
x_813 = lean_ctor_get(x_811, 0);
x_814 = lean_expr_update_mdata(x_5, x_813);
lean_ctor_set(x_811, 0, x_814);
return x_811;
}
else
{
lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; 
x_815 = lean_ctor_get(x_811, 0);
x_816 = lean_ctor_get(x_811, 1);
lean_inc(x_816);
lean_inc(x_815);
lean_dec(x_811);
x_817 = lean_expr_update_mdata(x_5, x_815);
x_818 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_818, 0, x_817);
lean_ctor_set(x_818, 1, x_816);
return x_818;
}
}
else
{
uint8_t x_819; 
lean_free_object(x_5);
lean_dec(x_810);
lean_dec(x_809);
x_819 = !lean_is_exclusive(x_811);
if (x_819 == 0)
{
return x_811;
}
else
{
lean_object* x_820; lean_object* x_821; lean_object* x_822; 
x_820 = lean_ctor_get(x_811, 0);
x_821 = lean_ctor_get(x_811, 1);
lean_inc(x_821);
lean_inc(x_820);
lean_dec(x_811);
x_822 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_822, 0, x_820);
lean_ctor_set(x_822, 1, x_821);
return x_822;
}
}
}
else
{
lean_object* x_823; lean_object* x_824; uint64_t x_825; lean_object* x_826; 
x_823 = lean_ctor_get(x_5, 0);
x_824 = lean_ctor_get(x_5, 1);
x_825 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_824);
lean_inc(x_823);
lean_dec(x_5);
lean_inc(x_824);
x_826 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_824, x_6, x_7, x_8, x_9, x_10, x_11, x_597);
if (lean_obj_tag(x_826) == 0)
{
lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; lean_object* x_831; lean_object* x_832; 
x_827 = lean_ctor_get(x_826, 0);
lean_inc(x_827);
x_828 = lean_ctor_get(x_826, 1);
lean_inc(x_828);
if (lean_is_exclusive(x_826)) {
 lean_ctor_release(x_826, 0);
 lean_ctor_release(x_826, 1);
 x_829 = x_826;
} else {
 lean_dec_ref(x_826);
 x_829 = lean_box(0);
}
x_830 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_830, 0, x_823);
lean_ctor_set(x_830, 1, x_824);
lean_ctor_set_uint64(x_830, sizeof(void*)*2, x_825);
x_831 = lean_expr_update_mdata(x_830, x_827);
if (lean_is_scalar(x_829)) {
 x_832 = lean_alloc_ctor(0, 2, 0);
} else {
 x_832 = x_829;
}
lean_ctor_set(x_832, 0, x_831);
lean_ctor_set(x_832, 1, x_828);
return x_832;
}
else
{
lean_object* x_833; lean_object* x_834; lean_object* x_835; lean_object* x_836; 
lean_dec(x_824);
lean_dec(x_823);
x_833 = lean_ctor_get(x_826, 0);
lean_inc(x_833);
x_834 = lean_ctor_get(x_826, 1);
lean_inc(x_834);
if (lean_is_exclusive(x_826)) {
 lean_ctor_release(x_826, 0);
 lean_ctor_release(x_826, 1);
 x_835 = x_826;
} else {
 lean_dec_ref(x_826);
 x_835 = lean_box(0);
}
if (lean_is_scalar(x_835)) {
 x_836 = lean_alloc_ctor(1, 2, 0);
} else {
 x_836 = x_835;
}
lean_ctor_set(x_836, 0, x_833);
lean_ctor_set(x_836, 1, x_834);
return x_836;
}
}
}
case 11:
{
uint8_t x_837; 
lean_free_object(x_595);
x_837 = !lean_is_exclusive(x_5);
if (x_837 == 0)
{
lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; 
x_838 = lean_ctor_get(x_5, 0);
x_839 = lean_ctor_get(x_5, 1);
x_840 = lean_ctor_get(x_5, 2);
lean_inc(x_840);
x_841 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_840, x_6, x_7, x_8, x_9, x_10, x_11, x_597);
if (lean_obj_tag(x_841) == 0)
{
uint8_t x_842; 
x_842 = !lean_is_exclusive(x_841);
if (x_842 == 0)
{
lean_object* x_843; lean_object* x_844; 
x_843 = lean_ctor_get(x_841, 0);
x_844 = lean_expr_update_proj(x_5, x_843);
lean_ctor_set(x_841, 0, x_844);
return x_841;
}
else
{
lean_object* x_845; lean_object* x_846; lean_object* x_847; lean_object* x_848; 
x_845 = lean_ctor_get(x_841, 0);
x_846 = lean_ctor_get(x_841, 1);
lean_inc(x_846);
lean_inc(x_845);
lean_dec(x_841);
x_847 = lean_expr_update_proj(x_5, x_845);
x_848 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_848, 0, x_847);
lean_ctor_set(x_848, 1, x_846);
return x_848;
}
}
else
{
uint8_t x_849; 
lean_free_object(x_5);
lean_dec(x_840);
lean_dec(x_839);
lean_dec(x_838);
x_849 = !lean_is_exclusive(x_841);
if (x_849 == 0)
{
return x_841;
}
else
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; 
x_850 = lean_ctor_get(x_841, 0);
x_851 = lean_ctor_get(x_841, 1);
lean_inc(x_851);
lean_inc(x_850);
lean_dec(x_841);
x_852 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_852, 0, x_850);
lean_ctor_set(x_852, 1, x_851);
return x_852;
}
}
}
else
{
lean_object* x_853; lean_object* x_854; lean_object* x_855; uint64_t x_856; lean_object* x_857; 
x_853 = lean_ctor_get(x_5, 0);
x_854 = lean_ctor_get(x_5, 1);
x_855 = lean_ctor_get(x_5, 2);
x_856 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_855);
lean_inc(x_854);
lean_inc(x_853);
lean_dec(x_5);
lean_inc(x_855);
x_857 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_855, x_6, x_7, x_8, x_9, x_10, x_11, x_597);
if (lean_obj_tag(x_857) == 0)
{
lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; 
x_858 = lean_ctor_get(x_857, 0);
lean_inc(x_858);
x_859 = lean_ctor_get(x_857, 1);
lean_inc(x_859);
if (lean_is_exclusive(x_857)) {
 lean_ctor_release(x_857, 0);
 lean_ctor_release(x_857, 1);
 x_860 = x_857;
} else {
 lean_dec_ref(x_857);
 x_860 = lean_box(0);
}
x_861 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_861, 0, x_853);
lean_ctor_set(x_861, 1, x_854);
lean_ctor_set(x_861, 2, x_855);
lean_ctor_set_uint64(x_861, sizeof(void*)*3, x_856);
x_862 = lean_expr_update_proj(x_861, x_858);
if (lean_is_scalar(x_860)) {
 x_863 = lean_alloc_ctor(0, 2, 0);
} else {
 x_863 = x_860;
}
lean_ctor_set(x_863, 0, x_862);
lean_ctor_set(x_863, 1, x_859);
return x_863;
}
else
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; 
lean_dec(x_855);
lean_dec(x_854);
lean_dec(x_853);
x_864 = lean_ctor_get(x_857, 0);
lean_inc(x_864);
x_865 = lean_ctor_get(x_857, 1);
lean_inc(x_865);
if (lean_is_exclusive(x_857)) {
 lean_ctor_release(x_857, 0);
 lean_ctor_release(x_857, 1);
 x_866 = x_857;
} else {
 lean_dec_ref(x_857);
 x_866 = lean_box(0);
}
if (lean_is_scalar(x_866)) {
 x_867 = lean_alloc_ctor(1, 2, 0);
} else {
 x_867 = x_866;
}
lean_ctor_set(x_867, 0, x_864);
lean_ctor_set(x_867, 1, x_865);
return x_867;
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
lean_ctor_set(x_595, 0, x_5);
return x_595;
}
}
}
else
{
lean_object* x_868; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_868 = l_Lean_mkBVar(x_6);
lean_ctor_set(x_595, 0, x_868);
return x_595;
}
}
else
{
lean_object* x_869; uint8_t x_870; 
x_869 = lean_ctor_get(x_595, 1);
lean_inc(x_869);
lean_dec(x_595);
x_870 = l_Lean_Occurrences_contains(x_2, x_589);
lean_dec(x_589);
if (x_870 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_871; lean_object* x_872; uint64_t x_873; lean_object* x_874; lean_object* x_875; 
x_871 = lean_ctor_get(x_5, 0);
lean_inc(x_871);
x_872 = lean_ctor_get(x_5, 1);
lean_inc(x_872);
x_873 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_874 = x_5;
} else {
 lean_dec_ref(x_5);
 x_874 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_871);
lean_inc(x_1);
x_875 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_871, x_6, x_7, x_8, x_9, x_10, x_11, x_869);
if (lean_obj_tag(x_875) == 0)
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; 
x_876 = lean_ctor_get(x_875, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_875, 1);
lean_inc(x_877);
lean_dec(x_875);
lean_inc(x_872);
x_878 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_872, x_6, x_7, x_8, x_9, x_10, x_11, x_877);
if (lean_obj_tag(x_878) == 0)
{
lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; 
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
if (lean_is_exclusive(x_878)) {
 lean_ctor_release(x_878, 0);
 lean_ctor_release(x_878, 1);
 x_881 = x_878;
} else {
 lean_dec_ref(x_878);
 x_881 = lean_box(0);
}
if (lean_is_scalar(x_874)) {
 x_882 = lean_alloc_ctor(5, 2, 8);
} else {
 x_882 = x_874;
}
lean_ctor_set(x_882, 0, x_871);
lean_ctor_set(x_882, 1, x_872);
lean_ctor_set_uint64(x_882, sizeof(void*)*2, x_873);
x_883 = lean_expr_update_app(x_882, x_876, x_879);
if (lean_is_scalar(x_881)) {
 x_884 = lean_alloc_ctor(0, 2, 0);
} else {
 x_884 = x_881;
}
lean_ctor_set(x_884, 0, x_883);
lean_ctor_set(x_884, 1, x_880);
return x_884;
}
else
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; 
lean_dec(x_876);
lean_dec(x_874);
lean_dec(x_872);
lean_dec(x_871);
x_885 = lean_ctor_get(x_878, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_878, 1);
lean_inc(x_886);
if (lean_is_exclusive(x_878)) {
 lean_ctor_release(x_878, 0);
 lean_ctor_release(x_878, 1);
 x_887 = x_878;
} else {
 lean_dec_ref(x_878);
 x_887 = lean_box(0);
}
if (lean_is_scalar(x_887)) {
 x_888 = lean_alloc_ctor(1, 2, 0);
} else {
 x_888 = x_887;
}
lean_ctor_set(x_888, 0, x_885);
lean_ctor_set(x_888, 1, x_886);
return x_888;
}
}
else
{
lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; 
lean_dec(x_874);
lean_dec(x_872);
lean_dec(x_871);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_889 = lean_ctor_get(x_875, 0);
lean_inc(x_889);
x_890 = lean_ctor_get(x_875, 1);
lean_inc(x_890);
if (lean_is_exclusive(x_875)) {
 lean_ctor_release(x_875, 0);
 lean_ctor_release(x_875, 1);
 x_891 = x_875;
} else {
 lean_dec_ref(x_875);
 x_891 = lean_box(0);
}
if (lean_is_scalar(x_891)) {
 x_892 = lean_alloc_ctor(1, 2, 0);
} else {
 x_892 = x_891;
}
lean_ctor_set(x_892, 0, x_889);
lean_ctor_set(x_892, 1, x_890);
return x_892;
}
}
case 6:
{
lean_object* x_893; lean_object* x_894; lean_object* x_895; uint64_t x_896; lean_object* x_897; lean_object* x_898; 
x_893 = lean_ctor_get(x_5, 0);
lean_inc(x_893);
x_894 = lean_ctor_get(x_5, 1);
lean_inc(x_894);
x_895 = lean_ctor_get(x_5, 2);
lean_inc(x_895);
x_896 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_897 = x_5;
} else {
 lean_dec_ref(x_5);
 x_897 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_894);
lean_inc(x_1);
x_898 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_894, x_6, x_7, x_8, x_9, x_10, x_11, x_869);
if (lean_obj_tag(x_898) == 0)
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; lean_object* x_902; 
x_899 = lean_ctor_get(x_898, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_898, 1);
lean_inc(x_900);
lean_dec(x_898);
x_901 = lean_nat_add(x_6, x_591);
lean_dec(x_6);
lean_inc(x_895);
x_902 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_895, x_901, x_7, x_8, x_9, x_10, x_11, x_900);
if (lean_obj_tag(x_902) == 0)
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; uint8_t x_907; lean_object* x_908; lean_object* x_909; 
x_903 = lean_ctor_get(x_902, 0);
lean_inc(x_903);
x_904 = lean_ctor_get(x_902, 1);
lean_inc(x_904);
if (lean_is_exclusive(x_902)) {
 lean_ctor_release(x_902, 0);
 lean_ctor_release(x_902, 1);
 x_905 = x_902;
} else {
 lean_dec_ref(x_902);
 x_905 = lean_box(0);
}
if (lean_is_scalar(x_897)) {
 x_906 = lean_alloc_ctor(6, 3, 8);
} else {
 x_906 = x_897;
}
lean_ctor_set(x_906, 0, x_893);
lean_ctor_set(x_906, 1, x_894);
lean_ctor_set(x_906, 2, x_895);
lean_ctor_set_uint64(x_906, sizeof(void*)*3, x_896);
x_907 = (uint8_t)((x_896 << 24) >> 61);
x_908 = lean_expr_update_lambda(x_906, x_907, x_899, x_903);
if (lean_is_scalar(x_905)) {
 x_909 = lean_alloc_ctor(0, 2, 0);
} else {
 x_909 = x_905;
}
lean_ctor_set(x_909, 0, x_908);
lean_ctor_set(x_909, 1, x_904);
return x_909;
}
else
{
lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_913; 
lean_dec(x_899);
lean_dec(x_897);
lean_dec(x_895);
lean_dec(x_894);
lean_dec(x_893);
x_910 = lean_ctor_get(x_902, 0);
lean_inc(x_910);
x_911 = lean_ctor_get(x_902, 1);
lean_inc(x_911);
if (lean_is_exclusive(x_902)) {
 lean_ctor_release(x_902, 0);
 lean_ctor_release(x_902, 1);
 x_912 = x_902;
} else {
 lean_dec_ref(x_902);
 x_912 = lean_box(0);
}
if (lean_is_scalar(x_912)) {
 x_913 = lean_alloc_ctor(1, 2, 0);
} else {
 x_913 = x_912;
}
lean_ctor_set(x_913, 0, x_910);
lean_ctor_set(x_913, 1, x_911);
return x_913;
}
}
else
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; 
lean_dec(x_897);
lean_dec(x_895);
lean_dec(x_894);
lean_dec(x_893);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_914 = lean_ctor_get(x_898, 0);
lean_inc(x_914);
x_915 = lean_ctor_get(x_898, 1);
lean_inc(x_915);
if (lean_is_exclusive(x_898)) {
 lean_ctor_release(x_898, 0);
 lean_ctor_release(x_898, 1);
 x_916 = x_898;
} else {
 lean_dec_ref(x_898);
 x_916 = lean_box(0);
}
if (lean_is_scalar(x_916)) {
 x_917 = lean_alloc_ctor(1, 2, 0);
} else {
 x_917 = x_916;
}
lean_ctor_set(x_917, 0, x_914);
lean_ctor_set(x_917, 1, x_915);
return x_917;
}
}
case 7:
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; uint64_t x_921; lean_object* x_922; lean_object* x_923; 
x_918 = lean_ctor_get(x_5, 0);
lean_inc(x_918);
x_919 = lean_ctor_get(x_5, 1);
lean_inc(x_919);
x_920 = lean_ctor_get(x_5, 2);
lean_inc(x_920);
x_921 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_922 = x_5;
} else {
 lean_dec_ref(x_5);
 x_922 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_919);
lean_inc(x_1);
x_923 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_919, x_6, x_7, x_8, x_9, x_10, x_11, x_869);
if (lean_obj_tag(x_923) == 0)
{
lean_object* x_924; lean_object* x_925; lean_object* x_926; lean_object* x_927; 
x_924 = lean_ctor_get(x_923, 0);
lean_inc(x_924);
x_925 = lean_ctor_get(x_923, 1);
lean_inc(x_925);
lean_dec(x_923);
x_926 = lean_nat_add(x_6, x_591);
lean_dec(x_6);
lean_inc(x_920);
x_927 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_920, x_926, x_7, x_8, x_9, x_10, x_11, x_925);
if (lean_obj_tag(x_927) == 0)
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; uint8_t x_932; lean_object* x_933; lean_object* x_934; 
x_928 = lean_ctor_get(x_927, 0);
lean_inc(x_928);
x_929 = lean_ctor_get(x_927, 1);
lean_inc(x_929);
if (lean_is_exclusive(x_927)) {
 lean_ctor_release(x_927, 0);
 lean_ctor_release(x_927, 1);
 x_930 = x_927;
} else {
 lean_dec_ref(x_927);
 x_930 = lean_box(0);
}
if (lean_is_scalar(x_922)) {
 x_931 = lean_alloc_ctor(7, 3, 8);
} else {
 x_931 = x_922;
}
lean_ctor_set(x_931, 0, x_918);
lean_ctor_set(x_931, 1, x_919);
lean_ctor_set(x_931, 2, x_920);
lean_ctor_set_uint64(x_931, sizeof(void*)*3, x_921);
x_932 = (uint8_t)((x_921 << 24) >> 61);
x_933 = lean_expr_update_forall(x_931, x_932, x_924, x_928);
if (lean_is_scalar(x_930)) {
 x_934 = lean_alloc_ctor(0, 2, 0);
} else {
 x_934 = x_930;
}
lean_ctor_set(x_934, 0, x_933);
lean_ctor_set(x_934, 1, x_929);
return x_934;
}
else
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
lean_dec(x_924);
lean_dec(x_922);
lean_dec(x_920);
lean_dec(x_919);
lean_dec(x_918);
x_935 = lean_ctor_get(x_927, 0);
lean_inc(x_935);
x_936 = lean_ctor_get(x_927, 1);
lean_inc(x_936);
if (lean_is_exclusive(x_927)) {
 lean_ctor_release(x_927, 0);
 lean_ctor_release(x_927, 1);
 x_937 = x_927;
} else {
 lean_dec_ref(x_927);
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
lean_dec(x_922);
lean_dec(x_920);
lean_dec(x_919);
lean_dec(x_918);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_939 = lean_ctor_get(x_923, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_923, 1);
lean_inc(x_940);
if (lean_is_exclusive(x_923)) {
 lean_ctor_release(x_923, 0);
 lean_ctor_release(x_923, 1);
 x_941 = x_923;
} else {
 lean_dec_ref(x_923);
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
case 8:
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; uint64_t x_947; lean_object* x_948; lean_object* x_949; 
x_943 = lean_ctor_get(x_5, 0);
lean_inc(x_943);
x_944 = lean_ctor_get(x_5, 1);
lean_inc(x_944);
x_945 = lean_ctor_get(x_5, 2);
lean_inc(x_945);
x_946 = lean_ctor_get(x_5, 3);
lean_inc(x_946);
x_947 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 lean_ctor_release(x_5, 3);
 x_948 = x_5;
} else {
 lean_dec_ref(x_5);
 x_948 = lean_box(0);
}
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_944);
lean_inc(x_1);
x_949 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_944, x_6, x_7, x_8, x_9, x_10, x_11, x_869);
if (lean_obj_tag(x_949) == 0)
{
lean_object* x_950; lean_object* x_951; lean_object* x_952; 
x_950 = lean_ctor_get(x_949, 0);
lean_inc(x_950);
x_951 = lean_ctor_get(x_949, 1);
lean_inc(x_951);
lean_dec(x_949);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_945);
lean_inc(x_1);
x_952 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_945, x_6, x_7, x_8, x_9, x_10, x_11, x_951);
if (lean_obj_tag(x_952) == 0)
{
lean_object* x_953; lean_object* x_954; lean_object* x_955; lean_object* x_956; 
x_953 = lean_ctor_get(x_952, 0);
lean_inc(x_953);
x_954 = lean_ctor_get(x_952, 1);
lean_inc(x_954);
lean_dec(x_952);
x_955 = lean_nat_add(x_6, x_591);
lean_dec(x_6);
lean_inc(x_946);
x_956 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_946, x_955, x_7, x_8, x_9, x_10, x_11, x_954);
if (lean_obj_tag(x_956) == 0)
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; 
x_957 = lean_ctor_get(x_956, 0);
lean_inc(x_957);
x_958 = lean_ctor_get(x_956, 1);
lean_inc(x_958);
if (lean_is_exclusive(x_956)) {
 lean_ctor_release(x_956, 0);
 lean_ctor_release(x_956, 1);
 x_959 = x_956;
} else {
 lean_dec_ref(x_956);
 x_959 = lean_box(0);
}
if (lean_is_scalar(x_948)) {
 x_960 = lean_alloc_ctor(8, 4, 8);
} else {
 x_960 = x_948;
}
lean_ctor_set(x_960, 0, x_943);
lean_ctor_set(x_960, 1, x_944);
lean_ctor_set(x_960, 2, x_945);
lean_ctor_set(x_960, 3, x_946);
lean_ctor_set_uint64(x_960, sizeof(void*)*4, x_947);
x_961 = lean_expr_update_let(x_960, x_950, x_953, x_957);
if (lean_is_scalar(x_959)) {
 x_962 = lean_alloc_ctor(0, 2, 0);
} else {
 x_962 = x_959;
}
lean_ctor_set(x_962, 0, x_961);
lean_ctor_set(x_962, 1, x_958);
return x_962;
}
else
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; 
lean_dec(x_953);
lean_dec(x_950);
lean_dec(x_948);
lean_dec(x_946);
lean_dec(x_945);
lean_dec(x_944);
lean_dec(x_943);
x_963 = lean_ctor_get(x_956, 0);
lean_inc(x_963);
x_964 = lean_ctor_get(x_956, 1);
lean_inc(x_964);
if (lean_is_exclusive(x_956)) {
 lean_ctor_release(x_956, 0);
 lean_ctor_release(x_956, 1);
 x_965 = x_956;
} else {
 lean_dec_ref(x_956);
 x_965 = lean_box(0);
}
if (lean_is_scalar(x_965)) {
 x_966 = lean_alloc_ctor(1, 2, 0);
} else {
 x_966 = x_965;
}
lean_ctor_set(x_966, 0, x_963);
lean_ctor_set(x_966, 1, x_964);
return x_966;
}
}
else
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; 
lean_dec(x_950);
lean_dec(x_948);
lean_dec(x_946);
lean_dec(x_945);
lean_dec(x_944);
lean_dec(x_943);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_967 = lean_ctor_get(x_952, 0);
lean_inc(x_967);
x_968 = lean_ctor_get(x_952, 1);
lean_inc(x_968);
if (lean_is_exclusive(x_952)) {
 lean_ctor_release(x_952, 0);
 lean_ctor_release(x_952, 1);
 x_969 = x_952;
} else {
 lean_dec_ref(x_952);
 x_969 = lean_box(0);
}
if (lean_is_scalar(x_969)) {
 x_970 = lean_alloc_ctor(1, 2, 0);
} else {
 x_970 = x_969;
}
lean_ctor_set(x_970, 0, x_967);
lean_ctor_set(x_970, 1, x_968);
return x_970;
}
}
else
{
lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; 
lean_dec(x_948);
lean_dec(x_946);
lean_dec(x_945);
lean_dec(x_944);
lean_dec(x_943);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_971 = lean_ctor_get(x_949, 0);
lean_inc(x_971);
x_972 = lean_ctor_get(x_949, 1);
lean_inc(x_972);
if (lean_is_exclusive(x_949)) {
 lean_ctor_release(x_949, 0);
 lean_ctor_release(x_949, 1);
 x_973 = x_949;
} else {
 lean_dec_ref(x_949);
 x_973 = lean_box(0);
}
if (lean_is_scalar(x_973)) {
 x_974 = lean_alloc_ctor(1, 2, 0);
} else {
 x_974 = x_973;
}
lean_ctor_set(x_974, 0, x_971);
lean_ctor_set(x_974, 1, x_972);
return x_974;
}
}
case 10:
{
lean_object* x_975; lean_object* x_976; uint64_t x_977; lean_object* x_978; lean_object* x_979; 
x_975 = lean_ctor_get(x_5, 0);
lean_inc(x_975);
x_976 = lean_ctor_get(x_5, 1);
lean_inc(x_976);
x_977 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_978 = x_5;
} else {
 lean_dec_ref(x_5);
 x_978 = lean_box(0);
}
lean_inc(x_976);
x_979 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_976, x_6, x_7, x_8, x_9, x_10, x_11, x_869);
if (lean_obj_tag(x_979) == 0)
{
lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; 
x_980 = lean_ctor_get(x_979, 0);
lean_inc(x_980);
x_981 = lean_ctor_get(x_979, 1);
lean_inc(x_981);
if (lean_is_exclusive(x_979)) {
 lean_ctor_release(x_979, 0);
 lean_ctor_release(x_979, 1);
 x_982 = x_979;
} else {
 lean_dec_ref(x_979);
 x_982 = lean_box(0);
}
if (lean_is_scalar(x_978)) {
 x_983 = lean_alloc_ctor(10, 2, 8);
} else {
 x_983 = x_978;
}
lean_ctor_set(x_983, 0, x_975);
lean_ctor_set(x_983, 1, x_976);
lean_ctor_set_uint64(x_983, sizeof(void*)*2, x_977);
x_984 = lean_expr_update_mdata(x_983, x_980);
if (lean_is_scalar(x_982)) {
 x_985 = lean_alloc_ctor(0, 2, 0);
} else {
 x_985 = x_982;
}
lean_ctor_set(x_985, 0, x_984);
lean_ctor_set(x_985, 1, x_981);
return x_985;
}
else
{
lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; 
lean_dec(x_978);
lean_dec(x_976);
lean_dec(x_975);
x_986 = lean_ctor_get(x_979, 0);
lean_inc(x_986);
x_987 = lean_ctor_get(x_979, 1);
lean_inc(x_987);
if (lean_is_exclusive(x_979)) {
 lean_ctor_release(x_979, 0);
 lean_ctor_release(x_979, 1);
 x_988 = x_979;
} else {
 lean_dec_ref(x_979);
 x_988 = lean_box(0);
}
if (lean_is_scalar(x_988)) {
 x_989 = lean_alloc_ctor(1, 2, 0);
} else {
 x_989 = x_988;
}
lean_ctor_set(x_989, 0, x_986);
lean_ctor_set(x_989, 1, x_987);
return x_989;
}
}
case 11:
{
lean_object* x_990; lean_object* x_991; lean_object* x_992; uint64_t x_993; lean_object* x_994; lean_object* x_995; 
x_990 = lean_ctor_get(x_5, 0);
lean_inc(x_990);
x_991 = lean_ctor_get(x_5, 1);
lean_inc(x_991);
x_992 = lean_ctor_get(x_5, 2);
lean_inc(x_992);
x_993 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 lean_ctor_release(x_5, 2);
 x_994 = x_5;
} else {
 lean_dec_ref(x_5);
 x_994 = lean_box(0);
}
lean_inc(x_992);
x_995 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_992, x_6, x_7, x_8, x_9, x_10, x_11, x_869);
if (lean_obj_tag(x_995) == 0)
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
x_996 = lean_ctor_get(x_995, 0);
lean_inc(x_996);
x_997 = lean_ctor_get(x_995, 1);
lean_inc(x_997);
if (lean_is_exclusive(x_995)) {
 lean_ctor_release(x_995, 0);
 lean_ctor_release(x_995, 1);
 x_998 = x_995;
} else {
 lean_dec_ref(x_995);
 x_998 = lean_box(0);
}
if (lean_is_scalar(x_994)) {
 x_999 = lean_alloc_ctor(11, 3, 8);
} else {
 x_999 = x_994;
}
lean_ctor_set(x_999, 0, x_990);
lean_ctor_set(x_999, 1, x_991);
lean_ctor_set(x_999, 2, x_992);
lean_ctor_set_uint64(x_999, sizeof(void*)*3, x_993);
x_1000 = lean_expr_update_proj(x_999, x_996);
if (lean_is_scalar(x_998)) {
 x_1001 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1001 = x_998;
}
lean_ctor_set(x_1001, 0, x_1000);
lean_ctor_set(x_1001, 1, x_997);
return x_1001;
}
else
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; 
lean_dec(x_994);
lean_dec(x_992);
lean_dec(x_991);
lean_dec(x_990);
x_1002 = lean_ctor_get(x_995, 0);
lean_inc(x_1002);
x_1003 = lean_ctor_get(x_995, 1);
lean_inc(x_1003);
if (lean_is_exclusive(x_995)) {
 lean_ctor_release(x_995, 0);
 lean_ctor_release(x_995, 1);
 x_1004 = x_995;
} else {
 lean_dec_ref(x_995);
 x_1004 = lean_box(0);
}
if (lean_is_scalar(x_1004)) {
 x_1005 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1005 = x_1004;
}
lean_ctor_set(x_1005, 0, x_1002);
lean_ctor_set(x_1005, 1, x_1003);
return x_1005;
}
}
default: 
{
lean_object* x_1006; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1006 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1006, 0, x_5);
lean_ctor_set(x_1006, 1, x_869);
return x_1006;
}
}
}
else
{
lean_object* x_1007; lean_object* x_1008; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_1007 = l_Lean_mkBVar(x_6);
x_1008 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1008, 0, x_1007);
lean_ctor_set(x_1008, 1, x_869);
return x_1008;
}
}
}
}
else
{
uint8_t x_1009; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1009 = !lean_is_exclusive(x_298);
if (x_1009 == 0)
{
return x_298;
}
else
{
lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
x_1010 = lean_ctor_get(x_298, 0);
x_1011 = lean_ctor_get(x_298, 1);
lean_inc(x_1011);
lean_inc(x_1010);
lean_dec(x_298);
x_1012 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1012, 0, x_1010);
lean_ctor_set(x_1012, 1, x_1011);
return x_1012;
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
uint8_t x_1013; 
x_1013 = !lean_is_exclusive(x_5);
if (x_1013 == 0)
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
x_1014 = lean_ctor_get(x_5, 0);
x_1015 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1014);
lean_inc(x_1);
x_1016 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1014, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1016) == 0)
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; 
x_1017 = lean_ctor_get(x_1016, 0);
lean_inc(x_1017);
x_1018 = lean_ctor_get(x_1016, 1);
lean_inc(x_1018);
lean_dec(x_1016);
lean_inc(x_1015);
x_1019 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1015, x_6, x_7, x_8, x_9, x_10, x_11, x_1018);
if (lean_obj_tag(x_1019) == 0)
{
uint8_t x_1020; 
x_1020 = !lean_is_exclusive(x_1019);
if (x_1020 == 0)
{
lean_object* x_1021; lean_object* x_1022; 
x_1021 = lean_ctor_get(x_1019, 0);
x_1022 = lean_expr_update_app(x_5, x_1017, x_1021);
lean_ctor_set(x_1019, 0, x_1022);
return x_1019;
}
else
{
lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
x_1023 = lean_ctor_get(x_1019, 0);
x_1024 = lean_ctor_get(x_1019, 1);
lean_inc(x_1024);
lean_inc(x_1023);
lean_dec(x_1019);
x_1025 = lean_expr_update_app(x_5, x_1017, x_1023);
x_1026 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1026, 0, x_1025);
lean_ctor_set(x_1026, 1, x_1024);
return x_1026;
}
}
else
{
uint8_t x_1027; 
lean_dec(x_1017);
lean_free_object(x_5);
lean_dec(x_1015);
lean_dec(x_1014);
x_1027 = !lean_is_exclusive(x_1019);
if (x_1027 == 0)
{
return x_1019;
}
else
{
lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; 
x_1028 = lean_ctor_get(x_1019, 0);
x_1029 = lean_ctor_get(x_1019, 1);
lean_inc(x_1029);
lean_inc(x_1028);
lean_dec(x_1019);
x_1030 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1030, 0, x_1028);
lean_ctor_set(x_1030, 1, x_1029);
return x_1030;
}
}
}
else
{
uint8_t x_1031; 
lean_free_object(x_5);
lean_dec(x_1015);
lean_dec(x_1014);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1031 = !lean_is_exclusive(x_1016);
if (x_1031 == 0)
{
return x_1016;
}
else
{
lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; 
x_1032 = lean_ctor_get(x_1016, 0);
x_1033 = lean_ctor_get(x_1016, 1);
lean_inc(x_1033);
lean_inc(x_1032);
lean_dec(x_1016);
x_1034 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1034, 0, x_1032);
lean_ctor_set(x_1034, 1, x_1033);
return x_1034;
}
}
}
else
{
lean_object* x_1035; lean_object* x_1036; uint64_t x_1037; lean_object* x_1038; 
x_1035 = lean_ctor_get(x_5, 0);
x_1036 = lean_ctor_get(x_5, 1);
x_1037 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_1036);
lean_inc(x_1035);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1035);
lean_inc(x_1);
x_1038 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1035, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1038) == 0)
{
lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
x_1039 = lean_ctor_get(x_1038, 0);
lean_inc(x_1039);
x_1040 = lean_ctor_get(x_1038, 1);
lean_inc(x_1040);
lean_dec(x_1038);
lean_inc(x_1036);
x_1041 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1036, x_6, x_7, x_8, x_9, x_10, x_11, x_1040);
if (lean_obj_tag(x_1041) == 0)
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; 
x_1042 = lean_ctor_get(x_1041, 0);
lean_inc(x_1042);
x_1043 = lean_ctor_get(x_1041, 1);
lean_inc(x_1043);
if (lean_is_exclusive(x_1041)) {
 lean_ctor_release(x_1041, 0);
 lean_ctor_release(x_1041, 1);
 x_1044 = x_1041;
} else {
 lean_dec_ref(x_1041);
 x_1044 = lean_box(0);
}
x_1045 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_1045, 0, x_1035);
lean_ctor_set(x_1045, 1, x_1036);
lean_ctor_set_uint64(x_1045, sizeof(void*)*2, x_1037);
x_1046 = lean_expr_update_app(x_1045, x_1039, x_1042);
if (lean_is_scalar(x_1044)) {
 x_1047 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1047 = x_1044;
}
lean_ctor_set(x_1047, 0, x_1046);
lean_ctor_set(x_1047, 1, x_1043);
return x_1047;
}
else
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
lean_dec(x_1039);
lean_dec(x_1036);
lean_dec(x_1035);
x_1048 = lean_ctor_get(x_1041, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_1041, 1);
lean_inc(x_1049);
if (lean_is_exclusive(x_1041)) {
 lean_ctor_release(x_1041, 0);
 lean_ctor_release(x_1041, 1);
 x_1050 = x_1041;
} else {
 lean_dec_ref(x_1041);
 x_1050 = lean_box(0);
}
if (lean_is_scalar(x_1050)) {
 x_1051 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1051 = x_1050;
}
lean_ctor_set(x_1051, 0, x_1048);
lean_ctor_set(x_1051, 1, x_1049);
return x_1051;
}
}
else
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
lean_dec(x_1036);
lean_dec(x_1035);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1052 = lean_ctor_get(x_1038, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_1038, 1);
lean_inc(x_1053);
if (lean_is_exclusive(x_1038)) {
 lean_ctor_release(x_1038, 0);
 lean_ctor_release(x_1038, 1);
 x_1054 = x_1038;
} else {
 lean_dec_ref(x_1038);
 x_1054 = lean_box(0);
}
if (lean_is_scalar(x_1054)) {
 x_1055 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1055 = x_1054;
}
lean_ctor_set(x_1055, 0, x_1052);
lean_ctor_set(x_1055, 1, x_1053);
return x_1055;
}
}
}
case 6:
{
uint8_t x_1056; 
x_1056 = !lean_is_exclusive(x_5);
if (x_1056 == 0)
{
lean_object* x_1057; lean_object* x_1058; lean_object* x_1059; uint64_t x_1060; lean_object* x_1061; 
x_1057 = lean_ctor_get(x_5, 0);
x_1058 = lean_ctor_get(x_5, 1);
x_1059 = lean_ctor_get(x_5, 2);
x_1060 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1058);
lean_inc(x_1);
x_1061 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1058, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1061) == 0)
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; 
x_1062 = lean_ctor_get(x_1061, 0);
lean_inc(x_1062);
x_1063 = lean_ctor_get(x_1061, 1);
lean_inc(x_1063);
lean_dec(x_1061);
x_1064 = lean_unsigned_to_nat(1u);
x_1065 = lean_nat_add(x_6, x_1064);
lean_dec(x_6);
lean_inc(x_1059);
x_1066 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1059, x_1065, x_7, x_8, x_9, x_10, x_11, x_1063);
if (lean_obj_tag(x_1066) == 0)
{
uint8_t x_1067; 
x_1067 = !lean_is_exclusive(x_1066);
if (x_1067 == 0)
{
lean_object* x_1068; uint8_t x_1069; lean_object* x_1070; 
x_1068 = lean_ctor_get(x_1066, 0);
x_1069 = (uint8_t)((x_1060 << 24) >> 61);
x_1070 = lean_expr_update_lambda(x_5, x_1069, x_1062, x_1068);
lean_ctor_set(x_1066, 0, x_1070);
return x_1066;
}
else
{
lean_object* x_1071; lean_object* x_1072; uint8_t x_1073; lean_object* x_1074; lean_object* x_1075; 
x_1071 = lean_ctor_get(x_1066, 0);
x_1072 = lean_ctor_get(x_1066, 1);
lean_inc(x_1072);
lean_inc(x_1071);
lean_dec(x_1066);
x_1073 = (uint8_t)((x_1060 << 24) >> 61);
x_1074 = lean_expr_update_lambda(x_5, x_1073, x_1062, x_1071);
x_1075 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1075, 0, x_1074);
lean_ctor_set(x_1075, 1, x_1072);
return x_1075;
}
}
else
{
uint8_t x_1076; 
lean_dec(x_1062);
lean_free_object(x_5);
lean_dec(x_1059);
lean_dec(x_1058);
lean_dec(x_1057);
x_1076 = !lean_is_exclusive(x_1066);
if (x_1076 == 0)
{
return x_1066;
}
else
{
lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
x_1077 = lean_ctor_get(x_1066, 0);
x_1078 = lean_ctor_get(x_1066, 1);
lean_inc(x_1078);
lean_inc(x_1077);
lean_dec(x_1066);
x_1079 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1079, 0, x_1077);
lean_ctor_set(x_1079, 1, x_1078);
return x_1079;
}
}
}
else
{
uint8_t x_1080; 
lean_free_object(x_5);
lean_dec(x_1059);
lean_dec(x_1058);
lean_dec(x_1057);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1080 = !lean_is_exclusive(x_1061);
if (x_1080 == 0)
{
return x_1061;
}
else
{
lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; 
x_1081 = lean_ctor_get(x_1061, 0);
x_1082 = lean_ctor_get(x_1061, 1);
lean_inc(x_1082);
lean_inc(x_1081);
lean_dec(x_1061);
x_1083 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1083, 0, x_1081);
lean_ctor_set(x_1083, 1, x_1082);
return x_1083;
}
}
}
else
{
lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; uint64_t x_1087; lean_object* x_1088; 
x_1084 = lean_ctor_get(x_5, 0);
x_1085 = lean_ctor_get(x_5, 1);
x_1086 = lean_ctor_get(x_5, 2);
x_1087 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_1086);
lean_inc(x_1085);
lean_inc(x_1084);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1085);
lean_inc(x_1);
x_1088 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1085, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1088) == 0)
{
lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; 
x_1089 = lean_ctor_get(x_1088, 0);
lean_inc(x_1089);
x_1090 = lean_ctor_get(x_1088, 1);
lean_inc(x_1090);
lean_dec(x_1088);
x_1091 = lean_unsigned_to_nat(1u);
x_1092 = lean_nat_add(x_6, x_1091);
lean_dec(x_6);
lean_inc(x_1086);
x_1093 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1086, x_1092, x_7, x_8, x_9, x_10, x_11, x_1090);
if (lean_obj_tag(x_1093) == 0)
{
lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; uint8_t x_1098; lean_object* x_1099; lean_object* x_1100; 
x_1094 = lean_ctor_get(x_1093, 0);
lean_inc(x_1094);
x_1095 = lean_ctor_get(x_1093, 1);
lean_inc(x_1095);
if (lean_is_exclusive(x_1093)) {
 lean_ctor_release(x_1093, 0);
 lean_ctor_release(x_1093, 1);
 x_1096 = x_1093;
} else {
 lean_dec_ref(x_1093);
 x_1096 = lean_box(0);
}
x_1097 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_1097, 0, x_1084);
lean_ctor_set(x_1097, 1, x_1085);
lean_ctor_set(x_1097, 2, x_1086);
lean_ctor_set_uint64(x_1097, sizeof(void*)*3, x_1087);
x_1098 = (uint8_t)((x_1087 << 24) >> 61);
x_1099 = lean_expr_update_lambda(x_1097, x_1098, x_1089, x_1094);
if (lean_is_scalar(x_1096)) {
 x_1100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1100 = x_1096;
}
lean_ctor_set(x_1100, 0, x_1099);
lean_ctor_set(x_1100, 1, x_1095);
return x_1100;
}
else
{
lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; 
lean_dec(x_1089);
lean_dec(x_1086);
lean_dec(x_1085);
lean_dec(x_1084);
x_1101 = lean_ctor_get(x_1093, 0);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1093, 1);
lean_inc(x_1102);
if (lean_is_exclusive(x_1093)) {
 lean_ctor_release(x_1093, 0);
 lean_ctor_release(x_1093, 1);
 x_1103 = x_1093;
} else {
 lean_dec_ref(x_1093);
 x_1103 = lean_box(0);
}
if (lean_is_scalar(x_1103)) {
 x_1104 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1104 = x_1103;
}
lean_ctor_set(x_1104, 0, x_1101);
lean_ctor_set(x_1104, 1, x_1102);
return x_1104;
}
}
else
{
lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; 
lean_dec(x_1086);
lean_dec(x_1085);
lean_dec(x_1084);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1105 = lean_ctor_get(x_1088, 0);
lean_inc(x_1105);
x_1106 = lean_ctor_get(x_1088, 1);
lean_inc(x_1106);
if (lean_is_exclusive(x_1088)) {
 lean_ctor_release(x_1088, 0);
 lean_ctor_release(x_1088, 1);
 x_1107 = x_1088;
} else {
 lean_dec_ref(x_1088);
 x_1107 = lean_box(0);
}
if (lean_is_scalar(x_1107)) {
 x_1108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1108 = x_1107;
}
lean_ctor_set(x_1108, 0, x_1105);
lean_ctor_set(x_1108, 1, x_1106);
return x_1108;
}
}
}
case 7:
{
uint8_t x_1109; 
x_1109 = !lean_is_exclusive(x_5);
if (x_1109 == 0)
{
lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; uint64_t x_1113; lean_object* x_1114; 
x_1110 = lean_ctor_get(x_5, 0);
x_1111 = lean_ctor_get(x_5, 1);
x_1112 = lean_ctor_get(x_5, 2);
x_1113 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1111);
lean_inc(x_1);
x_1114 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1111, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1114) == 0)
{
lean_object* x_1115; lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; 
x_1115 = lean_ctor_get(x_1114, 0);
lean_inc(x_1115);
x_1116 = lean_ctor_get(x_1114, 1);
lean_inc(x_1116);
lean_dec(x_1114);
x_1117 = lean_unsigned_to_nat(1u);
x_1118 = lean_nat_add(x_6, x_1117);
lean_dec(x_6);
lean_inc(x_1112);
x_1119 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1112, x_1118, x_7, x_8, x_9, x_10, x_11, x_1116);
if (lean_obj_tag(x_1119) == 0)
{
uint8_t x_1120; 
x_1120 = !lean_is_exclusive(x_1119);
if (x_1120 == 0)
{
lean_object* x_1121; uint8_t x_1122; lean_object* x_1123; 
x_1121 = lean_ctor_get(x_1119, 0);
x_1122 = (uint8_t)((x_1113 << 24) >> 61);
x_1123 = lean_expr_update_forall(x_5, x_1122, x_1115, x_1121);
lean_ctor_set(x_1119, 0, x_1123);
return x_1119;
}
else
{
lean_object* x_1124; lean_object* x_1125; uint8_t x_1126; lean_object* x_1127; lean_object* x_1128; 
x_1124 = lean_ctor_get(x_1119, 0);
x_1125 = lean_ctor_get(x_1119, 1);
lean_inc(x_1125);
lean_inc(x_1124);
lean_dec(x_1119);
x_1126 = (uint8_t)((x_1113 << 24) >> 61);
x_1127 = lean_expr_update_forall(x_5, x_1126, x_1115, x_1124);
x_1128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1128, 0, x_1127);
lean_ctor_set(x_1128, 1, x_1125);
return x_1128;
}
}
else
{
uint8_t x_1129; 
lean_dec(x_1115);
lean_free_object(x_5);
lean_dec(x_1112);
lean_dec(x_1111);
lean_dec(x_1110);
x_1129 = !lean_is_exclusive(x_1119);
if (x_1129 == 0)
{
return x_1119;
}
else
{
lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; 
x_1130 = lean_ctor_get(x_1119, 0);
x_1131 = lean_ctor_get(x_1119, 1);
lean_inc(x_1131);
lean_inc(x_1130);
lean_dec(x_1119);
x_1132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1132, 0, x_1130);
lean_ctor_set(x_1132, 1, x_1131);
return x_1132;
}
}
}
else
{
uint8_t x_1133; 
lean_free_object(x_5);
lean_dec(x_1112);
lean_dec(x_1111);
lean_dec(x_1110);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1133 = !lean_is_exclusive(x_1114);
if (x_1133 == 0)
{
return x_1114;
}
else
{
lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; 
x_1134 = lean_ctor_get(x_1114, 0);
x_1135 = lean_ctor_get(x_1114, 1);
lean_inc(x_1135);
lean_inc(x_1134);
lean_dec(x_1114);
x_1136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1136, 0, x_1134);
lean_ctor_set(x_1136, 1, x_1135);
return x_1136;
}
}
}
else
{
lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; uint64_t x_1140; lean_object* x_1141; 
x_1137 = lean_ctor_get(x_5, 0);
x_1138 = lean_ctor_get(x_5, 1);
x_1139 = lean_ctor_get(x_5, 2);
x_1140 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_1139);
lean_inc(x_1138);
lean_inc(x_1137);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1138);
lean_inc(x_1);
x_1141 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1138, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1141) == 0)
{
lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; 
x_1142 = lean_ctor_get(x_1141, 0);
lean_inc(x_1142);
x_1143 = lean_ctor_get(x_1141, 1);
lean_inc(x_1143);
lean_dec(x_1141);
x_1144 = lean_unsigned_to_nat(1u);
x_1145 = lean_nat_add(x_6, x_1144);
lean_dec(x_6);
lean_inc(x_1139);
x_1146 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1139, x_1145, x_7, x_8, x_9, x_10, x_11, x_1143);
if (lean_obj_tag(x_1146) == 0)
{
lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; uint8_t x_1151; lean_object* x_1152; lean_object* x_1153; 
x_1147 = lean_ctor_get(x_1146, 0);
lean_inc(x_1147);
x_1148 = lean_ctor_get(x_1146, 1);
lean_inc(x_1148);
if (lean_is_exclusive(x_1146)) {
 lean_ctor_release(x_1146, 0);
 lean_ctor_release(x_1146, 1);
 x_1149 = x_1146;
} else {
 lean_dec_ref(x_1146);
 x_1149 = lean_box(0);
}
x_1150 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_1150, 0, x_1137);
lean_ctor_set(x_1150, 1, x_1138);
lean_ctor_set(x_1150, 2, x_1139);
lean_ctor_set_uint64(x_1150, sizeof(void*)*3, x_1140);
x_1151 = (uint8_t)((x_1140 << 24) >> 61);
x_1152 = lean_expr_update_forall(x_1150, x_1151, x_1142, x_1147);
if (lean_is_scalar(x_1149)) {
 x_1153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1153 = x_1149;
}
lean_ctor_set(x_1153, 0, x_1152);
lean_ctor_set(x_1153, 1, x_1148);
return x_1153;
}
else
{
lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; 
lean_dec(x_1142);
lean_dec(x_1139);
lean_dec(x_1138);
lean_dec(x_1137);
x_1154 = lean_ctor_get(x_1146, 0);
lean_inc(x_1154);
x_1155 = lean_ctor_get(x_1146, 1);
lean_inc(x_1155);
if (lean_is_exclusive(x_1146)) {
 lean_ctor_release(x_1146, 0);
 lean_ctor_release(x_1146, 1);
 x_1156 = x_1146;
} else {
 lean_dec_ref(x_1146);
 x_1156 = lean_box(0);
}
if (lean_is_scalar(x_1156)) {
 x_1157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1157 = x_1156;
}
lean_ctor_set(x_1157, 0, x_1154);
lean_ctor_set(x_1157, 1, x_1155);
return x_1157;
}
}
else
{
lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; 
lean_dec(x_1139);
lean_dec(x_1138);
lean_dec(x_1137);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1158 = lean_ctor_get(x_1141, 0);
lean_inc(x_1158);
x_1159 = lean_ctor_get(x_1141, 1);
lean_inc(x_1159);
if (lean_is_exclusive(x_1141)) {
 lean_ctor_release(x_1141, 0);
 lean_ctor_release(x_1141, 1);
 x_1160 = x_1141;
} else {
 lean_dec_ref(x_1141);
 x_1160 = lean_box(0);
}
if (lean_is_scalar(x_1160)) {
 x_1161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1161 = x_1160;
}
lean_ctor_set(x_1161, 0, x_1158);
lean_ctor_set(x_1161, 1, x_1159);
return x_1161;
}
}
}
case 8:
{
uint8_t x_1162; 
x_1162 = !lean_is_exclusive(x_5);
if (x_1162 == 0)
{
lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; 
x_1163 = lean_ctor_get(x_5, 0);
x_1164 = lean_ctor_get(x_5, 1);
x_1165 = lean_ctor_get(x_5, 2);
x_1166 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1164);
lean_inc(x_1);
x_1167 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1164, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1167) == 0)
{
lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; 
x_1168 = lean_ctor_get(x_1167, 0);
lean_inc(x_1168);
x_1169 = lean_ctor_get(x_1167, 1);
lean_inc(x_1169);
lean_dec(x_1167);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1165);
lean_inc(x_1);
x_1170 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1165, x_6, x_7, x_8, x_9, x_10, x_11, x_1169);
if (lean_obj_tag(x_1170) == 0)
{
lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; lean_object* x_1175; 
x_1171 = lean_ctor_get(x_1170, 0);
lean_inc(x_1171);
x_1172 = lean_ctor_get(x_1170, 1);
lean_inc(x_1172);
lean_dec(x_1170);
x_1173 = lean_unsigned_to_nat(1u);
x_1174 = lean_nat_add(x_6, x_1173);
lean_dec(x_6);
lean_inc(x_1166);
x_1175 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1166, x_1174, x_7, x_8, x_9, x_10, x_11, x_1172);
if (lean_obj_tag(x_1175) == 0)
{
uint8_t x_1176; 
x_1176 = !lean_is_exclusive(x_1175);
if (x_1176 == 0)
{
lean_object* x_1177; lean_object* x_1178; 
x_1177 = lean_ctor_get(x_1175, 0);
x_1178 = lean_expr_update_let(x_5, x_1168, x_1171, x_1177);
lean_ctor_set(x_1175, 0, x_1178);
return x_1175;
}
else
{
lean_object* x_1179; lean_object* x_1180; lean_object* x_1181; lean_object* x_1182; 
x_1179 = lean_ctor_get(x_1175, 0);
x_1180 = lean_ctor_get(x_1175, 1);
lean_inc(x_1180);
lean_inc(x_1179);
lean_dec(x_1175);
x_1181 = lean_expr_update_let(x_5, x_1168, x_1171, x_1179);
x_1182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1182, 0, x_1181);
lean_ctor_set(x_1182, 1, x_1180);
return x_1182;
}
}
else
{
uint8_t x_1183; 
lean_dec(x_1171);
lean_dec(x_1168);
lean_free_object(x_5);
lean_dec(x_1166);
lean_dec(x_1165);
lean_dec(x_1164);
lean_dec(x_1163);
x_1183 = !lean_is_exclusive(x_1175);
if (x_1183 == 0)
{
return x_1175;
}
else
{
lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; 
x_1184 = lean_ctor_get(x_1175, 0);
x_1185 = lean_ctor_get(x_1175, 1);
lean_inc(x_1185);
lean_inc(x_1184);
lean_dec(x_1175);
x_1186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1186, 0, x_1184);
lean_ctor_set(x_1186, 1, x_1185);
return x_1186;
}
}
}
else
{
uint8_t x_1187; 
lean_dec(x_1168);
lean_free_object(x_5);
lean_dec(x_1166);
lean_dec(x_1165);
lean_dec(x_1164);
lean_dec(x_1163);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1187 = !lean_is_exclusive(x_1170);
if (x_1187 == 0)
{
return x_1170;
}
else
{
lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; 
x_1188 = lean_ctor_get(x_1170, 0);
x_1189 = lean_ctor_get(x_1170, 1);
lean_inc(x_1189);
lean_inc(x_1188);
lean_dec(x_1170);
x_1190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1190, 0, x_1188);
lean_ctor_set(x_1190, 1, x_1189);
return x_1190;
}
}
}
else
{
uint8_t x_1191; 
lean_free_object(x_5);
lean_dec(x_1166);
lean_dec(x_1165);
lean_dec(x_1164);
lean_dec(x_1163);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1191 = !lean_is_exclusive(x_1167);
if (x_1191 == 0)
{
return x_1167;
}
else
{
lean_object* x_1192; lean_object* x_1193; lean_object* x_1194; 
x_1192 = lean_ctor_get(x_1167, 0);
x_1193 = lean_ctor_get(x_1167, 1);
lean_inc(x_1193);
lean_inc(x_1192);
lean_dec(x_1167);
x_1194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1194, 0, x_1192);
lean_ctor_set(x_1194, 1, x_1193);
return x_1194;
}
}
}
else
{
lean_object* x_1195; lean_object* x_1196; lean_object* x_1197; lean_object* x_1198; uint64_t x_1199; lean_object* x_1200; 
x_1195 = lean_ctor_get(x_5, 0);
x_1196 = lean_ctor_get(x_5, 1);
x_1197 = lean_ctor_get(x_5, 2);
x_1198 = lean_ctor_get(x_5, 3);
x_1199 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
lean_inc(x_1198);
lean_inc(x_1197);
lean_inc(x_1196);
lean_inc(x_1195);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1196);
lean_inc(x_1);
x_1200 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1196, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1200) == 0)
{
lean_object* x_1201; lean_object* x_1202; lean_object* x_1203; 
x_1201 = lean_ctor_get(x_1200, 0);
lean_inc(x_1201);
x_1202 = lean_ctor_get(x_1200, 1);
lean_inc(x_1202);
lean_dec(x_1200);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1197);
lean_inc(x_1);
x_1203 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1197, x_6, x_7, x_8, x_9, x_10, x_11, x_1202);
if (lean_obj_tag(x_1203) == 0)
{
lean_object* x_1204; lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; lean_object* x_1208; 
x_1204 = lean_ctor_get(x_1203, 0);
lean_inc(x_1204);
x_1205 = lean_ctor_get(x_1203, 1);
lean_inc(x_1205);
lean_dec(x_1203);
x_1206 = lean_unsigned_to_nat(1u);
x_1207 = lean_nat_add(x_6, x_1206);
lean_dec(x_6);
lean_inc(x_1198);
x_1208 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1198, x_1207, x_7, x_8, x_9, x_10, x_11, x_1205);
if (lean_obj_tag(x_1208) == 0)
{
lean_object* x_1209; lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; 
x_1209 = lean_ctor_get(x_1208, 0);
lean_inc(x_1209);
x_1210 = lean_ctor_get(x_1208, 1);
lean_inc(x_1210);
if (lean_is_exclusive(x_1208)) {
 lean_ctor_release(x_1208, 0);
 lean_ctor_release(x_1208, 1);
 x_1211 = x_1208;
} else {
 lean_dec_ref(x_1208);
 x_1211 = lean_box(0);
}
x_1212 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_1212, 0, x_1195);
lean_ctor_set(x_1212, 1, x_1196);
lean_ctor_set(x_1212, 2, x_1197);
lean_ctor_set(x_1212, 3, x_1198);
lean_ctor_set_uint64(x_1212, sizeof(void*)*4, x_1199);
x_1213 = lean_expr_update_let(x_1212, x_1201, x_1204, x_1209);
if (lean_is_scalar(x_1211)) {
 x_1214 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1214 = x_1211;
}
lean_ctor_set(x_1214, 0, x_1213);
lean_ctor_set(x_1214, 1, x_1210);
return x_1214;
}
else
{
lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; lean_object* x_1218; 
lean_dec(x_1204);
lean_dec(x_1201);
lean_dec(x_1198);
lean_dec(x_1197);
lean_dec(x_1196);
lean_dec(x_1195);
x_1215 = lean_ctor_get(x_1208, 0);
lean_inc(x_1215);
x_1216 = lean_ctor_get(x_1208, 1);
lean_inc(x_1216);
if (lean_is_exclusive(x_1208)) {
 lean_ctor_release(x_1208, 0);
 lean_ctor_release(x_1208, 1);
 x_1217 = x_1208;
} else {
 lean_dec_ref(x_1208);
 x_1217 = lean_box(0);
}
if (lean_is_scalar(x_1217)) {
 x_1218 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1218 = x_1217;
}
lean_ctor_set(x_1218, 0, x_1215);
lean_ctor_set(x_1218, 1, x_1216);
return x_1218;
}
}
else
{
lean_object* x_1219; lean_object* x_1220; lean_object* x_1221; lean_object* x_1222; 
lean_dec(x_1201);
lean_dec(x_1198);
lean_dec(x_1197);
lean_dec(x_1196);
lean_dec(x_1195);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1219 = lean_ctor_get(x_1203, 0);
lean_inc(x_1219);
x_1220 = lean_ctor_get(x_1203, 1);
lean_inc(x_1220);
if (lean_is_exclusive(x_1203)) {
 lean_ctor_release(x_1203, 0);
 lean_ctor_release(x_1203, 1);
 x_1221 = x_1203;
} else {
 lean_dec_ref(x_1203);
 x_1221 = lean_box(0);
}
if (lean_is_scalar(x_1221)) {
 x_1222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1222 = x_1221;
}
lean_ctor_set(x_1222, 0, x_1219);
lean_ctor_set(x_1222, 1, x_1220);
return x_1222;
}
}
else
{
lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; 
lean_dec(x_1198);
lean_dec(x_1197);
lean_dec(x_1196);
lean_dec(x_1195);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1223 = lean_ctor_get(x_1200, 0);
lean_inc(x_1223);
x_1224 = lean_ctor_get(x_1200, 1);
lean_inc(x_1224);
if (lean_is_exclusive(x_1200)) {
 lean_ctor_release(x_1200, 0);
 lean_ctor_release(x_1200, 1);
 x_1225 = x_1200;
} else {
 lean_dec_ref(x_1200);
 x_1225 = lean_box(0);
}
if (lean_is_scalar(x_1225)) {
 x_1226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1226 = x_1225;
}
lean_ctor_set(x_1226, 0, x_1223);
lean_ctor_set(x_1226, 1, x_1224);
return x_1226;
}
}
}
case 10:
{
uint8_t x_1227; 
x_1227 = !lean_is_exclusive(x_5);
if (x_1227 == 0)
{
lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; 
x_1228 = lean_ctor_get(x_5, 0);
x_1229 = lean_ctor_get(x_5, 1);
lean_inc(x_1229);
x_1230 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1229, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1230) == 0)
{
uint8_t x_1231; 
x_1231 = !lean_is_exclusive(x_1230);
if (x_1231 == 0)
{
lean_object* x_1232; lean_object* x_1233; 
x_1232 = lean_ctor_get(x_1230, 0);
x_1233 = lean_expr_update_mdata(x_5, x_1232);
lean_ctor_set(x_1230, 0, x_1233);
return x_1230;
}
else
{
lean_object* x_1234; lean_object* x_1235; lean_object* x_1236; lean_object* x_1237; 
x_1234 = lean_ctor_get(x_1230, 0);
x_1235 = lean_ctor_get(x_1230, 1);
lean_inc(x_1235);
lean_inc(x_1234);
lean_dec(x_1230);
x_1236 = lean_expr_update_mdata(x_5, x_1234);
x_1237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1237, 0, x_1236);
lean_ctor_set(x_1237, 1, x_1235);
return x_1237;
}
}
else
{
uint8_t x_1238; 
lean_free_object(x_5);
lean_dec(x_1229);
lean_dec(x_1228);
x_1238 = !lean_is_exclusive(x_1230);
if (x_1238 == 0)
{
return x_1230;
}
else
{
lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; 
x_1239 = lean_ctor_get(x_1230, 0);
x_1240 = lean_ctor_get(x_1230, 1);
lean_inc(x_1240);
lean_inc(x_1239);
lean_dec(x_1230);
x_1241 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1241, 0, x_1239);
lean_ctor_set(x_1241, 1, x_1240);
return x_1241;
}
}
}
else
{
lean_object* x_1242; lean_object* x_1243; uint64_t x_1244; lean_object* x_1245; 
x_1242 = lean_ctor_get(x_5, 0);
x_1243 = lean_ctor_get(x_5, 1);
x_1244 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_1243);
lean_inc(x_1242);
lean_dec(x_5);
lean_inc(x_1243);
x_1245 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1243, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1245) == 0)
{
lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; 
x_1246 = lean_ctor_get(x_1245, 0);
lean_inc(x_1246);
x_1247 = lean_ctor_get(x_1245, 1);
lean_inc(x_1247);
if (lean_is_exclusive(x_1245)) {
 lean_ctor_release(x_1245, 0);
 lean_ctor_release(x_1245, 1);
 x_1248 = x_1245;
} else {
 lean_dec_ref(x_1245);
 x_1248 = lean_box(0);
}
x_1249 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_1249, 0, x_1242);
lean_ctor_set(x_1249, 1, x_1243);
lean_ctor_set_uint64(x_1249, sizeof(void*)*2, x_1244);
x_1250 = lean_expr_update_mdata(x_1249, x_1246);
if (lean_is_scalar(x_1248)) {
 x_1251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1251 = x_1248;
}
lean_ctor_set(x_1251, 0, x_1250);
lean_ctor_set(x_1251, 1, x_1247);
return x_1251;
}
else
{
lean_object* x_1252; lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; 
lean_dec(x_1243);
lean_dec(x_1242);
x_1252 = lean_ctor_get(x_1245, 0);
lean_inc(x_1252);
x_1253 = lean_ctor_get(x_1245, 1);
lean_inc(x_1253);
if (lean_is_exclusive(x_1245)) {
 lean_ctor_release(x_1245, 0);
 lean_ctor_release(x_1245, 1);
 x_1254 = x_1245;
} else {
 lean_dec_ref(x_1245);
 x_1254 = lean_box(0);
}
if (lean_is_scalar(x_1254)) {
 x_1255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1255 = x_1254;
}
lean_ctor_set(x_1255, 0, x_1252);
lean_ctor_set(x_1255, 1, x_1253);
return x_1255;
}
}
}
case 11:
{
uint8_t x_1256; 
x_1256 = !lean_is_exclusive(x_5);
if (x_1256 == 0)
{
lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; 
x_1257 = lean_ctor_get(x_5, 0);
x_1258 = lean_ctor_get(x_5, 1);
x_1259 = lean_ctor_get(x_5, 2);
lean_inc(x_1259);
x_1260 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1259, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1260) == 0)
{
uint8_t x_1261; 
x_1261 = !lean_is_exclusive(x_1260);
if (x_1261 == 0)
{
lean_object* x_1262; lean_object* x_1263; 
x_1262 = lean_ctor_get(x_1260, 0);
x_1263 = lean_expr_update_proj(x_5, x_1262);
lean_ctor_set(x_1260, 0, x_1263);
return x_1260;
}
else
{
lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; 
x_1264 = lean_ctor_get(x_1260, 0);
x_1265 = lean_ctor_get(x_1260, 1);
lean_inc(x_1265);
lean_inc(x_1264);
lean_dec(x_1260);
x_1266 = lean_expr_update_proj(x_5, x_1264);
x_1267 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1267, 0, x_1266);
lean_ctor_set(x_1267, 1, x_1265);
return x_1267;
}
}
else
{
uint8_t x_1268; 
lean_free_object(x_5);
lean_dec(x_1259);
lean_dec(x_1258);
lean_dec(x_1257);
x_1268 = !lean_is_exclusive(x_1260);
if (x_1268 == 0)
{
return x_1260;
}
else
{
lean_object* x_1269; lean_object* x_1270; lean_object* x_1271; 
x_1269 = lean_ctor_get(x_1260, 0);
x_1270 = lean_ctor_get(x_1260, 1);
lean_inc(x_1270);
lean_inc(x_1269);
lean_dec(x_1260);
x_1271 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1271, 0, x_1269);
lean_ctor_set(x_1271, 1, x_1270);
return x_1271;
}
}
}
else
{
lean_object* x_1272; lean_object* x_1273; lean_object* x_1274; uint64_t x_1275; lean_object* x_1276; 
x_1272 = lean_ctor_get(x_5, 0);
x_1273 = lean_ctor_get(x_5, 1);
x_1274 = lean_ctor_get(x_5, 2);
x_1275 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_1274);
lean_inc(x_1273);
lean_inc(x_1272);
lean_dec(x_5);
lean_inc(x_1274);
x_1276 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1274, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1276) == 0)
{
lean_object* x_1277; lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; 
x_1277 = lean_ctor_get(x_1276, 0);
lean_inc(x_1277);
x_1278 = lean_ctor_get(x_1276, 1);
lean_inc(x_1278);
if (lean_is_exclusive(x_1276)) {
 lean_ctor_release(x_1276, 0);
 lean_ctor_release(x_1276, 1);
 x_1279 = x_1276;
} else {
 lean_dec_ref(x_1276);
 x_1279 = lean_box(0);
}
x_1280 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_1280, 0, x_1272);
lean_ctor_set(x_1280, 1, x_1273);
lean_ctor_set(x_1280, 2, x_1274);
lean_ctor_set_uint64(x_1280, sizeof(void*)*3, x_1275);
x_1281 = lean_expr_update_proj(x_1280, x_1277);
if (lean_is_scalar(x_1279)) {
 x_1282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1282 = x_1279;
}
lean_ctor_set(x_1282, 0, x_1281);
lean_ctor_set(x_1282, 1, x_1278);
return x_1282;
}
else
{
lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; 
lean_dec(x_1274);
lean_dec(x_1273);
lean_dec(x_1272);
x_1283 = lean_ctor_get(x_1276, 0);
lean_inc(x_1283);
x_1284 = lean_ctor_get(x_1276, 1);
lean_inc(x_1284);
if (lean_is_exclusive(x_1276)) {
 lean_ctor_release(x_1276, 0);
 lean_ctor_release(x_1276, 1);
 x_1285 = x_1276;
} else {
 lean_dec_ref(x_1276);
 x_1285 = lean_box(0);
}
if (lean_is_scalar(x_1285)) {
 x_1286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1286 = x_1285;
}
lean_ctor_set(x_1286, 0, x_1283);
lean_ctor_set(x_1286, 1, x_1284);
return x_1286;
}
}
}
default: 
{
lean_object* x_1287; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1287, 0, x_5);
lean_ctor_set(x_1287, 1, x_12);
return x_1287;
}
}
}
block_289:
{
lean_dec(x_13);
switch (lean_obj_tag(x_5)) {
case 5:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_5);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_5, 0);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_15);
lean_inc(x_1);
x_17 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_16);
x_20 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_expr_update_app(x_5, x_18, x_22);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_expr_update_app(x_5, x_18, x_24);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_18);
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_15);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_free_object(x_5);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
return x_17;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_ctor_get(x_17, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_17);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; uint64_t x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_5, 0);
x_37 = lean_ctor_get(x_5, 1);
x_38 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_36);
lean_inc(x_1);
x_39 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_36, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_37);
x_42 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_37, x_6, x_7, x_8, x_9, x_10, x_11, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_alloc_ctor(5, 2, 8);
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_37);
lean_ctor_set_uint64(x_46, sizeof(void*)*2, x_38);
x_47 = lean_expr_update_app(x_46, x_40, x_43);
if (lean_is_scalar(x_45)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_45;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_44);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_36);
x_49 = lean_ctor_get(x_42, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_51 = x_42;
} else {
 lean_dec_ref(x_42);
 x_51 = lean_box(0);
}
if (lean_is_scalar(x_51)) {
 x_52 = lean_alloc_ctor(1, 2, 0);
} else {
 x_52 = x_51;
}
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_53 = lean_ctor_get(x_39, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_39, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_55 = x_39;
} else {
 lean_dec_ref(x_39);
 x_55 = lean_box(0);
}
if (lean_is_scalar(x_55)) {
 x_56 = lean_alloc_ctor(1, 2, 0);
} else {
 x_56 = x_55;
}
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
case 6:
{
uint8_t x_57; 
x_57 = !lean_is_exclusive(x_5);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_5, 0);
x_59 = lean_ctor_get(x_5, 1);
x_60 = lean_ctor_get(x_5, 2);
x_61 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_59);
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
lean_inc(x_60);
x_67 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_60, x_66, x_7, x_8, x_9, x_10, x_11, x_64);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; uint8_t x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = (uint8_t)((x_61 << 24) >> 61);
x_71 = lean_expr_update_lambda(x_5, x_70, x_63, x_69);
lean_ctor_set(x_67, 0, x_71);
return x_67;
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_67, 0);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_67);
x_74 = (uint8_t)((x_61 << 24) >> 61);
x_75 = lean_expr_update_lambda(x_5, x_74, x_63, x_72);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
}
else
{
uint8_t x_77; 
lean_dec(x_63);
lean_free_object(x_5);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
x_77 = !lean_is_exclusive(x_67);
if (x_77 == 0)
{
return x_67;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_67, 0);
x_79 = lean_ctor_get(x_67, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_67);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_free_object(x_5);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_62);
if (x_81 == 0)
{
return x_62;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_62, 0);
x_83 = lean_ctor_get(x_62, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_62);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint64_t x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_5, 0);
x_86 = lean_ctor_get(x_5, 1);
x_87 = lean_ctor_get(x_5, 2);
x_88 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_87);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_86);
lean_inc(x_1);
x_89 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_86, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
lean_inc(x_87);
x_94 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_87, x_93, x_7, x_8, x_9, x_10, x_11, x_91);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
x_98 = lean_alloc_ctor(6, 3, 8);
lean_ctor_set(x_98, 0, x_85);
lean_ctor_set(x_98, 1, x_86);
lean_ctor_set(x_98, 2, x_87);
lean_ctor_set_uint64(x_98, sizeof(void*)*3, x_88);
x_99 = (uint8_t)((x_88 << 24) >> 61);
x_100 = lean_expr_update_lambda(x_98, x_99, x_90, x_95);
if (lean_is_scalar(x_97)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_97;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_96);
return x_101;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
x_102 = lean_ctor_get(x_94, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_94, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_104 = x_94;
} else {
 lean_dec_ref(x_94);
 x_104 = lean_box(0);
}
if (lean_is_scalar(x_104)) {
 x_105 = lean_alloc_ctor(1, 2, 0);
} else {
 x_105 = x_104;
}
lean_ctor_set(x_105, 0, x_102);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_106 = lean_ctor_get(x_89, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_89, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_108 = x_89;
} else {
 lean_dec_ref(x_89);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(1, 2, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
return x_109;
}
}
}
case 7:
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_5);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; uint64_t x_114; lean_object* x_115; 
x_111 = lean_ctor_get(x_5, 0);
x_112 = lean_ctor_get(x_5, 1);
x_113 = lean_ctor_get(x_5, 2);
x_114 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_112);
lean_inc(x_1);
x_115 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_112, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_nat_add(x_6, x_118);
lean_dec(x_6);
lean_inc(x_113);
x_120 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_113, x_119, x_7, x_8, x_9, x_10, x_11, x_117);
if (lean_obj_tag(x_120) == 0)
{
uint8_t x_121; 
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = (uint8_t)((x_114 << 24) >> 61);
x_124 = lean_expr_update_forall(x_5, x_123, x_116, x_122);
lean_ctor_set(x_120, 0, x_124);
return x_120;
}
else
{
lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_120, 0);
x_126 = lean_ctor_get(x_120, 1);
lean_inc(x_126);
lean_inc(x_125);
lean_dec(x_120);
x_127 = (uint8_t)((x_114 << 24) >> 61);
x_128 = lean_expr_update_forall(x_5, x_127, x_116, x_125);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
return x_129;
}
}
else
{
uint8_t x_130; 
lean_dec(x_116);
lean_free_object(x_5);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
x_130 = !lean_is_exclusive(x_120);
if (x_130 == 0)
{
return x_120;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_120, 0);
x_132 = lean_ctor_get(x_120, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_120);
x_133 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
return x_133;
}
}
}
else
{
uint8_t x_134; 
lean_free_object(x_5);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_134 = !lean_is_exclusive(x_115);
if (x_134 == 0)
{
return x_115;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_115, 0);
x_136 = lean_ctor_get(x_115, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_115);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; uint64_t x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_5, 0);
x_139 = lean_ctor_get(x_5, 1);
x_140 = lean_ctor_get(x_5, 2);
x_141 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_140);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_139);
lean_inc(x_1);
x_142 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_139, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_unsigned_to_nat(1u);
x_146 = lean_nat_add(x_6, x_145);
lean_dec(x_6);
lean_inc(x_140);
x_147 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_140, x_146, x_7, x_8, x_9, x_10, x_11, x_144);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_150 = x_147;
} else {
 lean_dec_ref(x_147);
 x_150 = lean_box(0);
}
x_151 = lean_alloc_ctor(7, 3, 8);
lean_ctor_set(x_151, 0, x_138);
lean_ctor_set(x_151, 1, x_139);
lean_ctor_set(x_151, 2, x_140);
lean_ctor_set_uint64(x_151, sizeof(void*)*3, x_141);
x_152 = (uint8_t)((x_141 << 24) >> 61);
x_153 = lean_expr_update_forall(x_151, x_152, x_143, x_148);
if (lean_is_scalar(x_150)) {
 x_154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_154 = x_150;
}
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_149);
return x_154;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_143);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
x_155 = lean_ctor_get(x_147, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_147, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_147)) {
 lean_ctor_release(x_147, 0);
 lean_ctor_release(x_147, 1);
 x_157 = x_147;
} else {
 lean_dec_ref(x_147);
 x_157 = lean_box(0);
}
if (lean_is_scalar(x_157)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_157;
}
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_159 = lean_ctor_get(x_142, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_142, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_161 = x_142;
} else {
 lean_dec_ref(x_142);
 x_161 = lean_box(0);
}
if (lean_is_scalar(x_161)) {
 x_162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_162 = x_161;
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_160);
return x_162;
}
}
}
case 8:
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_5);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_164 = lean_ctor_get(x_5, 0);
x_165 = lean_ctor_get(x_5, 1);
x_166 = lean_ctor_get(x_5, 2);
x_167 = lean_ctor_get(x_5, 3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_165);
lean_inc(x_1);
x_168 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_165, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_166);
lean_inc(x_1);
x_171 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_166, x_6, x_7, x_8, x_9, x_10, x_11, x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_unsigned_to_nat(1u);
x_175 = lean_nat_add(x_6, x_174);
lean_dec(x_6);
lean_inc(x_167);
x_176 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_167, x_175, x_7, x_8, x_9, x_10, x_11, x_173);
if (lean_obj_tag(x_176) == 0)
{
uint8_t x_177; 
x_177 = !lean_is_exclusive(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; 
x_178 = lean_ctor_get(x_176, 0);
x_179 = lean_expr_update_let(x_5, x_169, x_172, x_178);
lean_ctor_set(x_176, 0, x_179);
return x_176;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_180 = lean_ctor_get(x_176, 0);
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_176);
x_182 = lean_expr_update_let(x_5, x_169, x_172, x_180);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_181);
return x_183;
}
}
else
{
uint8_t x_184; 
lean_dec(x_172);
lean_dec(x_169);
lean_free_object(x_5);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
x_184 = !lean_is_exclusive(x_176);
if (x_184 == 0)
{
return x_176;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_176, 0);
x_186 = lean_ctor_get(x_176, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_176);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
else
{
uint8_t x_188; 
lean_dec(x_169);
lean_free_object(x_5);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_188 = !lean_is_exclusive(x_171);
if (x_188 == 0)
{
return x_171;
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_171, 0);
x_190 = lean_ctor_get(x_171, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_171);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_189);
lean_ctor_set(x_191, 1, x_190);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_free_object(x_5);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_192 = !lean_is_exclusive(x_168);
if (x_192 == 0)
{
return x_168;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_168, 0);
x_194 = lean_ctor_get(x_168, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_168);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint64_t x_200; lean_object* x_201; 
x_196 = lean_ctor_get(x_5, 0);
x_197 = lean_ctor_get(x_5, 1);
x_198 = lean_ctor_get(x_5, 2);
x_199 = lean_ctor_get(x_5, 3);
x_200 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
lean_inc(x_199);
lean_inc(x_198);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_197);
lean_inc(x_1);
x_201 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_197, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_198);
lean_inc(x_1);
x_204 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_198, x_6, x_7, x_8, x_9, x_10, x_11, x_203);
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
lean_inc(x_199);
x_209 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_199, x_208, x_7, x_8, x_9, x_10, x_11, x_206);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_212 = x_209;
} else {
 lean_dec_ref(x_209);
 x_212 = lean_box(0);
}
x_213 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_213, 0, x_196);
lean_ctor_set(x_213, 1, x_197);
lean_ctor_set(x_213, 2, x_198);
lean_ctor_set(x_213, 3, x_199);
lean_ctor_set_uint64(x_213, sizeof(void*)*4, x_200);
x_214 = lean_expr_update_let(x_213, x_202, x_205, x_210);
if (lean_is_scalar(x_212)) {
 x_215 = lean_alloc_ctor(0, 2, 0);
} else {
 x_215 = x_212;
}
lean_ctor_set(x_215, 0, x_214);
lean_ctor_set(x_215, 1, x_211);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_205);
lean_dec(x_202);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
x_216 = lean_ctor_get(x_209, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_209, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_218 = x_209;
} else {
 lean_dec_ref(x_209);
 x_218 = lean_box(0);
}
if (lean_is_scalar(x_218)) {
 x_219 = lean_alloc_ctor(1, 2, 0);
} else {
 x_219 = x_218;
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_217);
return x_219;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; 
lean_dec(x_202);
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_220 = lean_ctor_get(x_204, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_204, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_222 = x_204;
} else {
 lean_dec_ref(x_204);
 x_222 = lean_box(0);
}
if (lean_is_scalar(x_222)) {
 x_223 = lean_alloc_ctor(1, 2, 0);
} else {
 x_223 = x_222;
}
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_221);
return x_223;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_dec(x_199);
lean_dec(x_198);
lean_dec(x_197);
lean_dec(x_196);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_224 = lean_ctor_get(x_201, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_201, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_226 = x_201;
} else {
 lean_dec_ref(x_201);
 x_226 = lean_box(0);
}
if (lean_is_scalar(x_226)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_226;
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_225);
return x_227;
}
}
}
case 10:
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_5);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_5, 0);
x_230 = lean_ctor_get(x_5, 1);
lean_inc(x_230);
x_231 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_230, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_231) == 0)
{
uint8_t x_232; 
x_232 = !lean_is_exclusive(x_231);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; 
x_233 = lean_ctor_get(x_231, 0);
x_234 = lean_expr_update_mdata(x_5, x_233);
lean_ctor_set(x_231, 0, x_234);
return x_231;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_235 = lean_ctor_get(x_231, 0);
x_236 = lean_ctor_get(x_231, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_231);
x_237 = lean_expr_update_mdata(x_5, x_235);
x_238 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_238, 0, x_237);
lean_ctor_set(x_238, 1, x_236);
return x_238;
}
}
else
{
uint8_t x_239; 
lean_free_object(x_5);
lean_dec(x_230);
lean_dec(x_229);
x_239 = !lean_is_exclusive(x_231);
if (x_239 == 0)
{
return x_231;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_231, 0);
x_241 = lean_ctor_get(x_231, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_231);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
else
{
lean_object* x_243; lean_object* x_244; uint64_t x_245; lean_object* x_246; 
x_243 = lean_ctor_get(x_5, 0);
x_244 = lean_ctor_get(x_5, 1);
x_245 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
lean_inc(x_244);
lean_inc(x_243);
lean_dec(x_5);
lean_inc(x_244);
x_246 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_244, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_249 = x_246;
} else {
 lean_dec_ref(x_246);
 x_249 = lean_box(0);
}
x_250 = lean_alloc_ctor(10, 2, 8);
lean_ctor_set(x_250, 0, x_243);
lean_ctor_set(x_250, 1, x_244);
lean_ctor_set_uint64(x_250, sizeof(void*)*2, x_245);
x_251 = lean_expr_update_mdata(x_250, x_247);
if (lean_is_scalar(x_249)) {
 x_252 = lean_alloc_ctor(0, 2, 0);
} else {
 x_252 = x_249;
}
lean_ctor_set(x_252, 0, x_251);
lean_ctor_set(x_252, 1, x_248);
return x_252;
}
else
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_244);
lean_dec(x_243);
x_253 = lean_ctor_get(x_246, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_246, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_255 = x_246;
} else {
 lean_dec_ref(x_246);
 x_255 = lean_box(0);
}
if (lean_is_scalar(x_255)) {
 x_256 = lean_alloc_ctor(1, 2, 0);
} else {
 x_256 = x_255;
}
lean_ctor_set(x_256, 0, x_253);
lean_ctor_set(x_256, 1, x_254);
return x_256;
}
}
}
case 11:
{
uint8_t x_257; 
x_257 = !lean_is_exclusive(x_5);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_258 = lean_ctor_get(x_5, 0);
x_259 = lean_ctor_get(x_5, 1);
x_260 = lean_ctor_get(x_5, 2);
lean_inc(x_260);
x_261 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_260, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_261) == 0)
{
uint8_t x_262; 
x_262 = !lean_is_exclusive(x_261);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; 
x_263 = lean_ctor_get(x_261, 0);
x_264 = lean_expr_update_proj(x_5, x_263);
lean_ctor_set(x_261, 0, x_264);
return x_261;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_265 = lean_ctor_get(x_261, 0);
x_266 = lean_ctor_get(x_261, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_261);
x_267 = lean_expr_update_proj(x_5, x_265);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_267);
lean_ctor_set(x_268, 1, x_266);
return x_268;
}
}
else
{
uint8_t x_269; 
lean_free_object(x_5);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_258);
x_269 = !lean_is_exclusive(x_261);
if (x_269 == 0)
{
return x_261;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_261, 0);
x_271 = lean_ctor_get(x_261, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_261);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; uint64_t x_276; lean_object* x_277; 
x_273 = lean_ctor_get(x_5, 0);
x_274 = lean_ctor_get(x_5, 1);
x_275 = lean_ctor_get(x_5, 2);
x_276 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
lean_inc(x_275);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_5);
lean_inc(x_275);
x_277 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_275, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_280 = x_277;
} else {
 lean_dec_ref(x_277);
 x_280 = lean_box(0);
}
x_281 = lean_alloc_ctor(11, 3, 8);
lean_ctor_set(x_281, 0, x_273);
lean_ctor_set(x_281, 1, x_274);
lean_ctor_set(x_281, 2, x_275);
lean_ctor_set_uint64(x_281, sizeof(void*)*3, x_276);
x_282 = lean_expr_update_proj(x_281, x_278);
if (lean_is_scalar(x_280)) {
 x_283 = lean_alloc_ctor(0, 2, 0);
} else {
 x_283 = x_280;
}
lean_ctor_set(x_283, 0, x_282);
lean_ctor_set(x_283, 1, x_279);
return x_283;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
x_284 = lean_ctor_get(x_277, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_277, 1);
lean_inc(x_285);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_286 = x_277;
} else {
 lean_dec_ref(x_277);
 x_286 = lean_box(0);
}
if (lean_is_scalar(x_286)) {
 x_287 = lean_alloc_ctor(1, 2, 0);
} else {
 x_287 = x_286;
}
lean_ctor_set(x_287, 0, x_284);
lean_ctor_set(x_287, 1, x_285);
return x_287;
}
}
}
default: 
{
lean_object* x_288; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_5);
lean_ctor_set(x_288, 1, x_12);
return x_288;
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
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = l_Lean_Meta_instantiateMVars(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
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
x_38 = l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_31_(x_3, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_9);
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
x_91 = l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_31_(x_3, x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
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
else
{
uint8_t x_118; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_118 = !lean_is_exclusive(x_9);
if (x_118 == 0)
{
return x_9;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_9, 0);
x_120 = lean_ctor_get(x_9, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_9);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
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
lean_object* initialize_Init(lean_object*);
lean_object* initialize_Lean_Data_Occurrences(lean_object*);
lean_object* initialize_Lean_HeadIndex(lean_object*);
lean_object* initialize_Lean_Meta_ExprDefEq(lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_KAbstract(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
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
l_Lean_Meta_kabstract___closed__1 = _init_l_Lean_Meta_kabstract___closed__1();
lean_mark_persistent(l_Lean_Meta_kabstract___closed__1);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
