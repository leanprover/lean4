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
uint8_t l_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1336_(lean_object*, lean_object*);
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
uint8_t l_Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_92_(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_252; 
x_252 = l_Lean_Expr_hasLooseBVars(x_5);
if (x_252 == 0)
{
lean_object* x_253; uint8_t x_254; 
lean_inc(x_5);
x_253 = l_Lean_Expr_toHeadIndex(x_5);
x_254 = l_Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_92_(x_253, x_3);
lean_dec(x_253);
if (x_254 == 0)
{
lean_object* x_255; 
x_255 = lean_box(0);
x_13 = x_255;
goto block_251;
}
else
{
lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_256 = lean_unsigned_to_nat(0u);
x_257 = l_Lean_Expr_headNumArgs_go(x_5, x_256);
x_258 = lean_nat_dec_eq(x_257, x_4);
lean_dec(x_257);
if (x_258 == 0)
{
lean_object* x_259; 
x_259 = lean_box(0);
x_13 = x_259;
goto block_251;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_260 = lean_st_ref_get(x_9, x_12);
x_261 = lean_ctor_get(x_260, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_260, 1);
lean_inc(x_262);
lean_dec(x_260);
x_263 = lean_ctor_get(x_261, 0);
lean_inc(x_263);
lean_dec(x_261);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_5);
x_264 = l_Lean_Meta_isExprDefEq(x_5, x_1, x_8, x_9, x_10, x_11, x_262);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; uint8_t x_266; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_unbox(x_265);
lean_dec(x_265);
if (x_266 == 0)
{
lean_dec(x_263);
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_267 = lean_ctor_get(x_264, 1);
lean_inc(x_267);
lean_dec(x_264);
x_268 = lean_ctor_get(x_5, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_5, 1);
lean_inc(x_269);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_268);
lean_inc(x_1);
x_270 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_268, x_6, x_7, x_8, x_9, x_10, x_11, x_267);
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_270, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_270, 1);
lean_inc(x_272);
lean_dec(x_270);
lean_inc(x_269);
x_273 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_269, x_6, x_7, x_8, x_9, x_10, x_11, x_272);
if (lean_obj_tag(x_273) == 0)
{
uint8_t x_274; 
x_274 = !lean_is_exclusive(x_273);
if (x_274 == 0)
{
lean_object* x_275; size_t x_276; size_t x_277; uint8_t x_278; 
x_275 = lean_ctor_get(x_273, 0);
x_276 = lean_ptr_addr(x_268);
lean_dec(x_268);
x_277 = lean_ptr_addr(x_271);
x_278 = lean_usize_dec_eq(x_276, x_277);
if (x_278 == 0)
{
lean_object* x_279; 
lean_dec(x_269);
lean_dec(x_5);
x_279 = l_Lean_Expr_app___override(x_271, x_275);
lean_ctor_set(x_273, 0, x_279);
return x_273;
}
else
{
size_t x_280; size_t x_281; uint8_t x_282; 
x_280 = lean_ptr_addr(x_269);
lean_dec(x_269);
x_281 = lean_ptr_addr(x_275);
x_282 = lean_usize_dec_eq(x_280, x_281);
if (x_282 == 0)
{
lean_object* x_283; 
lean_dec(x_5);
x_283 = l_Lean_Expr_app___override(x_271, x_275);
lean_ctor_set(x_273, 0, x_283);
return x_273;
}
else
{
lean_dec(x_275);
lean_dec(x_271);
lean_ctor_set(x_273, 0, x_5);
return x_273;
}
}
}
else
{
lean_object* x_284; lean_object* x_285; size_t x_286; size_t x_287; uint8_t x_288; 
x_284 = lean_ctor_get(x_273, 0);
x_285 = lean_ctor_get(x_273, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_273);
x_286 = lean_ptr_addr(x_268);
lean_dec(x_268);
x_287 = lean_ptr_addr(x_271);
x_288 = lean_usize_dec_eq(x_286, x_287);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; 
lean_dec(x_269);
lean_dec(x_5);
x_289 = l_Lean_Expr_app___override(x_271, x_284);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_285);
return x_290;
}
else
{
size_t x_291; size_t x_292; uint8_t x_293; 
x_291 = lean_ptr_addr(x_269);
lean_dec(x_269);
x_292 = lean_ptr_addr(x_284);
x_293 = lean_usize_dec_eq(x_291, x_292);
if (x_293 == 0)
{
lean_object* x_294; lean_object* x_295; 
lean_dec(x_5);
x_294 = l_Lean_Expr_app___override(x_271, x_284);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_285);
return x_295;
}
else
{
lean_object* x_296; 
lean_dec(x_284);
lean_dec(x_271);
x_296 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_296, 0, x_5);
lean_ctor_set(x_296, 1, x_285);
return x_296;
}
}
}
}
else
{
uint8_t x_297; 
lean_dec(x_271);
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_5);
x_297 = !lean_is_exclusive(x_273);
if (x_297 == 0)
{
return x_273;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_273, 0);
x_299 = lean_ctor_get(x_273, 1);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_273);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
return x_300;
}
}
}
else
{
uint8_t x_301; 
lean_dec(x_269);
lean_dec(x_268);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_301 = !lean_is_exclusive(x_270);
if (x_301 == 0)
{
return x_270;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_270, 0);
x_303 = lean_ctor_get(x_270, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_270);
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
return x_304;
}
}
}
case 6:
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; 
x_305 = lean_ctor_get(x_264, 1);
lean_inc(x_305);
lean_dec(x_264);
x_306 = lean_ctor_get(x_5, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_5, 1);
lean_inc(x_307);
x_308 = lean_ctor_get(x_5, 2);
lean_inc(x_308);
x_309 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_307);
lean_inc(x_1);
x_310 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_307, x_6, x_7, x_8, x_9, x_10, x_11, x_305);
if (lean_obj_tag(x_310) == 0)
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
x_313 = lean_unsigned_to_nat(1u);
x_314 = lean_nat_add(x_6, x_313);
lean_dec(x_6);
lean_inc(x_308);
x_315 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_308, x_314, x_7, x_8, x_9, x_10, x_11, x_312);
if (lean_obj_tag(x_315) == 0)
{
uint8_t x_316; 
x_316 = !lean_is_exclusive(x_315);
if (x_316 == 0)
{
lean_object* x_317; lean_object* x_318; size_t x_319; size_t x_320; uint8_t x_321; 
x_317 = lean_ctor_get(x_315, 0);
lean_inc(x_308);
lean_inc(x_307);
lean_inc(x_306);
x_318 = l_Lean_Expr_lam___override(x_306, x_307, x_308, x_309);
x_319 = lean_ptr_addr(x_307);
lean_dec(x_307);
x_320 = lean_ptr_addr(x_311);
x_321 = lean_usize_dec_eq(x_319, x_320);
if (x_321 == 0)
{
lean_object* x_322; 
lean_dec(x_318);
lean_dec(x_308);
x_322 = l_Lean_Expr_lam___override(x_306, x_311, x_317, x_309);
lean_ctor_set(x_315, 0, x_322);
return x_315;
}
else
{
size_t x_323; size_t x_324; uint8_t x_325; 
x_323 = lean_ptr_addr(x_308);
lean_dec(x_308);
x_324 = lean_ptr_addr(x_317);
x_325 = lean_usize_dec_eq(x_323, x_324);
if (x_325 == 0)
{
lean_object* x_326; 
lean_dec(x_318);
x_326 = l_Lean_Expr_lam___override(x_306, x_311, x_317, x_309);
lean_ctor_set(x_315, 0, x_326);
return x_315;
}
else
{
uint8_t x_327; 
x_327 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_309, x_309);
if (x_327 == 0)
{
lean_object* x_328; 
lean_dec(x_318);
x_328 = l_Lean_Expr_lam___override(x_306, x_311, x_317, x_309);
lean_ctor_set(x_315, 0, x_328);
return x_315;
}
else
{
lean_dec(x_317);
lean_dec(x_311);
lean_dec(x_306);
lean_ctor_set(x_315, 0, x_318);
return x_315;
}
}
}
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; size_t x_332; size_t x_333; uint8_t x_334; 
x_329 = lean_ctor_get(x_315, 0);
x_330 = lean_ctor_get(x_315, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_315);
lean_inc(x_308);
lean_inc(x_307);
lean_inc(x_306);
x_331 = l_Lean_Expr_lam___override(x_306, x_307, x_308, x_309);
x_332 = lean_ptr_addr(x_307);
lean_dec(x_307);
x_333 = lean_ptr_addr(x_311);
x_334 = lean_usize_dec_eq(x_332, x_333);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; 
lean_dec(x_331);
lean_dec(x_308);
x_335 = l_Lean_Expr_lam___override(x_306, x_311, x_329, x_309);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_330);
return x_336;
}
else
{
size_t x_337; size_t x_338; uint8_t x_339; 
x_337 = lean_ptr_addr(x_308);
lean_dec(x_308);
x_338 = lean_ptr_addr(x_329);
x_339 = lean_usize_dec_eq(x_337, x_338);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; 
lean_dec(x_331);
x_340 = l_Lean_Expr_lam___override(x_306, x_311, x_329, x_309);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_330);
return x_341;
}
else
{
uint8_t x_342; 
x_342 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_309, x_309);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; 
lean_dec(x_331);
x_343 = l_Lean_Expr_lam___override(x_306, x_311, x_329, x_309);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_330);
return x_344;
}
else
{
lean_object* x_345; 
lean_dec(x_329);
lean_dec(x_311);
lean_dec(x_306);
x_345 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_345, 0, x_331);
lean_ctor_set(x_345, 1, x_330);
return x_345;
}
}
}
}
}
else
{
uint8_t x_346; 
lean_dec(x_311);
lean_dec(x_308);
lean_dec(x_307);
lean_dec(x_306);
x_346 = !lean_is_exclusive(x_315);
if (x_346 == 0)
{
return x_315;
}
else
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_347 = lean_ctor_get(x_315, 0);
x_348 = lean_ctor_get(x_315, 1);
lean_inc(x_348);
lean_inc(x_347);
lean_dec(x_315);
x_349 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
return x_349;
}
}
}
else
{
uint8_t x_350; 
lean_dec(x_308);
lean_dec(x_307);
lean_dec(x_306);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_350 = !lean_is_exclusive(x_310);
if (x_350 == 0)
{
return x_310;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_310, 0);
x_352 = lean_ctor_get(x_310, 1);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_310);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
return x_353;
}
}
}
case 7:
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; uint8_t x_358; lean_object* x_359; 
x_354 = lean_ctor_get(x_264, 1);
lean_inc(x_354);
lean_dec(x_264);
x_355 = lean_ctor_get(x_5, 0);
lean_inc(x_355);
x_356 = lean_ctor_get(x_5, 1);
lean_inc(x_356);
x_357 = lean_ctor_get(x_5, 2);
lean_inc(x_357);
x_358 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_356);
lean_inc(x_1);
x_359 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_356, x_6, x_7, x_8, x_9, x_10, x_11, x_354);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_360 = lean_ctor_get(x_359, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_359, 1);
lean_inc(x_361);
lean_dec(x_359);
x_362 = lean_unsigned_to_nat(1u);
x_363 = lean_nat_add(x_6, x_362);
lean_dec(x_6);
lean_inc(x_357);
x_364 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_357, x_363, x_7, x_8, x_9, x_10, x_11, x_361);
if (lean_obj_tag(x_364) == 0)
{
uint8_t x_365; 
x_365 = !lean_is_exclusive(x_364);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; size_t x_368; size_t x_369; uint8_t x_370; 
x_366 = lean_ctor_get(x_364, 0);
lean_inc(x_357);
lean_inc(x_356);
lean_inc(x_355);
x_367 = l_Lean_Expr_forallE___override(x_355, x_356, x_357, x_358);
x_368 = lean_ptr_addr(x_356);
lean_dec(x_356);
x_369 = lean_ptr_addr(x_360);
x_370 = lean_usize_dec_eq(x_368, x_369);
if (x_370 == 0)
{
lean_object* x_371; 
lean_dec(x_367);
lean_dec(x_357);
x_371 = l_Lean_Expr_forallE___override(x_355, x_360, x_366, x_358);
lean_ctor_set(x_364, 0, x_371);
return x_364;
}
else
{
size_t x_372; size_t x_373; uint8_t x_374; 
x_372 = lean_ptr_addr(x_357);
lean_dec(x_357);
x_373 = lean_ptr_addr(x_366);
x_374 = lean_usize_dec_eq(x_372, x_373);
if (x_374 == 0)
{
lean_object* x_375; 
lean_dec(x_367);
x_375 = l_Lean_Expr_forallE___override(x_355, x_360, x_366, x_358);
lean_ctor_set(x_364, 0, x_375);
return x_364;
}
else
{
uint8_t x_376; 
x_376 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_358, x_358);
if (x_376 == 0)
{
lean_object* x_377; 
lean_dec(x_367);
x_377 = l_Lean_Expr_forallE___override(x_355, x_360, x_366, x_358);
lean_ctor_set(x_364, 0, x_377);
return x_364;
}
else
{
lean_dec(x_366);
lean_dec(x_360);
lean_dec(x_355);
lean_ctor_set(x_364, 0, x_367);
return x_364;
}
}
}
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; size_t x_381; size_t x_382; uint8_t x_383; 
x_378 = lean_ctor_get(x_364, 0);
x_379 = lean_ctor_get(x_364, 1);
lean_inc(x_379);
lean_inc(x_378);
lean_dec(x_364);
lean_inc(x_357);
lean_inc(x_356);
lean_inc(x_355);
x_380 = l_Lean_Expr_forallE___override(x_355, x_356, x_357, x_358);
x_381 = lean_ptr_addr(x_356);
lean_dec(x_356);
x_382 = lean_ptr_addr(x_360);
x_383 = lean_usize_dec_eq(x_381, x_382);
if (x_383 == 0)
{
lean_object* x_384; lean_object* x_385; 
lean_dec(x_380);
lean_dec(x_357);
x_384 = l_Lean_Expr_forallE___override(x_355, x_360, x_378, x_358);
x_385 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_385, 0, x_384);
lean_ctor_set(x_385, 1, x_379);
return x_385;
}
else
{
size_t x_386; size_t x_387; uint8_t x_388; 
x_386 = lean_ptr_addr(x_357);
lean_dec(x_357);
x_387 = lean_ptr_addr(x_378);
x_388 = lean_usize_dec_eq(x_386, x_387);
if (x_388 == 0)
{
lean_object* x_389; lean_object* x_390; 
lean_dec(x_380);
x_389 = l_Lean_Expr_forallE___override(x_355, x_360, x_378, x_358);
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_389);
lean_ctor_set(x_390, 1, x_379);
return x_390;
}
else
{
uint8_t x_391; 
x_391 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_358, x_358);
if (x_391 == 0)
{
lean_object* x_392; lean_object* x_393; 
lean_dec(x_380);
x_392 = l_Lean_Expr_forallE___override(x_355, x_360, x_378, x_358);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_392);
lean_ctor_set(x_393, 1, x_379);
return x_393;
}
else
{
lean_object* x_394; 
lean_dec(x_378);
lean_dec(x_360);
lean_dec(x_355);
x_394 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_394, 0, x_380);
lean_ctor_set(x_394, 1, x_379);
return x_394;
}
}
}
}
}
else
{
uint8_t x_395; 
lean_dec(x_360);
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
x_395 = !lean_is_exclusive(x_364);
if (x_395 == 0)
{
return x_364;
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_396 = lean_ctor_get(x_364, 0);
x_397 = lean_ctor_get(x_364, 1);
lean_inc(x_397);
lean_inc(x_396);
lean_dec(x_364);
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_396);
lean_ctor_set(x_398, 1, x_397);
return x_398;
}
}
}
else
{
uint8_t x_399; 
lean_dec(x_357);
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_399 = !lean_is_exclusive(x_359);
if (x_399 == 0)
{
return x_359;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; 
x_400 = lean_ctor_get(x_359, 0);
x_401 = lean_ctor_get(x_359, 1);
lean_inc(x_401);
lean_inc(x_400);
lean_dec(x_359);
x_402 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_402, 0, x_400);
lean_ctor_set(x_402, 1, x_401);
return x_402;
}
}
}
case 8:
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; uint8_t x_408; lean_object* x_409; 
x_403 = lean_ctor_get(x_264, 1);
lean_inc(x_403);
lean_dec(x_264);
x_404 = lean_ctor_get(x_5, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_5, 1);
lean_inc(x_405);
x_406 = lean_ctor_get(x_5, 2);
lean_inc(x_406);
x_407 = lean_ctor_get(x_5, 3);
lean_inc(x_407);
x_408 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_405);
lean_inc(x_1);
x_409 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_405, x_6, x_7, x_8, x_9, x_10, x_11, x_403);
if (lean_obj_tag(x_409) == 0)
{
lean_object* x_410; lean_object* x_411; lean_object* x_412; 
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
lean_dec(x_409);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_406);
lean_inc(x_1);
x_412 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_406, x_6, x_7, x_8, x_9, x_10, x_11, x_411);
if (lean_obj_tag(x_412) == 0)
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_412, 1);
lean_inc(x_414);
lean_dec(x_412);
x_415 = lean_unsigned_to_nat(1u);
x_416 = lean_nat_add(x_6, x_415);
lean_dec(x_6);
lean_inc(x_407);
x_417 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_407, x_416, x_7, x_8, x_9, x_10, x_11, x_414);
if (lean_obj_tag(x_417) == 0)
{
uint8_t x_418; 
x_418 = !lean_is_exclusive(x_417);
if (x_418 == 0)
{
lean_object* x_419; lean_object* x_420; size_t x_421; size_t x_422; uint8_t x_423; 
x_419 = lean_ctor_get(x_417, 0);
lean_inc(x_407);
lean_inc(x_406);
lean_inc(x_405);
lean_inc(x_404);
x_420 = l_Lean_Expr_letE___override(x_404, x_405, x_406, x_407, x_408);
x_421 = lean_ptr_addr(x_405);
lean_dec(x_405);
x_422 = lean_ptr_addr(x_410);
x_423 = lean_usize_dec_eq(x_421, x_422);
if (x_423 == 0)
{
lean_object* x_424; 
lean_dec(x_420);
lean_dec(x_407);
lean_dec(x_406);
x_424 = l_Lean_Expr_letE___override(x_404, x_410, x_413, x_419, x_408);
lean_ctor_set(x_417, 0, x_424);
return x_417;
}
else
{
size_t x_425; size_t x_426; uint8_t x_427; 
x_425 = lean_ptr_addr(x_406);
lean_dec(x_406);
x_426 = lean_ptr_addr(x_413);
x_427 = lean_usize_dec_eq(x_425, x_426);
if (x_427 == 0)
{
lean_object* x_428; 
lean_dec(x_420);
lean_dec(x_407);
x_428 = l_Lean_Expr_letE___override(x_404, x_410, x_413, x_419, x_408);
lean_ctor_set(x_417, 0, x_428);
return x_417;
}
else
{
size_t x_429; size_t x_430; uint8_t x_431; 
x_429 = lean_ptr_addr(x_407);
lean_dec(x_407);
x_430 = lean_ptr_addr(x_419);
x_431 = lean_usize_dec_eq(x_429, x_430);
if (x_431 == 0)
{
lean_object* x_432; 
lean_dec(x_420);
x_432 = l_Lean_Expr_letE___override(x_404, x_410, x_413, x_419, x_408);
lean_ctor_set(x_417, 0, x_432);
return x_417;
}
else
{
lean_dec(x_419);
lean_dec(x_413);
lean_dec(x_410);
lean_dec(x_404);
lean_ctor_set(x_417, 0, x_420);
return x_417;
}
}
}
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; size_t x_436; size_t x_437; uint8_t x_438; 
x_433 = lean_ctor_get(x_417, 0);
x_434 = lean_ctor_get(x_417, 1);
lean_inc(x_434);
lean_inc(x_433);
lean_dec(x_417);
lean_inc(x_407);
lean_inc(x_406);
lean_inc(x_405);
lean_inc(x_404);
x_435 = l_Lean_Expr_letE___override(x_404, x_405, x_406, x_407, x_408);
x_436 = lean_ptr_addr(x_405);
lean_dec(x_405);
x_437 = lean_ptr_addr(x_410);
x_438 = lean_usize_dec_eq(x_436, x_437);
if (x_438 == 0)
{
lean_object* x_439; lean_object* x_440; 
lean_dec(x_435);
lean_dec(x_407);
lean_dec(x_406);
x_439 = l_Lean_Expr_letE___override(x_404, x_410, x_413, x_433, x_408);
x_440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_434);
return x_440;
}
else
{
size_t x_441; size_t x_442; uint8_t x_443; 
x_441 = lean_ptr_addr(x_406);
lean_dec(x_406);
x_442 = lean_ptr_addr(x_413);
x_443 = lean_usize_dec_eq(x_441, x_442);
if (x_443 == 0)
{
lean_object* x_444; lean_object* x_445; 
lean_dec(x_435);
lean_dec(x_407);
x_444 = l_Lean_Expr_letE___override(x_404, x_410, x_413, x_433, x_408);
x_445 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_445, 1, x_434);
return x_445;
}
else
{
size_t x_446; size_t x_447; uint8_t x_448; 
x_446 = lean_ptr_addr(x_407);
lean_dec(x_407);
x_447 = lean_ptr_addr(x_433);
x_448 = lean_usize_dec_eq(x_446, x_447);
if (x_448 == 0)
{
lean_object* x_449; lean_object* x_450; 
lean_dec(x_435);
x_449 = l_Lean_Expr_letE___override(x_404, x_410, x_413, x_433, x_408);
x_450 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_450, 0, x_449);
lean_ctor_set(x_450, 1, x_434);
return x_450;
}
else
{
lean_object* x_451; 
lean_dec(x_433);
lean_dec(x_413);
lean_dec(x_410);
lean_dec(x_404);
x_451 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_451, 0, x_435);
lean_ctor_set(x_451, 1, x_434);
return x_451;
}
}
}
}
}
else
{
uint8_t x_452; 
lean_dec(x_413);
lean_dec(x_410);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_404);
x_452 = !lean_is_exclusive(x_417);
if (x_452 == 0)
{
return x_417;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_417, 0);
x_454 = lean_ctor_get(x_417, 1);
lean_inc(x_454);
lean_inc(x_453);
lean_dec(x_417);
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
lean_dec(x_410);
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_456 = !lean_is_exclusive(x_412);
if (x_456 == 0)
{
return x_412;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_412, 0);
x_458 = lean_ctor_get(x_412, 1);
lean_inc(x_458);
lean_inc(x_457);
lean_dec(x_412);
x_459 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_459, 0, x_457);
lean_ctor_set(x_459, 1, x_458);
return x_459;
}
}
}
else
{
uint8_t x_460; 
lean_dec(x_407);
lean_dec(x_406);
lean_dec(x_405);
lean_dec(x_404);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_460 = !lean_is_exclusive(x_409);
if (x_460 == 0)
{
return x_409;
}
else
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; 
x_461 = lean_ctor_get(x_409, 0);
x_462 = lean_ctor_get(x_409, 1);
lean_inc(x_462);
lean_inc(x_461);
lean_dec(x_409);
x_463 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_463, 0, x_461);
lean_ctor_set(x_463, 1, x_462);
return x_463;
}
}
}
case 10:
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_464 = lean_ctor_get(x_264, 1);
lean_inc(x_464);
lean_dec(x_264);
x_465 = lean_ctor_get(x_5, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_5, 1);
lean_inc(x_466);
lean_inc(x_466);
x_467 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_466, x_6, x_7, x_8, x_9, x_10, x_11, x_464);
if (lean_obj_tag(x_467) == 0)
{
uint8_t x_468; 
x_468 = !lean_is_exclusive(x_467);
if (x_468 == 0)
{
lean_object* x_469; size_t x_470; size_t x_471; uint8_t x_472; 
x_469 = lean_ctor_get(x_467, 0);
x_470 = lean_ptr_addr(x_466);
lean_dec(x_466);
x_471 = lean_ptr_addr(x_469);
x_472 = lean_usize_dec_eq(x_470, x_471);
if (x_472 == 0)
{
lean_object* x_473; 
lean_dec(x_5);
x_473 = l_Lean_Expr_mdata___override(x_465, x_469);
lean_ctor_set(x_467, 0, x_473);
return x_467;
}
else
{
lean_dec(x_469);
lean_dec(x_465);
lean_ctor_set(x_467, 0, x_5);
return x_467;
}
}
else
{
lean_object* x_474; lean_object* x_475; size_t x_476; size_t x_477; uint8_t x_478; 
x_474 = lean_ctor_get(x_467, 0);
x_475 = lean_ctor_get(x_467, 1);
lean_inc(x_475);
lean_inc(x_474);
lean_dec(x_467);
x_476 = lean_ptr_addr(x_466);
lean_dec(x_466);
x_477 = lean_ptr_addr(x_474);
x_478 = lean_usize_dec_eq(x_476, x_477);
if (x_478 == 0)
{
lean_object* x_479; lean_object* x_480; 
lean_dec(x_5);
x_479 = l_Lean_Expr_mdata___override(x_465, x_474);
x_480 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_480, 0, x_479);
lean_ctor_set(x_480, 1, x_475);
return x_480;
}
else
{
lean_object* x_481; 
lean_dec(x_474);
lean_dec(x_465);
x_481 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_481, 0, x_5);
lean_ctor_set(x_481, 1, x_475);
return x_481;
}
}
}
else
{
uint8_t x_482; 
lean_dec(x_466);
lean_dec(x_465);
lean_dec(x_5);
x_482 = !lean_is_exclusive(x_467);
if (x_482 == 0)
{
return x_467;
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_483 = lean_ctor_get(x_467, 0);
x_484 = lean_ctor_get(x_467, 1);
lean_inc(x_484);
lean_inc(x_483);
lean_dec(x_467);
x_485 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_485, 0, x_483);
lean_ctor_set(x_485, 1, x_484);
return x_485;
}
}
}
case 11:
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_486 = lean_ctor_get(x_264, 1);
lean_inc(x_486);
lean_dec(x_264);
x_487 = lean_ctor_get(x_5, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_5, 1);
lean_inc(x_488);
x_489 = lean_ctor_get(x_5, 2);
lean_inc(x_489);
lean_inc(x_489);
x_490 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_489, x_6, x_7, x_8, x_9, x_10, x_11, x_486);
if (lean_obj_tag(x_490) == 0)
{
uint8_t x_491; 
x_491 = !lean_is_exclusive(x_490);
if (x_491 == 0)
{
lean_object* x_492; size_t x_493; size_t x_494; uint8_t x_495; 
x_492 = lean_ctor_get(x_490, 0);
x_493 = lean_ptr_addr(x_489);
lean_dec(x_489);
x_494 = lean_ptr_addr(x_492);
x_495 = lean_usize_dec_eq(x_493, x_494);
if (x_495 == 0)
{
lean_object* x_496; 
lean_dec(x_5);
x_496 = l_Lean_Expr_proj___override(x_487, x_488, x_492);
lean_ctor_set(x_490, 0, x_496);
return x_490;
}
else
{
lean_dec(x_492);
lean_dec(x_488);
lean_dec(x_487);
lean_ctor_set(x_490, 0, x_5);
return x_490;
}
}
else
{
lean_object* x_497; lean_object* x_498; size_t x_499; size_t x_500; uint8_t x_501; 
x_497 = lean_ctor_get(x_490, 0);
x_498 = lean_ctor_get(x_490, 1);
lean_inc(x_498);
lean_inc(x_497);
lean_dec(x_490);
x_499 = lean_ptr_addr(x_489);
lean_dec(x_489);
x_500 = lean_ptr_addr(x_497);
x_501 = lean_usize_dec_eq(x_499, x_500);
if (x_501 == 0)
{
lean_object* x_502; lean_object* x_503; 
lean_dec(x_5);
x_502 = l_Lean_Expr_proj___override(x_487, x_488, x_497);
x_503 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_503, 0, x_502);
lean_ctor_set(x_503, 1, x_498);
return x_503;
}
else
{
lean_object* x_504; 
lean_dec(x_497);
lean_dec(x_488);
lean_dec(x_487);
x_504 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_504, 0, x_5);
lean_ctor_set(x_504, 1, x_498);
return x_504;
}
}
}
else
{
uint8_t x_505; 
lean_dec(x_489);
lean_dec(x_488);
lean_dec(x_487);
lean_dec(x_5);
x_505 = !lean_is_exclusive(x_490);
if (x_505 == 0)
{
return x_490;
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
x_506 = lean_ctor_get(x_490, 0);
x_507 = lean_ctor_get(x_490, 1);
lean_inc(x_507);
lean_inc(x_506);
lean_dec(x_490);
x_508 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_508, 0, x_506);
lean_ctor_set(x_508, 1, x_507);
return x_508;
}
}
}
default: 
{
uint8_t x_509; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_509 = !lean_is_exclusive(x_264);
if (x_509 == 0)
{
lean_object* x_510; 
x_510 = lean_ctor_get(x_264, 0);
lean_dec(x_510);
lean_ctor_set(x_264, 0, x_5);
return x_264;
}
else
{
lean_object* x_511; lean_object* x_512; 
x_511 = lean_ctor_get(x_264, 1);
lean_inc(x_511);
lean_dec(x_264);
x_512 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_512, 0, x_5);
lean_ctor_set(x_512, 1, x_511);
return x_512;
}
}
}
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; uint8_t x_520; 
x_513 = lean_ctor_get(x_264, 1);
lean_inc(x_513);
lean_dec(x_264);
x_514 = lean_st_ref_get(x_7, x_513);
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_514, 1);
lean_inc(x_516);
lean_dec(x_514);
x_517 = lean_unsigned_to_nat(1u);
x_518 = lean_nat_add(x_515, x_517);
x_519 = lean_st_ref_set(x_7, x_518, x_516);
x_520 = !lean_is_exclusive(x_519);
if (x_520 == 0)
{
lean_object* x_521; lean_object* x_522; uint8_t x_523; 
x_521 = lean_ctor_get(x_519, 1);
x_522 = lean_ctor_get(x_519, 0);
lean_dec(x_522);
x_523 = l_Lean_Meta_Occurrences_contains(x_2, x_515);
lean_dec(x_515);
if (x_523 == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; uint8_t x_527; 
lean_free_object(x_519);
x_524 = lean_st_ref_take(x_9, x_521);
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_524, 1);
lean_inc(x_526);
lean_dec(x_524);
x_527 = !lean_is_exclusive(x_525);
if (x_527 == 0)
{
lean_object* x_528; lean_object* x_529; 
x_528 = lean_ctor_get(x_525, 0);
lean_dec(x_528);
lean_ctor_set(x_525, 0, x_263);
x_529 = lean_st_ref_set(x_9, x_525, x_526);
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; 
x_530 = lean_ctor_get(x_529, 1);
lean_inc(x_530);
lean_dec(x_529);
x_531 = lean_ctor_get(x_5, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_5, 1);
lean_inc(x_532);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_531);
lean_inc(x_1);
x_533 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_531, x_6, x_7, x_8, x_9, x_10, x_11, x_530);
if (lean_obj_tag(x_533) == 0)
{
lean_object* x_534; lean_object* x_535; lean_object* x_536; 
x_534 = lean_ctor_get(x_533, 0);
lean_inc(x_534);
x_535 = lean_ctor_get(x_533, 1);
lean_inc(x_535);
lean_dec(x_533);
lean_inc(x_532);
x_536 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_532, x_6, x_7, x_8, x_9, x_10, x_11, x_535);
if (lean_obj_tag(x_536) == 0)
{
uint8_t x_537; 
x_537 = !lean_is_exclusive(x_536);
if (x_537 == 0)
{
lean_object* x_538; size_t x_539; size_t x_540; uint8_t x_541; 
x_538 = lean_ctor_get(x_536, 0);
x_539 = lean_ptr_addr(x_531);
lean_dec(x_531);
x_540 = lean_ptr_addr(x_534);
x_541 = lean_usize_dec_eq(x_539, x_540);
if (x_541 == 0)
{
lean_object* x_542; 
lean_dec(x_532);
lean_dec(x_5);
x_542 = l_Lean_Expr_app___override(x_534, x_538);
lean_ctor_set(x_536, 0, x_542);
return x_536;
}
else
{
size_t x_543; size_t x_544; uint8_t x_545; 
x_543 = lean_ptr_addr(x_532);
lean_dec(x_532);
x_544 = lean_ptr_addr(x_538);
x_545 = lean_usize_dec_eq(x_543, x_544);
if (x_545 == 0)
{
lean_object* x_546; 
lean_dec(x_5);
x_546 = l_Lean_Expr_app___override(x_534, x_538);
lean_ctor_set(x_536, 0, x_546);
return x_536;
}
else
{
lean_dec(x_538);
lean_dec(x_534);
lean_ctor_set(x_536, 0, x_5);
return x_536;
}
}
}
else
{
lean_object* x_547; lean_object* x_548; size_t x_549; size_t x_550; uint8_t x_551; 
x_547 = lean_ctor_get(x_536, 0);
x_548 = lean_ctor_get(x_536, 1);
lean_inc(x_548);
lean_inc(x_547);
lean_dec(x_536);
x_549 = lean_ptr_addr(x_531);
lean_dec(x_531);
x_550 = lean_ptr_addr(x_534);
x_551 = lean_usize_dec_eq(x_549, x_550);
if (x_551 == 0)
{
lean_object* x_552; lean_object* x_553; 
lean_dec(x_532);
lean_dec(x_5);
x_552 = l_Lean_Expr_app___override(x_534, x_547);
x_553 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_553, 0, x_552);
lean_ctor_set(x_553, 1, x_548);
return x_553;
}
else
{
size_t x_554; size_t x_555; uint8_t x_556; 
x_554 = lean_ptr_addr(x_532);
lean_dec(x_532);
x_555 = lean_ptr_addr(x_547);
x_556 = lean_usize_dec_eq(x_554, x_555);
if (x_556 == 0)
{
lean_object* x_557; lean_object* x_558; 
lean_dec(x_5);
x_557 = l_Lean_Expr_app___override(x_534, x_547);
x_558 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_558, 0, x_557);
lean_ctor_set(x_558, 1, x_548);
return x_558;
}
else
{
lean_object* x_559; 
lean_dec(x_547);
lean_dec(x_534);
x_559 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_559, 0, x_5);
lean_ctor_set(x_559, 1, x_548);
return x_559;
}
}
}
}
else
{
uint8_t x_560; 
lean_dec(x_534);
lean_dec(x_532);
lean_dec(x_531);
lean_dec(x_5);
x_560 = !lean_is_exclusive(x_536);
if (x_560 == 0)
{
return x_536;
}
else
{
lean_object* x_561; lean_object* x_562; lean_object* x_563; 
x_561 = lean_ctor_get(x_536, 0);
x_562 = lean_ctor_get(x_536, 1);
lean_inc(x_562);
lean_inc(x_561);
lean_dec(x_536);
x_563 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_563, 0, x_561);
lean_ctor_set(x_563, 1, x_562);
return x_563;
}
}
}
else
{
uint8_t x_564; 
lean_dec(x_532);
lean_dec(x_531);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_564 = !lean_is_exclusive(x_533);
if (x_564 == 0)
{
return x_533;
}
else
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; 
x_565 = lean_ctor_get(x_533, 0);
x_566 = lean_ctor_get(x_533, 1);
lean_inc(x_566);
lean_inc(x_565);
lean_dec(x_533);
x_567 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_567, 0, x_565);
lean_ctor_set(x_567, 1, x_566);
return x_567;
}
}
}
case 6:
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; uint8_t x_572; lean_object* x_573; 
x_568 = lean_ctor_get(x_529, 1);
lean_inc(x_568);
lean_dec(x_529);
x_569 = lean_ctor_get(x_5, 0);
lean_inc(x_569);
x_570 = lean_ctor_get(x_5, 1);
lean_inc(x_570);
x_571 = lean_ctor_get(x_5, 2);
lean_inc(x_571);
x_572 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_570);
lean_inc(x_1);
x_573 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_570, x_6, x_7, x_8, x_9, x_10, x_11, x_568);
if (lean_obj_tag(x_573) == 0)
{
lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; 
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_573, 1);
lean_inc(x_575);
lean_dec(x_573);
x_576 = lean_nat_add(x_6, x_517);
lean_dec(x_6);
lean_inc(x_571);
x_577 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_571, x_576, x_7, x_8, x_9, x_10, x_11, x_575);
if (lean_obj_tag(x_577) == 0)
{
uint8_t x_578; 
x_578 = !lean_is_exclusive(x_577);
if (x_578 == 0)
{
lean_object* x_579; lean_object* x_580; size_t x_581; size_t x_582; uint8_t x_583; 
x_579 = lean_ctor_get(x_577, 0);
lean_inc(x_571);
lean_inc(x_570);
lean_inc(x_569);
x_580 = l_Lean_Expr_lam___override(x_569, x_570, x_571, x_572);
x_581 = lean_ptr_addr(x_570);
lean_dec(x_570);
x_582 = lean_ptr_addr(x_574);
x_583 = lean_usize_dec_eq(x_581, x_582);
if (x_583 == 0)
{
lean_object* x_584; 
lean_dec(x_580);
lean_dec(x_571);
x_584 = l_Lean_Expr_lam___override(x_569, x_574, x_579, x_572);
lean_ctor_set(x_577, 0, x_584);
return x_577;
}
else
{
size_t x_585; size_t x_586; uint8_t x_587; 
x_585 = lean_ptr_addr(x_571);
lean_dec(x_571);
x_586 = lean_ptr_addr(x_579);
x_587 = lean_usize_dec_eq(x_585, x_586);
if (x_587 == 0)
{
lean_object* x_588; 
lean_dec(x_580);
x_588 = l_Lean_Expr_lam___override(x_569, x_574, x_579, x_572);
lean_ctor_set(x_577, 0, x_588);
return x_577;
}
else
{
uint8_t x_589; 
x_589 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_572, x_572);
if (x_589 == 0)
{
lean_object* x_590; 
lean_dec(x_580);
x_590 = l_Lean_Expr_lam___override(x_569, x_574, x_579, x_572);
lean_ctor_set(x_577, 0, x_590);
return x_577;
}
else
{
lean_dec(x_579);
lean_dec(x_574);
lean_dec(x_569);
lean_ctor_set(x_577, 0, x_580);
return x_577;
}
}
}
}
else
{
lean_object* x_591; lean_object* x_592; lean_object* x_593; size_t x_594; size_t x_595; uint8_t x_596; 
x_591 = lean_ctor_get(x_577, 0);
x_592 = lean_ctor_get(x_577, 1);
lean_inc(x_592);
lean_inc(x_591);
lean_dec(x_577);
lean_inc(x_571);
lean_inc(x_570);
lean_inc(x_569);
x_593 = l_Lean_Expr_lam___override(x_569, x_570, x_571, x_572);
x_594 = lean_ptr_addr(x_570);
lean_dec(x_570);
x_595 = lean_ptr_addr(x_574);
x_596 = lean_usize_dec_eq(x_594, x_595);
if (x_596 == 0)
{
lean_object* x_597; lean_object* x_598; 
lean_dec(x_593);
lean_dec(x_571);
x_597 = l_Lean_Expr_lam___override(x_569, x_574, x_591, x_572);
x_598 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_598, 0, x_597);
lean_ctor_set(x_598, 1, x_592);
return x_598;
}
else
{
size_t x_599; size_t x_600; uint8_t x_601; 
x_599 = lean_ptr_addr(x_571);
lean_dec(x_571);
x_600 = lean_ptr_addr(x_591);
x_601 = lean_usize_dec_eq(x_599, x_600);
if (x_601 == 0)
{
lean_object* x_602; lean_object* x_603; 
lean_dec(x_593);
x_602 = l_Lean_Expr_lam___override(x_569, x_574, x_591, x_572);
x_603 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_603, 0, x_602);
lean_ctor_set(x_603, 1, x_592);
return x_603;
}
else
{
uint8_t x_604; 
x_604 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_572, x_572);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; 
lean_dec(x_593);
x_605 = l_Lean_Expr_lam___override(x_569, x_574, x_591, x_572);
x_606 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_606, 0, x_605);
lean_ctor_set(x_606, 1, x_592);
return x_606;
}
else
{
lean_object* x_607; 
lean_dec(x_591);
lean_dec(x_574);
lean_dec(x_569);
x_607 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_607, 0, x_593);
lean_ctor_set(x_607, 1, x_592);
return x_607;
}
}
}
}
}
else
{
uint8_t x_608; 
lean_dec(x_574);
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_569);
x_608 = !lean_is_exclusive(x_577);
if (x_608 == 0)
{
return x_577;
}
else
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; 
x_609 = lean_ctor_get(x_577, 0);
x_610 = lean_ctor_get(x_577, 1);
lean_inc(x_610);
lean_inc(x_609);
lean_dec(x_577);
x_611 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_611, 0, x_609);
lean_ctor_set(x_611, 1, x_610);
return x_611;
}
}
}
else
{
uint8_t x_612; 
lean_dec(x_571);
lean_dec(x_570);
lean_dec(x_569);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_612 = !lean_is_exclusive(x_573);
if (x_612 == 0)
{
return x_573;
}
else
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; 
x_613 = lean_ctor_get(x_573, 0);
x_614 = lean_ctor_get(x_573, 1);
lean_inc(x_614);
lean_inc(x_613);
lean_dec(x_573);
x_615 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_615, 0, x_613);
lean_ctor_set(x_615, 1, x_614);
return x_615;
}
}
}
case 7:
{
lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; uint8_t x_620; lean_object* x_621; 
x_616 = lean_ctor_get(x_529, 1);
lean_inc(x_616);
lean_dec(x_529);
x_617 = lean_ctor_get(x_5, 0);
lean_inc(x_617);
x_618 = lean_ctor_get(x_5, 1);
lean_inc(x_618);
x_619 = lean_ctor_get(x_5, 2);
lean_inc(x_619);
x_620 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_618);
lean_inc(x_1);
x_621 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_618, x_6, x_7, x_8, x_9, x_10, x_11, x_616);
if (lean_obj_tag(x_621) == 0)
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; 
x_622 = lean_ctor_get(x_621, 0);
lean_inc(x_622);
x_623 = lean_ctor_get(x_621, 1);
lean_inc(x_623);
lean_dec(x_621);
x_624 = lean_nat_add(x_6, x_517);
lean_dec(x_6);
lean_inc(x_619);
x_625 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_619, x_624, x_7, x_8, x_9, x_10, x_11, x_623);
if (lean_obj_tag(x_625) == 0)
{
uint8_t x_626; 
x_626 = !lean_is_exclusive(x_625);
if (x_626 == 0)
{
lean_object* x_627; lean_object* x_628; size_t x_629; size_t x_630; uint8_t x_631; 
x_627 = lean_ctor_get(x_625, 0);
lean_inc(x_619);
lean_inc(x_618);
lean_inc(x_617);
x_628 = l_Lean_Expr_forallE___override(x_617, x_618, x_619, x_620);
x_629 = lean_ptr_addr(x_618);
lean_dec(x_618);
x_630 = lean_ptr_addr(x_622);
x_631 = lean_usize_dec_eq(x_629, x_630);
if (x_631 == 0)
{
lean_object* x_632; 
lean_dec(x_628);
lean_dec(x_619);
x_632 = l_Lean_Expr_forallE___override(x_617, x_622, x_627, x_620);
lean_ctor_set(x_625, 0, x_632);
return x_625;
}
else
{
size_t x_633; size_t x_634; uint8_t x_635; 
x_633 = lean_ptr_addr(x_619);
lean_dec(x_619);
x_634 = lean_ptr_addr(x_627);
x_635 = lean_usize_dec_eq(x_633, x_634);
if (x_635 == 0)
{
lean_object* x_636; 
lean_dec(x_628);
x_636 = l_Lean_Expr_forallE___override(x_617, x_622, x_627, x_620);
lean_ctor_set(x_625, 0, x_636);
return x_625;
}
else
{
uint8_t x_637; 
x_637 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_620, x_620);
if (x_637 == 0)
{
lean_object* x_638; 
lean_dec(x_628);
x_638 = l_Lean_Expr_forallE___override(x_617, x_622, x_627, x_620);
lean_ctor_set(x_625, 0, x_638);
return x_625;
}
else
{
lean_dec(x_627);
lean_dec(x_622);
lean_dec(x_617);
lean_ctor_set(x_625, 0, x_628);
return x_625;
}
}
}
}
else
{
lean_object* x_639; lean_object* x_640; lean_object* x_641; size_t x_642; size_t x_643; uint8_t x_644; 
x_639 = lean_ctor_get(x_625, 0);
x_640 = lean_ctor_get(x_625, 1);
lean_inc(x_640);
lean_inc(x_639);
lean_dec(x_625);
lean_inc(x_619);
lean_inc(x_618);
lean_inc(x_617);
x_641 = l_Lean_Expr_forallE___override(x_617, x_618, x_619, x_620);
x_642 = lean_ptr_addr(x_618);
lean_dec(x_618);
x_643 = lean_ptr_addr(x_622);
x_644 = lean_usize_dec_eq(x_642, x_643);
if (x_644 == 0)
{
lean_object* x_645; lean_object* x_646; 
lean_dec(x_641);
lean_dec(x_619);
x_645 = l_Lean_Expr_forallE___override(x_617, x_622, x_639, x_620);
x_646 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_646, 0, x_645);
lean_ctor_set(x_646, 1, x_640);
return x_646;
}
else
{
size_t x_647; size_t x_648; uint8_t x_649; 
x_647 = lean_ptr_addr(x_619);
lean_dec(x_619);
x_648 = lean_ptr_addr(x_639);
x_649 = lean_usize_dec_eq(x_647, x_648);
if (x_649 == 0)
{
lean_object* x_650; lean_object* x_651; 
lean_dec(x_641);
x_650 = l_Lean_Expr_forallE___override(x_617, x_622, x_639, x_620);
x_651 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_651, 0, x_650);
lean_ctor_set(x_651, 1, x_640);
return x_651;
}
else
{
uint8_t x_652; 
x_652 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_620, x_620);
if (x_652 == 0)
{
lean_object* x_653; lean_object* x_654; 
lean_dec(x_641);
x_653 = l_Lean_Expr_forallE___override(x_617, x_622, x_639, x_620);
x_654 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_654, 0, x_653);
lean_ctor_set(x_654, 1, x_640);
return x_654;
}
else
{
lean_object* x_655; 
lean_dec(x_639);
lean_dec(x_622);
lean_dec(x_617);
x_655 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_655, 0, x_641);
lean_ctor_set(x_655, 1, x_640);
return x_655;
}
}
}
}
}
else
{
uint8_t x_656; 
lean_dec(x_622);
lean_dec(x_619);
lean_dec(x_618);
lean_dec(x_617);
x_656 = !lean_is_exclusive(x_625);
if (x_656 == 0)
{
return x_625;
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_657 = lean_ctor_get(x_625, 0);
x_658 = lean_ctor_get(x_625, 1);
lean_inc(x_658);
lean_inc(x_657);
lean_dec(x_625);
x_659 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_659, 0, x_657);
lean_ctor_set(x_659, 1, x_658);
return x_659;
}
}
}
else
{
uint8_t x_660; 
lean_dec(x_619);
lean_dec(x_618);
lean_dec(x_617);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_660 = !lean_is_exclusive(x_621);
if (x_660 == 0)
{
return x_621;
}
else
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_661 = lean_ctor_get(x_621, 0);
x_662 = lean_ctor_get(x_621, 1);
lean_inc(x_662);
lean_inc(x_661);
lean_dec(x_621);
x_663 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_663, 0, x_661);
lean_ctor_set(x_663, 1, x_662);
return x_663;
}
}
}
case 8:
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; uint8_t x_669; lean_object* x_670; 
x_664 = lean_ctor_get(x_529, 1);
lean_inc(x_664);
lean_dec(x_529);
x_665 = lean_ctor_get(x_5, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_5, 1);
lean_inc(x_666);
x_667 = lean_ctor_get(x_5, 2);
lean_inc(x_667);
x_668 = lean_ctor_get(x_5, 3);
lean_inc(x_668);
x_669 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_666);
lean_inc(x_1);
x_670 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_666, x_6, x_7, x_8, x_9, x_10, x_11, x_664);
if (lean_obj_tag(x_670) == 0)
{
lean_object* x_671; lean_object* x_672; lean_object* x_673; 
x_671 = lean_ctor_get(x_670, 0);
lean_inc(x_671);
x_672 = lean_ctor_get(x_670, 1);
lean_inc(x_672);
lean_dec(x_670);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_667);
lean_inc(x_1);
x_673 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_667, x_6, x_7, x_8, x_9, x_10, x_11, x_672);
if (lean_obj_tag(x_673) == 0)
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; 
x_674 = lean_ctor_get(x_673, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_673, 1);
lean_inc(x_675);
lean_dec(x_673);
x_676 = lean_nat_add(x_6, x_517);
lean_dec(x_6);
lean_inc(x_668);
x_677 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_668, x_676, x_7, x_8, x_9, x_10, x_11, x_675);
if (lean_obj_tag(x_677) == 0)
{
uint8_t x_678; 
x_678 = !lean_is_exclusive(x_677);
if (x_678 == 0)
{
lean_object* x_679; lean_object* x_680; size_t x_681; size_t x_682; uint8_t x_683; 
x_679 = lean_ctor_get(x_677, 0);
lean_inc(x_668);
lean_inc(x_667);
lean_inc(x_666);
lean_inc(x_665);
x_680 = l_Lean_Expr_letE___override(x_665, x_666, x_667, x_668, x_669);
x_681 = lean_ptr_addr(x_666);
lean_dec(x_666);
x_682 = lean_ptr_addr(x_671);
x_683 = lean_usize_dec_eq(x_681, x_682);
if (x_683 == 0)
{
lean_object* x_684; 
lean_dec(x_680);
lean_dec(x_668);
lean_dec(x_667);
x_684 = l_Lean_Expr_letE___override(x_665, x_671, x_674, x_679, x_669);
lean_ctor_set(x_677, 0, x_684);
return x_677;
}
else
{
size_t x_685; size_t x_686; uint8_t x_687; 
x_685 = lean_ptr_addr(x_667);
lean_dec(x_667);
x_686 = lean_ptr_addr(x_674);
x_687 = lean_usize_dec_eq(x_685, x_686);
if (x_687 == 0)
{
lean_object* x_688; 
lean_dec(x_680);
lean_dec(x_668);
x_688 = l_Lean_Expr_letE___override(x_665, x_671, x_674, x_679, x_669);
lean_ctor_set(x_677, 0, x_688);
return x_677;
}
else
{
size_t x_689; size_t x_690; uint8_t x_691; 
x_689 = lean_ptr_addr(x_668);
lean_dec(x_668);
x_690 = lean_ptr_addr(x_679);
x_691 = lean_usize_dec_eq(x_689, x_690);
if (x_691 == 0)
{
lean_object* x_692; 
lean_dec(x_680);
x_692 = l_Lean_Expr_letE___override(x_665, x_671, x_674, x_679, x_669);
lean_ctor_set(x_677, 0, x_692);
return x_677;
}
else
{
lean_dec(x_679);
lean_dec(x_674);
lean_dec(x_671);
lean_dec(x_665);
lean_ctor_set(x_677, 0, x_680);
return x_677;
}
}
}
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; size_t x_696; size_t x_697; uint8_t x_698; 
x_693 = lean_ctor_get(x_677, 0);
x_694 = lean_ctor_get(x_677, 1);
lean_inc(x_694);
lean_inc(x_693);
lean_dec(x_677);
lean_inc(x_668);
lean_inc(x_667);
lean_inc(x_666);
lean_inc(x_665);
x_695 = l_Lean_Expr_letE___override(x_665, x_666, x_667, x_668, x_669);
x_696 = lean_ptr_addr(x_666);
lean_dec(x_666);
x_697 = lean_ptr_addr(x_671);
x_698 = lean_usize_dec_eq(x_696, x_697);
if (x_698 == 0)
{
lean_object* x_699; lean_object* x_700; 
lean_dec(x_695);
lean_dec(x_668);
lean_dec(x_667);
x_699 = l_Lean_Expr_letE___override(x_665, x_671, x_674, x_693, x_669);
x_700 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_700, 0, x_699);
lean_ctor_set(x_700, 1, x_694);
return x_700;
}
else
{
size_t x_701; size_t x_702; uint8_t x_703; 
x_701 = lean_ptr_addr(x_667);
lean_dec(x_667);
x_702 = lean_ptr_addr(x_674);
x_703 = lean_usize_dec_eq(x_701, x_702);
if (x_703 == 0)
{
lean_object* x_704; lean_object* x_705; 
lean_dec(x_695);
lean_dec(x_668);
x_704 = l_Lean_Expr_letE___override(x_665, x_671, x_674, x_693, x_669);
x_705 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_705, 0, x_704);
lean_ctor_set(x_705, 1, x_694);
return x_705;
}
else
{
size_t x_706; size_t x_707; uint8_t x_708; 
x_706 = lean_ptr_addr(x_668);
lean_dec(x_668);
x_707 = lean_ptr_addr(x_693);
x_708 = lean_usize_dec_eq(x_706, x_707);
if (x_708 == 0)
{
lean_object* x_709; lean_object* x_710; 
lean_dec(x_695);
x_709 = l_Lean_Expr_letE___override(x_665, x_671, x_674, x_693, x_669);
x_710 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_710, 0, x_709);
lean_ctor_set(x_710, 1, x_694);
return x_710;
}
else
{
lean_object* x_711; 
lean_dec(x_693);
lean_dec(x_674);
lean_dec(x_671);
lean_dec(x_665);
x_711 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_711, 0, x_695);
lean_ctor_set(x_711, 1, x_694);
return x_711;
}
}
}
}
}
else
{
uint8_t x_712; 
lean_dec(x_674);
lean_dec(x_671);
lean_dec(x_668);
lean_dec(x_667);
lean_dec(x_666);
lean_dec(x_665);
x_712 = !lean_is_exclusive(x_677);
if (x_712 == 0)
{
return x_677;
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; 
x_713 = lean_ctor_get(x_677, 0);
x_714 = lean_ctor_get(x_677, 1);
lean_inc(x_714);
lean_inc(x_713);
lean_dec(x_677);
x_715 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_715, 0, x_713);
lean_ctor_set(x_715, 1, x_714);
return x_715;
}
}
}
else
{
uint8_t x_716; 
lean_dec(x_671);
lean_dec(x_668);
lean_dec(x_667);
lean_dec(x_666);
lean_dec(x_665);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_716 = !lean_is_exclusive(x_673);
if (x_716 == 0)
{
return x_673;
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_717 = lean_ctor_get(x_673, 0);
x_718 = lean_ctor_get(x_673, 1);
lean_inc(x_718);
lean_inc(x_717);
lean_dec(x_673);
x_719 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_719, 0, x_717);
lean_ctor_set(x_719, 1, x_718);
return x_719;
}
}
}
else
{
uint8_t x_720; 
lean_dec(x_668);
lean_dec(x_667);
lean_dec(x_666);
lean_dec(x_665);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_720 = !lean_is_exclusive(x_670);
if (x_720 == 0)
{
return x_670;
}
else
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; 
x_721 = lean_ctor_get(x_670, 0);
x_722 = lean_ctor_get(x_670, 1);
lean_inc(x_722);
lean_inc(x_721);
lean_dec(x_670);
x_723 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_723, 0, x_721);
lean_ctor_set(x_723, 1, x_722);
return x_723;
}
}
}
case 10:
{
lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
x_724 = lean_ctor_get(x_529, 1);
lean_inc(x_724);
lean_dec(x_529);
x_725 = lean_ctor_get(x_5, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_5, 1);
lean_inc(x_726);
lean_inc(x_726);
x_727 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_726, x_6, x_7, x_8, x_9, x_10, x_11, x_724);
if (lean_obj_tag(x_727) == 0)
{
uint8_t x_728; 
x_728 = !lean_is_exclusive(x_727);
if (x_728 == 0)
{
lean_object* x_729; size_t x_730; size_t x_731; uint8_t x_732; 
x_729 = lean_ctor_get(x_727, 0);
x_730 = lean_ptr_addr(x_726);
lean_dec(x_726);
x_731 = lean_ptr_addr(x_729);
x_732 = lean_usize_dec_eq(x_730, x_731);
if (x_732 == 0)
{
lean_object* x_733; 
lean_dec(x_5);
x_733 = l_Lean_Expr_mdata___override(x_725, x_729);
lean_ctor_set(x_727, 0, x_733);
return x_727;
}
else
{
lean_dec(x_729);
lean_dec(x_725);
lean_ctor_set(x_727, 0, x_5);
return x_727;
}
}
else
{
lean_object* x_734; lean_object* x_735; size_t x_736; size_t x_737; uint8_t x_738; 
x_734 = lean_ctor_get(x_727, 0);
x_735 = lean_ctor_get(x_727, 1);
lean_inc(x_735);
lean_inc(x_734);
lean_dec(x_727);
x_736 = lean_ptr_addr(x_726);
lean_dec(x_726);
x_737 = lean_ptr_addr(x_734);
x_738 = lean_usize_dec_eq(x_736, x_737);
if (x_738 == 0)
{
lean_object* x_739; lean_object* x_740; 
lean_dec(x_5);
x_739 = l_Lean_Expr_mdata___override(x_725, x_734);
x_740 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_740, 0, x_739);
lean_ctor_set(x_740, 1, x_735);
return x_740;
}
else
{
lean_object* x_741; 
lean_dec(x_734);
lean_dec(x_725);
x_741 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_741, 0, x_5);
lean_ctor_set(x_741, 1, x_735);
return x_741;
}
}
}
else
{
uint8_t x_742; 
lean_dec(x_726);
lean_dec(x_725);
lean_dec(x_5);
x_742 = !lean_is_exclusive(x_727);
if (x_742 == 0)
{
return x_727;
}
else
{
lean_object* x_743; lean_object* x_744; lean_object* x_745; 
x_743 = lean_ctor_get(x_727, 0);
x_744 = lean_ctor_get(x_727, 1);
lean_inc(x_744);
lean_inc(x_743);
lean_dec(x_727);
x_745 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_745, 0, x_743);
lean_ctor_set(x_745, 1, x_744);
return x_745;
}
}
}
case 11:
{
lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_746 = lean_ctor_get(x_529, 1);
lean_inc(x_746);
lean_dec(x_529);
x_747 = lean_ctor_get(x_5, 0);
lean_inc(x_747);
x_748 = lean_ctor_get(x_5, 1);
lean_inc(x_748);
x_749 = lean_ctor_get(x_5, 2);
lean_inc(x_749);
lean_inc(x_749);
x_750 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_749, x_6, x_7, x_8, x_9, x_10, x_11, x_746);
if (lean_obj_tag(x_750) == 0)
{
uint8_t x_751; 
x_751 = !lean_is_exclusive(x_750);
if (x_751 == 0)
{
lean_object* x_752; size_t x_753; size_t x_754; uint8_t x_755; 
x_752 = lean_ctor_get(x_750, 0);
x_753 = lean_ptr_addr(x_749);
lean_dec(x_749);
x_754 = lean_ptr_addr(x_752);
x_755 = lean_usize_dec_eq(x_753, x_754);
if (x_755 == 0)
{
lean_object* x_756; 
lean_dec(x_5);
x_756 = l_Lean_Expr_proj___override(x_747, x_748, x_752);
lean_ctor_set(x_750, 0, x_756);
return x_750;
}
else
{
lean_dec(x_752);
lean_dec(x_748);
lean_dec(x_747);
lean_ctor_set(x_750, 0, x_5);
return x_750;
}
}
else
{
lean_object* x_757; lean_object* x_758; size_t x_759; size_t x_760; uint8_t x_761; 
x_757 = lean_ctor_get(x_750, 0);
x_758 = lean_ctor_get(x_750, 1);
lean_inc(x_758);
lean_inc(x_757);
lean_dec(x_750);
x_759 = lean_ptr_addr(x_749);
lean_dec(x_749);
x_760 = lean_ptr_addr(x_757);
x_761 = lean_usize_dec_eq(x_759, x_760);
if (x_761 == 0)
{
lean_object* x_762; lean_object* x_763; 
lean_dec(x_5);
x_762 = l_Lean_Expr_proj___override(x_747, x_748, x_757);
x_763 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_763, 0, x_762);
lean_ctor_set(x_763, 1, x_758);
return x_763;
}
else
{
lean_object* x_764; 
lean_dec(x_757);
lean_dec(x_748);
lean_dec(x_747);
x_764 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_764, 0, x_5);
lean_ctor_set(x_764, 1, x_758);
return x_764;
}
}
}
else
{
uint8_t x_765; 
lean_dec(x_749);
lean_dec(x_748);
lean_dec(x_747);
lean_dec(x_5);
x_765 = !lean_is_exclusive(x_750);
if (x_765 == 0)
{
return x_750;
}
else
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; 
x_766 = lean_ctor_get(x_750, 0);
x_767 = lean_ctor_get(x_750, 1);
lean_inc(x_767);
lean_inc(x_766);
lean_dec(x_750);
x_768 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_768, 0, x_766);
lean_ctor_set(x_768, 1, x_767);
return x_768;
}
}
}
default: 
{
uint8_t x_769; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_769 = !lean_is_exclusive(x_529);
if (x_769 == 0)
{
lean_object* x_770; 
x_770 = lean_ctor_get(x_529, 0);
lean_dec(x_770);
lean_ctor_set(x_529, 0, x_5);
return x_529;
}
else
{
lean_object* x_771; lean_object* x_772; 
x_771 = lean_ctor_get(x_529, 1);
lean_inc(x_771);
lean_dec(x_529);
x_772 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_772, 0, x_5);
lean_ctor_set(x_772, 1, x_771);
return x_772;
}
}
}
}
else
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
x_773 = lean_ctor_get(x_525, 1);
x_774 = lean_ctor_get(x_525, 2);
x_775 = lean_ctor_get(x_525, 3);
x_776 = lean_ctor_get(x_525, 4);
lean_inc(x_776);
lean_inc(x_775);
lean_inc(x_774);
lean_inc(x_773);
lean_dec(x_525);
x_777 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_777, 0, x_263);
lean_ctor_set(x_777, 1, x_773);
lean_ctor_set(x_777, 2, x_774);
lean_ctor_set(x_777, 3, x_775);
lean_ctor_set(x_777, 4, x_776);
x_778 = lean_st_ref_set(x_9, x_777, x_526);
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
x_779 = lean_ctor_get(x_778, 1);
lean_inc(x_779);
lean_dec(x_778);
x_780 = lean_ctor_get(x_5, 0);
lean_inc(x_780);
x_781 = lean_ctor_get(x_5, 1);
lean_inc(x_781);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_780);
lean_inc(x_1);
x_782 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_780, x_6, x_7, x_8, x_9, x_10, x_11, x_779);
if (lean_obj_tag(x_782) == 0)
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; 
x_783 = lean_ctor_get(x_782, 0);
lean_inc(x_783);
x_784 = lean_ctor_get(x_782, 1);
lean_inc(x_784);
lean_dec(x_782);
lean_inc(x_781);
x_785 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_781, x_6, x_7, x_8, x_9, x_10, x_11, x_784);
if (lean_obj_tag(x_785) == 0)
{
lean_object* x_786; lean_object* x_787; lean_object* x_788; size_t x_789; size_t x_790; uint8_t x_791; 
x_786 = lean_ctor_get(x_785, 0);
lean_inc(x_786);
x_787 = lean_ctor_get(x_785, 1);
lean_inc(x_787);
if (lean_is_exclusive(x_785)) {
 lean_ctor_release(x_785, 0);
 lean_ctor_release(x_785, 1);
 x_788 = x_785;
} else {
 lean_dec_ref(x_785);
 x_788 = lean_box(0);
}
x_789 = lean_ptr_addr(x_780);
lean_dec(x_780);
x_790 = lean_ptr_addr(x_783);
x_791 = lean_usize_dec_eq(x_789, x_790);
if (x_791 == 0)
{
lean_object* x_792; lean_object* x_793; 
lean_dec(x_781);
lean_dec(x_5);
x_792 = l_Lean_Expr_app___override(x_783, x_786);
if (lean_is_scalar(x_788)) {
 x_793 = lean_alloc_ctor(0, 2, 0);
} else {
 x_793 = x_788;
}
lean_ctor_set(x_793, 0, x_792);
lean_ctor_set(x_793, 1, x_787);
return x_793;
}
else
{
size_t x_794; size_t x_795; uint8_t x_796; 
x_794 = lean_ptr_addr(x_781);
lean_dec(x_781);
x_795 = lean_ptr_addr(x_786);
x_796 = lean_usize_dec_eq(x_794, x_795);
if (x_796 == 0)
{
lean_object* x_797; lean_object* x_798; 
lean_dec(x_5);
x_797 = l_Lean_Expr_app___override(x_783, x_786);
if (lean_is_scalar(x_788)) {
 x_798 = lean_alloc_ctor(0, 2, 0);
} else {
 x_798 = x_788;
}
lean_ctor_set(x_798, 0, x_797);
lean_ctor_set(x_798, 1, x_787);
return x_798;
}
else
{
lean_object* x_799; 
lean_dec(x_786);
lean_dec(x_783);
if (lean_is_scalar(x_788)) {
 x_799 = lean_alloc_ctor(0, 2, 0);
} else {
 x_799 = x_788;
}
lean_ctor_set(x_799, 0, x_5);
lean_ctor_set(x_799, 1, x_787);
return x_799;
}
}
}
else
{
lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; 
lean_dec(x_783);
lean_dec(x_781);
lean_dec(x_780);
lean_dec(x_5);
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
lean_dec(x_781);
lean_dec(x_780);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
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
case 6:
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; lean_object* x_811; uint8_t x_812; lean_object* x_813; 
x_808 = lean_ctor_get(x_778, 1);
lean_inc(x_808);
lean_dec(x_778);
x_809 = lean_ctor_get(x_5, 0);
lean_inc(x_809);
x_810 = lean_ctor_get(x_5, 1);
lean_inc(x_810);
x_811 = lean_ctor_get(x_5, 2);
lean_inc(x_811);
x_812 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_810);
lean_inc(x_1);
x_813 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_810, x_6, x_7, x_8, x_9, x_10, x_11, x_808);
if (lean_obj_tag(x_813) == 0)
{
lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; 
x_814 = lean_ctor_get(x_813, 0);
lean_inc(x_814);
x_815 = lean_ctor_get(x_813, 1);
lean_inc(x_815);
lean_dec(x_813);
x_816 = lean_nat_add(x_6, x_517);
lean_dec(x_6);
lean_inc(x_811);
x_817 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_811, x_816, x_7, x_8, x_9, x_10, x_11, x_815);
if (lean_obj_tag(x_817) == 0)
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; size_t x_822; size_t x_823; uint8_t x_824; 
x_818 = lean_ctor_get(x_817, 0);
lean_inc(x_818);
x_819 = lean_ctor_get(x_817, 1);
lean_inc(x_819);
if (lean_is_exclusive(x_817)) {
 lean_ctor_release(x_817, 0);
 lean_ctor_release(x_817, 1);
 x_820 = x_817;
} else {
 lean_dec_ref(x_817);
 x_820 = lean_box(0);
}
lean_inc(x_811);
lean_inc(x_810);
lean_inc(x_809);
x_821 = l_Lean_Expr_lam___override(x_809, x_810, x_811, x_812);
x_822 = lean_ptr_addr(x_810);
lean_dec(x_810);
x_823 = lean_ptr_addr(x_814);
x_824 = lean_usize_dec_eq(x_822, x_823);
if (x_824 == 0)
{
lean_object* x_825; lean_object* x_826; 
lean_dec(x_821);
lean_dec(x_811);
x_825 = l_Lean_Expr_lam___override(x_809, x_814, x_818, x_812);
if (lean_is_scalar(x_820)) {
 x_826 = lean_alloc_ctor(0, 2, 0);
} else {
 x_826 = x_820;
}
lean_ctor_set(x_826, 0, x_825);
lean_ctor_set(x_826, 1, x_819);
return x_826;
}
else
{
size_t x_827; size_t x_828; uint8_t x_829; 
x_827 = lean_ptr_addr(x_811);
lean_dec(x_811);
x_828 = lean_ptr_addr(x_818);
x_829 = lean_usize_dec_eq(x_827, x_828);
if (x_829 == 0)
{
lean_object* x_830; lean_object* x_831; 
lean_dec(x_821);
x_830 = l_Lean_Expr_lam___override(x_809, x_814, x_818, x_812);
if (lean_is_scalar(x_820)) {
 x_831 = lean_alloc_ctor(0, 2, 0);
} else {
 x_831 = x_820;
}
lean_ctor_set(x_831, 0, x_830);
lean_ctor_set(x_831, 1, x_819);
return x_831;
}
else
{
uint8_t x_832; 
x_832 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_812, x_812);
if (x_832 == 0)
{
lean_object* x_833; lean_object* x_834; 
lean_dec(x_821);
x_833 = l_Lean_Expr_lam___override(x_809, x_814, x_818, x_812);
if (lean_is_scalar(x_820)) {
 x_834 = lean_alloc_ctor(0, 2, 0);
} else {
 x_834 = x_820;
}
lean_ctor_set(x_834, 0, x_833);
lean_ctor_set(x_834, 1, x_819);
return x_834;
}
else
{
lean_object* x_835; 
lean_dec(x_818);
lean_dec(x_814);
lean_dec(x_809);
if (lean_is_scalar(x_820)) {
 x_835 = lean_alloc_ctor(0, 2, 0);
} else {
 x_835 = x_820;
}
lean_ctor_set(x_835, 0, x_821);
lean_ctor_set(x_835, 1, x_819);
return x_835;
}
}
}
}
else
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; 
lean_dec(x_814);
lean_dec(x_811);
lean_dec(x_810);
lean_dec(x_809);
x_836 = lean_ctor_get(x_817, 0);
lean_inc(x_836);
x_837 = lean_ctor_get(x_817, 1);
lean_inc(x_837);
if (lean_is_exclusive(x_817)) {
 lean_ctor_release(x_817, 0);
 lean_ctor_release(x_817, 1);
 x_838 = x_817;
} else {
 lean_dec_ref(x_817);
 x_838 = lean_box(0);
}
if (lean_is_scalar(x_838)) {
 x_839 = lean_alloc_ctor(1, 2, 0);
} else {
 x_839 = x_838;
}
lean_ctor_set(x_839, 0, x_836);
lean_ctor_set(x_839, 1, x_837);
return x_839;
}
}
else
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; 
lean_dec(x_811);
lean_dec(x_810);
lean_dec(x_809);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_840 = lean_ctor_get(x_813, 0);
lean_inc(x_840);
x_841 = lean_ctor_get(x_813, 1);
lean_inc(x_841);
if (lean_is_exclusive(x_813)) {
 lean_ctor_release(x_813, 0);
 lean_ctor_release(x_813, 1);
 x_842 = x_813;
} else {
 lean_dec_ref(x_813);
 x_842 = lean_box(0);
}
if (lean_is_scalar(x_842)) {
 x_843 = lean_alloc_ctor(1, 2, 0);
} else {
 x_843 = x_842;
}
lean_ctor_set(x_843, 0, x_840);
lean_ctor_set(x_843, 1, x_841);
return x_843;
}
}
case 7:
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; uint8_t x_848; lean_object* x_849; 
x_844 = lean_ctor_get(x_778, 1);
lean_inc(x_844);
lean_dec(x_778);
x_845 = lean_ctor_get(x_5, 0);
lean_inc(x_845);
x_846 = lean_ctor_get(x_5, 1);
lean_inc(x_846);
x_847 = lean_ctor_get(x_5, 2);
lean_inc(x_847);
x_848 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_846);
lean_inc(x_1);
x_849 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_846, x_6, x_7, x_8, x_9, x_10, x_11, x_844);
if (lean_obj_tag(x_849) == 0)
{
lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; 
x_850 = lean_ctor_get(x_849, 0);
lean_inc(x_850);
x_851 = lean_ctor_get(x_849, 1);
lean_inc(x_851);
lean_dec(x_849);
x_852 = lean_nat_add(x_6, x_517);
lean_dec(x_6);
lean_inc(x_847);
x_853 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_847, x_852, x_7, x_8, x_9, x_10, x_11, x_851);
if (lean_obj_tag(x_853) == 0)
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; size_t x_858; size_t x_859; uint8_t x_860; 
x_854 = lean_ctor_get(x_853, 0);
lean_inc(x_854);
x_855 = lean_ctor_get(x_853, 1);
lean_inc(x_855);
if (lean_is_exclusive(x_853)) {
 lean_ctor_release(x_853, 0);
 lean_ctor_release(x_853, 1);
 x_856 = x_853;
} else {
 lean_dec_ref(x_853);
 x_856 = lean_box(0);
}
lean_inc(x_847);
lean_inc(x_846);
lean_inc(x_845);
x_857 = l_Lean_Expr_forallE___override(x_845, x_846, x_847, x_848);
x_858 = lean_ptr_addr(x_846);
lean_dec(x_846);
x_859 = lean_ptr_addr(x_850);
x_860 = lean_usize_dec_eq(x_858, x_859);
if (x_860 == 0)
{
lean_object* x_861; lean_object* x_862; 
lean_dec(x_857);
lean_dec(x_847);
x_861 = l_Lean_Expr_forallE___override(x_845, x_850, x_854, x_848);
if (lean_is_scalar(x_856)) {
 x_862 = lean_alloc_ctor(0, 2, 0);
} else {
 x_862 = x_856;
}
lean_ctor_set(x_862, 0, x_861);
lean_ctor_set(x_862, 1, x_855);
return x_862;
}
else
{
size_t x_863; size_t x_864; uint8_t x_865; 
x_863 = lean_ptr_addr(x_847);
lean_dec(x_847);
x_864 = lean_ptr_addr(x_854);
x_865 = lean_usize_dec_eq(x_863, x_864);
if (x_865 == 0)
{
lean_object* x_866; lean_object* x_867; 
lean_dec(x_857);
x_866 = l_Lean_Expr_forallE___override(x_845, x_850, x_854, x_848);
if (lean_is_scalar(x_856)) {
 x_867 = lean_alloc_ctor(0, 2, 0);
} else {
 x_867 = x_856;
}
lean_ctor_set(x_867, 0, x_866);
lean_ctor_set(x_867, 1, x_855);
return x_867;
}
else
{
uint8_t x_868; 
x_868 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_848, x_848);
if (x_868 == 0)
{
lean_object* x_869; lean_object* x_870; 
lean_dec(x_857);
x_869 = l_Lean_Expr_forallE___override(x_845, x_850, x_854, x_848);
if (lean_is_scalar(x_856)) {
 x_870 = lean_alloc_ctor(0, 2, 0);
} else {
 x_870 = x_856;
}
lean_ctor_set(x_870, 0, x_869);
lean_ctor_set(x_870, 1, x_855);
return x_870;
}
else
{
lean_object* x_871; 
lean_dec(x_854);
lean_dec(x_850);
lean_dec(x_845);
if (lean_is_scalar(x_856)) {
 x_871 = lean_alloc_ctor(0, 2, 0);
} else {
 x_871 = x_856;
}
lean_ctor_set(x_871, 0, x_857);
lean_ctor_set(x_871, 1, x_855);
return x_871;
}
}
}
}
else
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; 
lean_dec(x_850);
lean_dec(x_847);
lean_dec(x_846);
lean_dec(x_845);
x_872 = lean_ctor_get(x_853, 0);
lean_inc(x_872);
x_873 = lean_ctor_get(x_853, 1);
lean_inc(x_873);
if (lean_is_exclusive(x_853)) {
 lean_ctor_release(x_853, 0);
 lean_ctor_release(x_853, 1);
 x_874 = x_853;
} else {
 lean_dec_ref(x_853);
 x_874 = lean_box(0);
}
if (lean_is_scalar(x_874)) {
 x_875 = lean_alloc_ctor(1, 2, 0);
} else {
 x_875 = x_874;
}
lean_ctor_set(x_875, 0, x_872);
lean_ctor_set(x_875, 1, x_873);
return x_875;
}
}
else
{
lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; 
lean_dec(x_847);
lean_dec(x_846);
lean_dec(x_845);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_876 = lean_ctor_get(x_849, 0);
lean_inc(x_876);
x_877 = lean_ctor_get(x_849, 1);
lean_inc(x_877);
if (lean_is_exclusive(x_849)) {
 lean_ctor_release(x_849, 0);
 lean_ctor_release(x_849, 1);
 x_878 = x_849;
} else {
 lean_dec_ref(x_849);
 x_878 = lean_box(0);
}
if (lean_is_scalar(x_878)) {
 x_879 = lean_alloc_ctor(1, 2, 0);
} else {
 x_879 = x_878;
}
lean_ctor_set(x_879, 0, x_876);
lean_ctor_set(x_879, 1, x_877);
return x_879;
}
}
case 8:
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; uint8_t x_885; lean_object* x_886; 
x_880 = lean_ctor_get(x_778, 1);
lean_inc(x_880);
lean_dec(x_778);
x_881 = lean_ctor_get(x_5, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_5, 1);
lean_inc(x_882);
x_883 = lean_ctor_get(x_5, 2);
lean_inc(x_883);
x_884 = lean_ctor_get(x_5, 3);
lean_inc(x_884);
x_885 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_882);
lean_inc(x_1);
x_886 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_882, x_6, x_7, x_8, x_9, x_10, x_11, x_880);
if (lean_obj_tag(x_886) == 0)
{
lean_object* x_887; lean_object* x_888; lean_object* x_889; 
x_887 = lean_ctor_get(x_886, 0);
lean_inc(x_887);
x_888 = lean_ctor_get(x_886, 1);
lean_inc(x_888);
lean_dec(x_886);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_883);
lean_inc(x_1);
x_889 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_883, x_6, x_7, x_8, x_9, x_10, x_11, x_888);
if (lean_obj_tag(x_889) == 0)
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; 
x_890 = lean_ctor_get(x_889, 0);
lean_inc(x_890);
x_891 = lean_ctor_get(x_889, 1);
lean_inc(x_891);
lean_dec(x_889);
x_892 = lean_nat_add(x_6, x_517);
lean_dec(x_6);
lean_inc(x_884);
x_893 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_884, x_892, x_7, x_8, x_9, x_10, x_11, x_891);
if (lean_obj_tag(x_893) == 0)
{
lean_object* x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; size_t x_898; size_t x_899; uint8_t x_900; 
x_894 = lean_ctor_get(x_893, 0);
lean_inc(x_894);
x_895 = lean_ctor_get(x_893, 1);
lean_inc(x_895);
if (lean_is_exclusive(x_893)) {
 lean_ctor_release(x_893, 0);
 lean_ctor_release(x_893, 1);
 x_896 = x_893;
} else {
 lean_dec_ref(x_893);
 x_896 = lean_box(0);
}
lean_inc(x_884);
lean_inc(x_883);
lean_inc(x_882);
lean_inc(x_881);
x_897 = l_Lean_Expr_letE___override(x_881, x_882, x_883, x_884, x_885);
x_898 = lean_ptr_addr(x_882);
lean_dec(x_882);
x_899 = lean_ptr_addr(x_887);
x_900 = lean_usize_dec_eq(x_898, x_899);
if (x_900 == 0)
{
lean_object* x_901; lean_object* x_902; 
lean_dec(x_897);
lean_dec(x_884);
lean_dec(x_883);
x_901 = l_Lean_Expr_letE___override(x_881, x_887, x_890, x_894, x_885);
if (lean_is_scalar(x_896)) {
 x_902 = lean_alloc_ctor(0, 2, 0);
} else {
 x_902 = x_896;
}
lean_ctor_set(x_902, 0, x_901);
lean_ctor_set(x_902, 1, x_895);
return x_902;
}
else
{
size_t x_903; size_t x_904; uint8_t x_905; 
x_903 = lean_ptr_addr(x_883);
lean_dec(x_883);
x_904 = lean_ptr_addr(x_890);
x_905 = lean_usize_dec_eq(x_903, x_904);
if (x_905 == 0)
{
lean_object* x_906; lean_object* x_907; 
lean_dec(x_897);
lean_dec(x_884);
x_906 = l_Lean_Expr_letE___override(x_881, x_887, x_890, x_894, x_885);
if (lean_is_scalar(x_896)) {
 x_907 = lean_alloc_ctor(0, 2, 0);
} else {
 x_907 = x_896;
}
lean_ctor_set(x_907, 0, x_906);
lean_ctor_set(x_907, 1, x_895);
return x_907;
}
else
{
size_t x_908; size_t x_909; uint8_t x_910; 
x_908 = lean_ptr_addr(x_884);
lean_dec(x_884);
x_909 = lean_ptr_addr(x_894);
x_910 = lean_usize_dec_eq(x_908, x_909);
if (x_910 == 0)
{
lean_object* x_911; lean_object* x_912; 
lean_dec(x_897);
x_911 = l_Lean_Expr_letE___override(x_881, x_887, x_890, x_894, x_885);
if (lean_is_scalar(x_896)) {
 x_912 = lean_alloc_ctor(0, 2, 0);
} else {
 x_912 = x_896;
}
lean_ctor_set(x_912, 0, x_911);
lean_ctor_set(x_912, 1, x_895);
return x_912;
}
else
{
lean_object* x_913; 
lean_dec(x_894);
lean_dec(x_890);
lean_dec(x_887);
lean_dec(x_881);
if (lean_is_scalar(x_896)) {
 x_913 = lean_alloc_ctor(0, 2, 0);
} else {
 x_913 = x_896;
}
lean_ctor_set(x_913, 0, x_897);
lean_ctor_set(x_913, 1, x_895);
return x_913;
}
}
}
}
else
{
lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; 
lean_dec(x_890);
lean_dec(x_887);
lean_dec(x_884);
lean_dec(x_883);
lean_dec(x_882);
lean_dec(x_881);
x_914 = lean_ctor_get(x_893, 0);
lean_inc(x_914);
x_915 = lean_ctor_get(x_893, 1);
lean_inc(x_915);
if (lean_is_exclusive(x_893)) {
 lean_ctor_release(x_893, 0);
 lean_ctor_release(x_893, 1);
 x_916 = x_893;
} else {
 lean_dec_ref(x_893);
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
else
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; 
lean_dec(x_887);
lean_dec(x_884);
lean_dec(x_883);
lean_dec(x_882);
lean_dec(x_881);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_918 = lean_ctor_get(x_889, 0);
lean_inc(x_918);
x_919 = lean_ctor_get(x_889, 1);
lean_inc(x_919);
if (lean_is_exclusive(x_889)) {
 lean_ctor_release(x_889, 0);
 lean_ctor_release(x_889, 1);
 x_920 = x_889;
} else {
 lean_dec_ref(x_889);
 x_920 = lean_box(0);
}
if (lean_is_scalar(x_920)) {
 x_921 = lean_alloc_ctor(1, 2, 0);
} else {
 x_921 = x_920;
}
lean_ctor_set(x_921, 0, x_918);
lean_ctor_set(x_921, 1, x_919);
return x_921;
}
}
else
{
lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; 
lean_dec(x_884);
lean_dec(x_883);
lean_dec(x_882);
lean_dec(x_881);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_922 = lean_ctor_get(x_886, 0);
lean_inc(x_922);
x_923 = lean_ctor_get(x_886, 1);
lean_inc(x_923);
if (lean_is_exclusive(x_886)) {
 lean_ctor_release(x_886, 0);
 lean_ctor_release(x_886, 1);
 x_924 = x_886;
} else {
 lean_dec_ref(x_886);
 x_924 = lean_box(0);
}
if (lean_is_scalar(x_924)) {
 x_925 = lean_alloc_ctor(1, 2, 0);
} else {
 x_925 = x_924;
}
lean_ctor_set(x_925, 0, x_922);
lean_ctor_set(x_925, 1, x_923);
return x_925;
}
}
case 10:
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; 
x_926 = lean_ctor_get(x_778, 1);
lean_inc(x_926);
lean_dec(x_778);
x_927 = lean_ctor_get(x_5, 0);
lean_inc(x_927);
x_928 = lean_ctor_get(x_5, 1);
lean_inc(x_928);
lean_inc(x_928);
x_929 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_928, x_6, x_7, x_8, x_9, x_10, x_11, x_926);
if (lean_obj_tag(x_929) == 0)
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; size_t x_933; size_t x_934; uint8_t x_935; 
x_930 = lean_ctor_get(x_929, 0);
lean_inc(x_930);
x_931 = lean_ctor_get(x_929, 1);
lean_inc(x_931);
if (lean_is_exclusive(x_929)) {
 lean_ctor_release(x_929, 0);
 lean_ctor_release(x_929, 1);
 x_932 = x_929;
} else {
 lean_dec_ref(x_929);
 x_932 = lean_box(0);
}
x_933 = lean_ptr_addr(x_928);
lean_dec(x_928);
x_934 = lean_ptr_addr(x_930);
x_935 = lean_usize_dec_eq(x_933, x_934);
if (x_935 == 0)
{
lean_object* x_936; lean_object* x_937; 
lean_dec(x_5);
x_936 = l_Lean_Expr_mdata___override(x_927, x_930);
if (lean_is_scalar(x_932)) {
 x_937 = lean_alloc_ctor(0, 2, 0);
} else {
 x_937 = x_932;
}
lean_ctor_set(x_937, 0, x_936);
lean_ctor_set(x_937, 1, x_931);
return x_937;
}
else
{
lean_object* x_938; 
lean_dec(x_930);
lean_dec(x_927);
if (lean_is_scalar(x_932)) {
 x_938 = lean_alloc_ctor(0, 2, 0);
} else {
 x_938 = x_932;
}
lean_ctor_set(x_938, 0, x_5);
lean_ctor_set(x_938, 1, x_931);
return x_938;
}
}
else
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; 
lean_dec(x_928);
lean_dec(x_927);
lean_dec(x_5);
x_939 = lean_ctor_get(x_929, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_929, 1);
lean_inc(x_940);
if (lean_is_exclusive(x_929)) {
 lean_ctor_release(x_929, 0);
 lean_ctor_release(x_929, 1);
 x_941 = x_929;
} else {
 lean_dec_ref(x_929);
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
case 11:
{
lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; 
x_943 = lean_ctor_get(x_778, 1);
lean_inc(x_943);
lean_dec(x_778);
x_944 = lean_ctor_get(x_5, 0);
lean_inc(x_944);
x_945 = lean_ctor_get(x_5, 1);
lean_inc(x_945);
x_946 = lean_ctor_get(x_5, 2);
lean_inc(x_946);
lean_inc(x_946);
x_947 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_946, x_6, x_7, x_8, x_9, x_10, x_11, x_943);
if (lean_obj_tag(x_947) == 0)
{
lean_object* x_948; lean_object* x_949; lean_object* x_950; size_t x_951; size_t x_952; uint8_t x_953; 
x_948 = lean_ctor_get(x_947, 0);
lean_inc(x_948);
x_949 = lean_ctor_get(x_947, 1);
lean_inc(x_949);
if (lean_is_exclusive(x_947)) {
 lean_ctor_release(x_947, 0);
 lean_ctor_release(x_947, 1);
 x_950 = x_947;
} else {
 lean_dec_ref(x_947);
 x_950 = lean_box(0);
}
x_951 = lean_ptr_addr(x_946);
lean_dec(x_946);
x_952 = lean_ptr_addr(x_948);
x_953 = lean_usize_dec_eq(x_951, x_952);
if (x_953 == 0)
{
lean_object* x_954; lean_object* x_955; 
lean_dec(x_5);
x_954 = l_Lean_Expr_proj___override(x_944, x_945, x_948);
if (lean_is_scalar(x_950)) {
 x_955 = lean_alloc_ctor(0, 2, 0);
} else {
 x_955 = x_950;
}
lean_ctor_set(x_955, 0, x_954);
lean_ctor_set(x_955, 1, x_949);
return x_955;
}
else
{
lean_object* x_956; 
lean_dec(x_948);
lean_dec(x_945);
lean_dec(x_944);
if (lean_is_scalar(x_950)) {
 x_956 = lean_alloc_ctor(0, 2, 0);
} else {
 x_956 = x_950;
}
lean_ctor_set(x_956, 0, x_5);
lean_ctor_set(x_956, 1, x_949);
return x_956;
}
}
else
{
lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; 
lean_dec(x_946);
lean_dec(x_945);
lean_dec(x_944);
lean_dec(x_5);
x_957 = lean_ctor_get(x_947, 0);
lean_inc(x_957);
x_958 = lean_ctor_get(x_947, 1);
lean_inc(x_958);
if (lean_is_exclusive(x_947)) {
 lean_ctor_release(x_947, 0);
 lean_ctor_release(x_947, 1);
 x_959 = x_947;
} else {
 lean_dec_ref(x_947);
 x_959 = lean_box(0);
}
if (lean_is_scalar(x_959)) {
 x_960 = lean_alloc_ctor(1, 2, 0);
} else {
 x_960 = x_959;
}
lean_ctor_set(x_960, 0, x_957);
lean_ctor_set(x_960, 1, x_958);
return x_960;
}
}
default: 
{
lean_object* x_961; lean_object* x_962; lean_object* x_963; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_961 = lean_ctor_get(x_778, 1);
lean_inc(x_961);
if (lean_is_exclusive(x_778)) {
 lean_ctor_release(x_778, 0);
 lean_ctor_release(x_778, 1);
 x_962 = x_778;
} else {
 lean_dec_ref(x_778);
 x_962 = lean_box(0);
}
if (lean_is_scalar(x_962)) {
 x_963 = lean_alloc_ctor(0, 2, 0);
} else {
 x_963 = x_962;
}
lean_ctor_set(x_963, 0, x_5);
lean_ctor_set(x_963, 1, x_961);
return x_963;
}
}
}
}
else
{
lean_object* x_964; 
lean_dec(x_263);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_964 = l_Lean_Expr_bvar___override(x_6);
lean_ctor_set(x_519, 0, x_964);
return x_519;
}
}
else
{
lean_object* x_965; uint8_t x_966; 
x_965 = lean_ctor_get(x_519, 1);
lean_inc(x_965);
lean_dec(x_519);
x_966 = l_Lean_Meta_Occurrences_contains(x_2, x_515);
lean_dec(x_515);
if (x_966 == 0)
{
lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; 
x_967 = lean_st_ref_take(x_9, x_965);
x_968 = lean_ctor_get(x_967, 0);
lean_inc(x_968);
x_969 = lean_ctor_get(x_967, 1);
lean_inc(x_969);
lean_dec(x_967);
x_970 = lean_ctor_get(x_968, 1);
lean_inc(x_970);
x_971 = lean_ctor_get(x_968, 2);
lean_inc(x_971);
x_972 = lean_ctor_get(x_968, 3);
lean_inc(x_972);
x_973 = lean_ctor_get(x_968, 4);
lean_inc(x_973);
if (lean_is_exclusive(x_968)) {
 lean_ctor_release(x_968, 0);
 lean_ctor_release(x_968, 1);
 lean_ctor_release(x_968, 2);
 lean_ctor_release(x_968, 3);
 lean_ctor_release(x_968, 4);
 x_974 = x_968;
} else {
 lean_dec_ref(x_968);
 x_974 = lean_box(0);
}
if (lean_is_scalar(x_974)) {
 x_975 = lean_alloc_ctor(0, 5, 0);
} else {
 x_975 = x_974;
}
lean_ctor_set(x_975, 0, x_263);
lean_ctor_set(x_975, 1, x_970);
lean_ctor_set(x_975, 2, x_971);
lean_ctor_set(x_975, 3, x_972);
lean_ctor_set(x_975, 4, x_973);
x_976 = lean_st_ref_set(x_9, x_975, x_969);
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; 
x_977 = lean_ctor_get(x_976, 1);
lean_inc(x_977);
lean_dec(x_976);
x_978 = lean_ctor_get(x_5, 0);
lean_inc(x_978);
x_979 = lean_ctor_get(x_5, 1);
lean_inc(x_979);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_978);
lean_inc(x_1);
x_980 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_978, x_6, x_7, x_8, x_9, x_10, x_11, x_977);
if (lean_obj_tag(x_980) == 0)
{
lean_object* x_981; lean_object* x_982; lean_object* x_983; 
x_981 = lean_ctor_get(x_980, 0);
lean_inc(x_981);
x_982 = lean_ctor_get(x_980, 1);
lean_inc(x_982);
lean_dec(x_980);
lean_inc(x_979);
x_983 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_979, x_6, x_7, x_8, x_9, x_10, x_11, x_982);
if (lean_obj_tag(x_983) == 0)
{
lean_object* x_984; lean_object* x_985; lean_object* x_986; size_t x_987; size_t x_988; uint8_t x_989; 
x_984 = lean_ctor_get(x_983, 0);
lean_inc(x_984);
x_985 = lean_ctor_get(x_983, 1);
lean_inc(x_985);
if (lean_is_exclusive(x_983)) {
 lean_ctor_release(x_983, 0);
 lean_ctor_release(x_983, 1);
 x_986 = x_983;
} else {
 lean_dec_ref(x_983);
 x_986 = lean_box(0);
}
x_987 = lean_ptr_addr(x_978);
lean_dec(x_978);
x_988 = lean_ptr_addr(x_981);
x_989 = lean_usize_dec_eq(x_987, x_988);
if (x_989 == 0)
{
lean_object* x_990; lean_object* x_991; 
lean_dec(x_979);
lean_dec(x_5);
x_990 = l_Lean_Expr_app___override(x_981, x_984);
if (lean_is_scalar(x_986)) {
 x_991 = lean_alloc_ctor(0, 2, 0);
} else {
 x_991 = x_986;
}
lean_ctor_set(x_991, 0, x_990);
lean_ctor_set(x_991, 1, x_985);
return x_991;
}
else
{
size_t x_992; size_t x_993; uint8_t x_994; 
x_992 = lean_ptr_addr(x_979);
lean_dec(x_979);
x_993 = lean_ptr_addr(x_984);
x_994 = lean_usize_dec_eq(x_992, x_993);
if (x_994 == 0)
{
lean_object* x_995; lean_object* x_996; 
lean_dec(x_5);
x_995 = l_Lean_Expr_app___override(x_981, x_984);
if (lean_is_scalar(x_986)) {
 x_996 = lean_alloc_ctor(0, 2, 0);
} else {
 x_996 = x_986;
}
lean_ctor_set(x_996, 0, x_995);
lean_ctor_set(x_996, 1, x_985);
return x_996;
}
else
{
lean_object* x_997; 
lean_dec(x_984);
lean_dec(x_981);
if (lean_is_scalar(x_986)) {
 x_997 = lean_alloc_ctor(0, 2, 0);
} else {
 x_997 = x_986;
}
lean_ctor_set(x_997, 0, x_5);
lean_ctor_set(x_997, 1, x_985);
return x_997;
}
}
}
else
{
lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
lean_dec(x_981);
lean_dec(x_979);
lean_dec(x_978);
lean_dec(x_5);
x_998 = lean_ctor_get(x_983, 0);
lean_inc(x_998);
x_999 = lean_ctor_get(x_983, 1);
lean_inc(x_999);
if (lean_is_exclusive(x_983)) {
 lean_ctor_release(x_983, 0);
 lean_ctor_release(x_983, 1);
 x_1000 = x_983;
} else {
 lean_dec_ref(x_983);
 x_1000 = lean_box(0);
}
if (lean_is_scalar(x_1000)) {
 x_1001 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1001 = x_1000;
}
lean_ctor_set(x_1001, 0, x_998);
lean_ctor_set(x_1001, 1, x_999);
return x_1001;
}
}
else
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; 
lean_dec(x_979);
lean_dec(x_978);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1002 = lean_ctor_get(x_980, 0);
lean_inc(x_1002);
x_1003 = lean_ctor_get(x_980, 1);
lean_inc(x_1003);
if (lean_is_exclusive(x_980)) {
 lean_ctor_release(x_980, 0);
 lean_ctor_release(x_980, 1);
 x_1004 = x_980;
} else {
 lean_dec_ref(x_980);
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
case 6:
{
lean_object* x_1006; lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; uint8_t x_1010; lean_object* x_1011; 
x_1006 = lean_ctor_get(x_976, 1);
lean_inc(x_1006);
lean_dec(x_976);
x_1007 = lean_ctor_get(x_5, 0);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_5, 1);
lean_inc(x_1008);
x_1009 = lean_ctor_get(x_5, 2);
lean_inc(x_1009);
x_1010 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1008);
lean_inc(x_1);
x_1011 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1008, x_6, x_7, x_8, x_9, x_10, x_11, x_1006);
if (lean_obj_tag(x_1011) == 0)
{
lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; 
x_1012 = lean_ctor_get(x_1011, 0);
lean_inc(x_1012);
x_1013 = lean_ctor_get(x_1011, 1);
lean_inc(x_1013);
lean_dec(x_1011);
x_1014 = lean_nat_add(x_6, x_517);
lean_dec(x_6);
lean_inc(x_1009);
x_1015 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1009, x_1014, x_7, x_8, x_9, x_10, x_11, x_1013);
if (lean_obj_tag(x_1015) == 0)
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; size_t x_1020; size_t x_1021; uint8_t x_1022; 
x_1016 = lean_ctor_get(x_1015, 0);
lean_inc(x_1016);
x_1017 = lean_ctor_get(x_1015, 1);
lean_inc(x_1017);
if (lean_is_exclusive(x_1015)) {
 lean_ctor_release(x_1015, 0);
 lean_ctor_release(x_1015, 1);
 x_1018 = x_1015;
} else {
 lean_dec_ref(x_1015);
 x_1018 = lean_box(0);
}
lean_inc(x_1009);
lean_inc(x_1008);
lean_inc(x_1007);
x_1019 = l_Lean_Expr_lam___override(x_1007, x_1008, x_1009, x_1010);
x_1020 = lean_ptr_addr(x_1008);
lean_dec(x_1008);
x_1021 = lean_ptr_addr(x_1012);
x_1022 = lean_usize_dec_eq(x_1020, x_1021);
if (x_1022 == 0)
{
lean_object* x_1023; lean_object* x_1024; 
lean_dec(x_1019);
lean_dec(x_1009);
x_1023 = l_Lean_Expr_lam___override(x_1007, x_1012, x_1016, x_1010);
if (lean_is_scalar(x_1018)) {
 x_1024 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1024 = x_1018;
}
lean_ctor_set(x_1024, 0, x_1023);
lean_ctor_set(x_1024, 1, x_1017);
return x_1024;
}
else
{
size_t x_1025; size_t x_1026; uint8_t x_1027; 
x_1025 = lean_ptr_addr(x_1009);
lean_dec(x_1009);
x_1026 = lean_ptr_addr(x_1016);
x_1027 = lean_usize_dec_eq(x_1025, x_1026);
if (x_1027 == 0)
{
lean_object* x_1028; lean_object* x_1029; 
lean_dec(x_1019);
x_1028 = l_Lean_Expr_lam___override(x_1007, x_1012, x_1016, x_1010);
if (lean_is_scalar(x_1018)) {
 x_1029 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1029 = x_1018;
}
lean_ctor_set(x_1029, 0, x_1028);
lean_ctor_set(x_1029, 1, x_1017);
return x_1029;
}
else
{
uint8_t x_1030; 
x_1030 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_1010, x_1010);
if (x_1030 == 0)
{
lean_object* x_1031; lean_object* x_1032; 
lean_dec(x_1019);
x_1031 = l_Lean_Expr_lam___override(x_1007, x_1012, x_1016, x_1010);
if (lean_is_scalar(x_1018)) {
 x_1032 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1032 = x_1018;
}
lean_ctor_set(x_1032, 0, x_1031);
lean_ctor_set(x_1032, 1, x_1017);
return x_1032;
}
else
{
lean_object* x_1033; 
lean_dec(x_1016);
lean_dec(x_1012);
lean_dec(x_1007);
if (lean_is_scalar(x_1018)) {
 x_1033 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1033 = x_1018;
}
lean_ctor_set(x_1033, 0, x_1019);
lean_ctor_set(x_1033, 1, x_1017);
return x_1033;
}
}
}
}
else
{
lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; 
lean_dec(x_1012);
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec(x_1007);
x_1034 = lean_ctor_get(x_1015, 0);
lean_inc(x_1034);
x_1035 = lean_ctor_get(x_1015, 1);
lean_inc(x_1035);
if (lean_is_exclusive(x_1015)) {
 lean_ctor_release(x_1015, 0);
 lean_ctor_release(x_1015, 1);
 x_1036 = x_1015;
} else {
 lean_dec_ref(x_1015);
 x_1036 = lean_box(0);
}
if (lean_is_scalar(x_1036)) {
 x_1037 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1037 = x_1036;
}
lean_ctor_set(x_1037, 0, x_1034);
lean_ctor_set(x_1037, 1, x_1035);
return x_1037;
}
}
else
{
lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; lean_object* x_1041; 
lean_dec(x_1009);
lean_dec(x_1008);
lean_dec(x_1007);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1038 = lean_ctor_get(x_1011, 0);
lean_inc(x_1038);
x_1039 = lean_ctor_get(x_1011, 1);
lean_inc(x_1039);
if (lean_is_exclusive(x_1011)) {
 lean_ctor_release(x_1011, 0);
 lean_ctor_release(x_1011, 1);
 x_1040 = x_1011;
} else {
 lean_dec_ref(x_1011);
 x_1040 = lean_box(0);
}
if (lean_is_scalar(x_1040)) {
 x_1041 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1041 = x_1040;
}
lean_ctor_set(x_1041, 0, x_1038);
lean_ctor_set(x_1041, 1, x_1039);
return x_1041;
}
}
case 7:
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; uint8_t x_1046; lean_object* x_1047; 
x_1042 = lean_ctor_get(x_976, 1);
lean_inc(x_1042);
lean_dec(x_976);
x_1043 = lean_ctor_get(x_5, 0);
lean_inc(x_1043);
x_1044 = lean_ctor_get(x_5, 1);
lean_inc(x_1044);
x_1045 = lean_ctor_get(x_5, 2);
lean_inc(x_1045);
x_1046 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1044);
lean_inc(x_1);
x_1047 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1044, x_6, x_7, x_8, x_9, x_10, x_11, x_1042);
if (lean_obj_tag(x_1047) == 0)
{
lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; 
x_1048 = lean_ctor_get(x_1047, 0);
lean_inc(x_1048);
x_1049 = lean_ctor_get(x_1047, 1);
lean_inc(x_1049);
lean_dec(x_1047);
x_1050 = lean_nat_add(x_6, x_517);
lean_dec(x_6);
lean_inc(x_1045);
x_1051 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1045, x_1050, x_7, x_8, x_9, x_10, x_11, x_1049);
if (lean_obj_tag(x_1051) == 0)
{
lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; size_t x_1056; size_t x_1057; uint8_t x_1058; 
x_1052 = lean_ctor_get(x_1051, 0);
lean_inc(x_1052);
x_1053 = lean_ctor_get(x_1051, 1);
lean_inc(x_1053);
if (lean_is_exclusive(x_1051)) {
 lean_ctor_release(x_1051, 0);
 lean_ctor_release(x_1051, 1);
 x_1054 = x_1051;
} else {
 lean_dec_ref(x_1051);
 x_1054 = lean_box(0);
}
lean_inc(x_1045);
lean_inc(x_1044);
lean_inc(x_1043);
x_1055 = l_Lean_Expr_forallE___override(x_1043, x_1044, x_1045, x_1046);
x_1056 = lean_ptr_addr(x_1044);
lean_dec(x_1044);
x_1057 = lean_ptr_addr(x_1048);
x_1058 = lean_usize_dec_eq(x_1056, x_1057);
if (x_1058 == 0)
{
lean_object* x_1059; lean_object* x_1060; 
lean_dec(x_1055);
lean_dec(x_1045);
x_1059 = l_Lean_Expr_forallE___override(x_1043, x_1048, x_1052, x_1046);
if (lean_is_scalar(x_1054)) {
 x_1060 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1060 = x_1054;
}
lean_ctor_set(x_1060, 0, x_1059);
lean_ctor_set(x_1060, 1, x_1053);
return x_1060;
}
else
{
size_t x_1061; size_t x_1062; uint8_t x_1063; 
x_1061 = lean_ptr_addr(x_1045);
lean_dec(x_1045);
x_1062 = lean_ptr_addr(x_1052);
x_1063 = lean_usize_dec_eq(x_1061, x_1062);
if (x_1063 == 0)
{
lean_object* x_1064; lean_object* x_1065; 
lean_dec(x_1055);
x_1064 = l_Lean_Expr_forallE___override(x_1043, x_1048, x_1052, x_1046);
if (lean_is_scalar(x_1054)) {
 x_1065 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1065 = x_1054;
}
lean_ctor_set(x_1065, 0, x_1064);
lean_ctor_set(x_1065, 1, x_1053);
return x_1065;
}
else
{
uint8_t x_1066; 
x_1066 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_1046, x_1046);
if (x_1066 == 0)
{
lean_object* x_1067; lean_object* x_1068; 
lean_dec(x_1055);
x_1067 = l_Lean_Expr_forallE___override(x_1043, x_1048, x_1052, x_1046);
if (lean_is_scalar(x_1054)) {
 x_1068 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1068 = x_1054;
}
lean_ctor_set(x_1068, 0, x_1067);
lean_ctor_set(x_1068, 1, x_1053);
return x_1068;
}
else
{
lean_object* x_1069; 
lean_dec(x_1052);
lean_dec(x_1048);
lean_dec(x_1043);
if (lean_is_scalar(x_1054)) {
 x_1069 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1069 = x_1054;
}
lean_ctor_set(x_1069, 0, x_1055);
lean_ctor_set(x_1069, 1, x_1053);
return x_1069;
}
}
}
}
else
{
lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; 
lean_dec(x_1048);
lean_dec(x_1045);
lean_dec(x_1044);
lean_dec(x_1043);
x_1070 = lean_ctor_get(x_1051, 0);
lean_inc(x_1070);
x_1071 = lean_ctor_get(x_1051, 1);
lean_inc(x_1071);
if (lean_is_exclusive(x_1051)) {
 lean_ctor_release(x_1051, 0);
 lean_ctor_release(x_1051, 1);
 x_1072 = x_1051;
} else {
 lean_dec_ref(x_1051);
 x_1072 = lean_box(0);
}
if (lean_is_scalar(x_1072)) {
 x_1073 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1073 = x_1072;
}
lean_ctor_set(x_1073, 0, x_1070);
lean_ctor_set(x_1073, 1, x_1071);
return x_1073;
}
}
else
{
lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; 
lean_dec(x_1045);
lean_dec(x_1044);
lean_dec(x_1043);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1074 = lean_ctor_get(x_1047, 0);
lean_inc(x_1074);
x_1075 = lean_ctor_get(x_1047, 1);
lean_inc(x_1075);
if (lean_is_exclusive(x_1047)) {
 lean_ctor_release(x_1047, 0);
 lean_ctor_release(x_1047, 1);
 x_1076 = x_1047;
} else {
 lean_dec_ref(x_1047);
 x_1076 = lean_box(0);
}
if (lean_is_scalar(x_1076)) {
 x_1077 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1077 = x_1076;
}
lean_ctor_set(x_1077, 0, x_1074);
lean_ctor_set(x_1077, 1, x_1075);
return x_1077;
}
}
case 8:
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; uint8_t x_1083; lean_object* x_1084; 
x_1078 = lean_ctor_get(x_976, 1);
lean_inc(x_1078);
lean_dec(x_976);
x_1079 = lean_ctor_get(x_5, 0);
lean_inc(x_1079);
x_1080 = lean_ctor_get(x_5, 1);
lean_inc(x_1080);
x_1081 = lean_ctor_get(x_5, 2);
lean_inc(x_1081);
x_1082 = lean_ctor_get(x_5, 3);
lean_inc(x_1082);
x_1083 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1080);
lean_inc(x_1);
x_1084 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1080, x_6, x_7, x_8, x_9, x_10, x_11, x_1078);
if (lean_obj_tag(x_1084) == 0)
{
lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; 
x_1085 = lean_ctor_get(x_1084, 0);
lean_inc(x_1085);
x_1086 = lean_ctor_get(x_1084, 1);
lean_inc(x_1086);
lean_dec(x_1084);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1081);
lean_inc(x_1);
x_1087 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1081, x_6, x_7, x_8, x_9, x_10, x_11, x_1086);
if (lean_obj_tag(x_1087) == 0)
{
lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; 
x_1088 = lean_ctor_get(x_1087, 0);
lean_inc(x_1088);
x_1089 = lean_ctor_get(x_1087, 1);
lean_inc(x_1089);
lean_dec(x_1087);
x_1090 = lean_nat_add(x_6, x_517);
lean_dec(x_6);
lean_inc(x_1082);
x_1091 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1082, x_1090, x_7, x_8, x_9, x_10, x_11, x_1089);
if (lean_obj_tag(x_1091) == 0)
{
lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; size_t x_1096; size_t x_1097; uint8_t x_1098; 
x_1092 = lean_ctor_get(x_1091, 0);
lean_inc(x_1092);
x_1093 = lean_ctor_get(x_1091, 1);
lean_inc(x_1093);
if (lean_is_exclusive(x_1091)) {
 lean_ctor_release(x_1091, 0);
 lean_ctor_release(x_1091, 1);
 x_1094 = x_1091;
} else {
 lean_dec_ref(x_1091);
 x_1094 = lean_box(0);
}
lean_inc(x_1082);
lean_inc(x_1081);
lean_inc(x_1080);
lean_inc(x_1079);
x_1095 = l_Lean_Expr_letE___override(x_1079, x_1080, x_1081, x_1082, x_1083);
x_1096 = lean_ptr_addr(x_1080);
lean_dec(x_1080);
x_1097 = lean_ptr_addr(x_1085);
x_1098 = lean_usize_dec_eq(x_1096, x_1097);
if (x_1098 == 0)
{
lean_object* x_1099; lean_object* x_1100; 
lean_dec(x_1095);
lean_dec(x_1082);
lean_dec(x_1081);
x_1099 = l_Lean_Expr_letE___override(x_1079, x_1085, x_1088, x_1092, x_1083);
if (lean_is_scalar(x_1094)) {
 x_1100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1100 = x_1094;
}
lean_ctor_set(x_1100, 0, x_1099);
lean_ctor_set(x_1100, 1, x_1093);
return x_1100;
}
else
{
size_t x_1101; size_t x_1102; uint8_t x_1103; 
x_1101 = lean_ptr_addr(x_1081);
lean_dec(x_1081);
x_1102 = lean_ptr_addr(x_1088);
x_1103 = lean_usize_dec_eq(x_1101, x_1102);
if (x_1103 == 0)
{
lean_object* x_1104; lean_object* x_1105; 
lean_dec(x_1095);
lean_dec(x_1082);
x_1104 = l_Lean_Expr_letE___override(x_1079, x_1085, x_1088, x_1092, x_1083);
if (lean_is_scalar(x_1094)) {
 x_1105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1105 = x_1094;
}
lean_ctor_set(x_1105, 0, x_1104);
lean_ctor_set(x_1105, 1, x_1093);
return x_1105;
}
else
{
size_t x_1106; size_t x_1107; uint8_t x_1108; 
x_1106 = lean_ptr_addr(x_1082);
lean_dec(x_1082);
x_1107 = lean_ptr_addr(x_1092);
x_1108 = lean_usize_dec_eq(x_1106, x_1107);
if (x_1108 == 0)
{
lean_object* x_1109; lean_object* x_1110; 
lean_dec(x_1095);
x_1109 = l_Lean_Expr_letE___override(x_1079, x_1085, x_1088, x_1092, x_1083);
if (lean_is_scalar(x_1094)) {
 x_1110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1110 = x_1094;
}
lean_ctor_set(x_1110, 0, x_1109);
lean_ctor_set(x_1110, 1, x_1093);
return x_1110;
}
else
{
lean_object* x_1111; 
lean_dec(x_1092);
lean_dec(x_1088);
lean_dec(x_1085);
lean_dec(x_1079);
if (lean_is_scalar(x_1094)) {
 x_1111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1111 = x_1094;
}
lean_ctor_set(x_1111, 0, x_1095);
lean_ctor_set(x_1111, 1, x_1093);
return x_1111;
}
}
}
}
else
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; lean_object* x_1115; 
lean_dec(x_1088);
lean_dec(x_1085);
lean_dec(x_1082);
lean_dec(x_1081);
lean_dec(x_1080);
lean_dec(x_1079);
x_1112 = lean_ctor_get(x_1091, 0);
lean_inc(x_1112);
x_1113 = lean_ctor_get(x_1091, 1);
lean_inc(x_1113);
if (lean_is_exclusive(x_1091)) {
 lean_ctor_release(x_1091, 0);
 lean_ctor_release(x_1091, 1);
 x_1114 = x_1091;
} else {
 lean_dec_ref(x_1091);
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
else
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; 
lean_dec(x_1085);
lean_dec(x_1082);
lean_dec(x_1081);
lean_dec(x_1080);
lean_dec(x_1079);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1116 = lean_ctor_get(x_1087, 0);
lean_inc(x_1116);
x_1117 = lean_ctor_get(x_1087, 1);
lean_inc(x_1117);
if (lean_is_exclusive(x_1087)) {
 lean_ctor_release(x_1087, 0);
 lean_ctor_release(x_1087, 1);
 x_1118 = x_1087;
} else {
 lean_dec_ref(x_1087);
 x_1118 = lean_box(0);
}
if (lean_is_scalar(x_1118)) {
 x_1119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1119 = x_1118;
}
lean_ctor_set(x_1119, 0, x_1116);
lean_ctor_set(x_1119, 1, x_1117);
return x_1119;
}
}
else
{
lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; 
lean_dec(x_1082);
lean_dec(x_1081);
lean_dec(x_1080);
lean_dec(x_1079);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1120 = lean_ctor_get(x_1084, 0);
lean_inc(x_1120);
x_1121 = lean_ctor_get(x_1084, 1);
lean_inc(x_1121);
if (lean_is_exclusive(x_1084)) {
 lean_ctor_release(x_1084, 0);
 lean_ctor_release(x_1084, 1);
 x_1122 = x_1084;
} else {
 lean_dec_ref(x_1084);
 x_1122 = lean_box(0);
}
if (lean_is_scalar(x_1122)) {
 x_1123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1123 = x_1122;
}
lean_ctor_set(x_1123, 0, x_1120);
lean_ctor_set(x_1123, 1, x_1121);
return x_1123;
}
}
case 10:
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; 
x_1124 = lean_ctor_get(x_976, 1);
lean_inc(x_1124);
lean_dec(x_976);
x_1125 = lean_ctor_get(x_5, 0);
lean_inc(x_1125);
x_1126 = lean_ctor_get(x_5, 1);
lean_inc(x_1126);
lean_inc(x_1126);
x_1127 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1126, x_6, x_7, x_8, x_9, x_10, x_11, x_1124);
if (lean_obj_tag(x_1127) == 0)
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; size_t x_1131; size_t x_1132; uint8_t x_1133; 
x_1128 = lean_ctor_get(x_1127, 0);
lean_inc(x_1128);
x_1129 = lean_ctor_get(x_1127, 1);
lean_inc(x_1129);
if (lean_is_exclusive(x_1127)) {
 lean_ctor_release(x_1127, 0);
 lean_ctor_release(x_1127, 1);
 x_1130 = x_1127;
} else {
 lean_dec_ref(x_1127);
 x_1130 = lean_box(0);
}
x_1131 = lean_ptr_addr(x_1126);
lean_dec(x_1126);
x_1132 = lean_ptr_addr(x_1128);
x_1133 = lean_usize_dec_eq(x_1131, x_1132);
if (x_1133 == 0)
{
lean_object* x_1134; lean_object* x_1135; 
lean_dec(x_5);
x_1134 = l_Lean_Expr_mdata___override(x_1125, x_1128);
if (lean_is_scalar(x_1130)) {
 x_1135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1135 = x_1130;
}
lean_ctor_set(x_1135, 0, x_1134);
lean_ctor_set(x_1135, 1, x_1129);
return x_1135;
}
else
{
lean_object* x_1136; 
lean_dec(x_1128);
lean_dec(x_1125);
if (lean_is_scalar(x_1130)) {
 x_1136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1136 = x_1130;
}
lean_ctor_set(x_1136, 0, x_5);
lean_ctor_set(x_1136, 1, x_1129);
return x_1136;
}
}
else
{
lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
lean_dec(x_1126);
lean_dec(x_1125);
lean_dec(x_5);
x_1137 = lean_ctor_get(x_1127, 0);
lean_inc(x_1137);
x_1138 = lean_ctor_get(x_1127, 1);
lean_inc(x_1138);
if (lean_is_exclusive(x_1127)) {
 lean_ctor_release(x_1127, 0);
 lean_ctor_release(x_1127, 1);
 x_1139 = x_1127;
} else {
 lean_dec_ref(x_1127);
 x_1139 = lean_box(0);
}
if (lean_is_scalar(x_1139)) {
 x_1140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1140 = x_1139;
}
lean_ctor_set(x_1140, 0, x_1137);
lean_ctor_set(x_1140, 1, x_1138);
return x_1140;
}
}
case 11:
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; 
x_1141 = lean_ctor_get(x_976, 1);
lean_inc(x_1141);
lean_dec(x_976);
x_1142 = lean_ctor_get(x_5, 0);
lean_inc(x_1142);
x_1143 = lean_ctor_get(x_5, 1);
lean_inc(x_1143);
x_1144 = lean_ctor_get(x_5, 2);
lean_inc(x_1144);
lean_inc(x_1144);
x_1145 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1144, x_6, x_7, x_8, x_9, x_10, x_11, x_1141);
if (lean_obj_tag(x_1145) == 0)
{
lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; size_t x_1149; size_t x_1150; uint8_t x_1151; 
x_1146 = lean_ctor_get(x_1145, 0);
lean_inc(x_1146);
x_1147 = lean_ctor_get(x_1145, 1);
lean_inc(x_1147);
if (lean_is_exclusive(x_1145)) {
 lean_ctor_release(x_1145, 0);
 lean_ctor_release(x_1145, 1);
 x_1148 = x_1145;
} else {
 lean_dec_ref(x_1145);
 x_1148 = lean_box(0);
}
x_1149 = lean_ptr_addr(x_1144);
lean_dec(x_1144);
x_1150 = lean_ptr_addr(x_1146);
x_1151 = lean_usize_dec_eq(x_1149, x_1150);
if (x_1151 == 0)
{
lean_object* x_1152; lean_object* x_1153; 
lean_dec(x_5);
x_1152 = l_Lean_Expr_proj___override(x_1142, x_1143, x_1146);
if (lean_is_scalar(x_1148)) {
 x_1153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1153 = x_1148;
}
lean_ctor_set(x_1153, 0, x_1152);
lean_ctor_set(x_1153, 1, x_1147);
return x_1153;
}
else
{
lean_object* x_1154; 
lean_dec(x_1146);
lean_dec(x_1143);
lean_dec(x_1142);
if (lean_is_scalar(x_1148)) {
 x_1154 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1154 = x_1148;
}
lean_ctor_set(x_1154, 0, x_5);
lean_ctor_set(x_1154, 1, x_1147);
return x_1154;
}
}
else
{
lean_object* x_1155; lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; 
lean_dec(x_1144);
lean_dec(x_1143);
lean_dec(x_1142);
lean_dec(x_5);
x_1155 = lean_ctor_get(x_1145, 0);
lean_inc(x_1155);
x_1156 = lean_ctor_get(x_1145, 1);
lean_inc(x_1156);
if (lean_is_exclusive(x_1145)) {
 lean_ctor_release(x_1145, 0);
 lean_ctor_release(x_1145, 1);
 x_1157 = x_1145;
} else {
 lean_dec_ref(x_1145);
 x_1157 = lean_box(0);
}
if (lean_is_scalar(x_1157)) {
 x_1158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1158 = x_1157;
}
lean_ctor_set(x_1158, 0, x_1155);
lean_ctor_set(x_1158, 1, x_1156);
return x_1158;
}
}
default: 
{
lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1159 = lean_ctor_get(x_976, 1);
lean_inc(x_1159);
if (lean_is_exclusive(x_976)) {
 lean_ctor_release(x_976, 0);
 lean_ctor_release(x_976, 1);
 x_1160 = x_976;
} else {
 lean_dec_ref(x_976);
 x_1160 = lean_box(0);
}
if (lean_is_scalar(x_1160)) {
 x_1161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1161 = x_1160;
}
lean_ctor_set(x_1161, 0, x_5);
lean_ctor_set(x_1161, 1, x_1159);
return x_1161;
}
}
}
else
{
lean_object* x_1162; lean_object* x_1163; 
lean_dec(x_263);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_1162 = l_Lean_Expr_bvar___override(x_6);
x_1163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1163, 0, x_1162);
lean_ctor_set(x_1163, 1, x_965);
return x_1163;
}
}
}
}
else
{
uint8_t x_1164; 
lean_dec(x_263);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1164 = !lean_is_exclusive(x_264);
if (x_1164 == 0)
{
return x_264;
}
else
{
lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; 
x_1165 = lean_ctor_get(x_264, 0);
x_1166 = lean_ctor_get(x_264, 1);
lean_inc(x_1166);
lean_inc(x_1165);
lean_dec(x_264);
x_1167 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1167, 0, x_1165);
lean_ctor_set(x_1167, 1, x_1166);
return x_1167;
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
lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; 
x_1168 = lean_ctor_get(x_5, 0);
lean_inc(x_1168);
x_1169 = lean_ctor_get(x_5, 1);
lean_inc(x_1169);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1168);
lean_inc(x_1);
x_1170 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1168, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1170) == 0)
{
lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; 
x_1171 = lean_ctor_get(x_1170, 0);
lean_inc(x_1171);
x_1172 = lean_ctor_get(x_1170, 1);
lean_inc(x_1172);
lean_dec(x_1170);
lean_inc(x_1169);
x_1173 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1169, x_6, x_7, x_8, x_9, x_10, x_11, x_1172);
if (lean_obj_tag(x_1173) == 0)
{
uint8_t x_1174; 
x_1174 = !lean_is_exclusive(x_1173);
if (x_1174 == 0)
{
lean_object* x_1175; size_t x_1176; size_t x_1177; uint8_t x_1178; 
x_1175 = lean_ctor_get(x_1173, 0);
x_1176 = lean_ptr_addr(x_1168);
lean_dec(x_1168);
x_1177 = lean_ptr_addr(x_1171);
x_1178 = lean_usize_dec_eq(x_1176, x_1177);
if (x_1178 == 0)
{
lean_object* x_1179; 
lean_dec(x_1169);
lean_dec(x_5);
x_1179 = l_Lean_Expr_app___override(x_1171, x_1175);
lean_ctor_set(x_1173, 0, x_1179);
return x_1173;
}
else
{
size_t x_1180; size_t x_1181; uint8_t x_1182; 
x_1180 = lean_ptr_addr(x_1169);
lean_dec(x_1169);
x_1181 = lean_ptr_addr(x_1175);
x_1182 = lean_usize_dec_eq(x_1180, x_1181);
if (x_1182 == 0)
{
lean_object* x_1183; 
lean_dec(x_5);
x_1183 = l_Lean_Expr_app___override(x_1171, x_1175);
lean_ctor_set(x_1173, 0, x_1183);
return x_1173;
}
else
{
lean_dec(x_1175);
lean_dec(x_1171);
lean_ctor_set(x_1173, 0, x_5);
return x_1173;
}
}
}
else
{
lean_object* x_1184; lean_object* x_1185; size_t x_1186; size_t x_1187; uint8_t x_1188; 
x_1184 = lean_ctor_get(x_1173, 0);
x_1185 = lean_ctor_get(x_1173, 1);
lean_inc(x_1185);
lean_inc(x_1184);
lean_dec(x_1173);
x_1186 = lean_ptr_addr(x_1168);
lean_dec(x_1168);
x_1187 = lean_ptr_addr(x_1171);
x_1188 = lean_usize_dec_eq(x_1186, x_1187);
if (x_1188 == 0)
{
lean_object* x_1189; lean_object* x_1190; 
lean_dec(x_1169);
lean_dec(x_5);
x_1189 = l_Lean_Expr_app___override(x_1171, x_1184);
x_1190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1190, 0, x_1189);
lean_ctor_set(x_1190, 1, x_1185);
return x_1190;
}
else
{
size_t x_1191; size_t x_1192; uint8_t x_1193; 
x_1191 = lean_ptr_addr(x_1169);
lean_dec(x_1169);
x_1192 = lean_ptr_addr(x_1184);
x_1193 = lean_usize_dec_eq(x_1191, x_1192);
if (x_1193 == 0)
{
lean_object* x_1194; lean_object* x_1195; 
lean_dec(x_5);
x_1194 = l_Lean_Expr_app___override(x_1171, x_1184);
x_1195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1195, 0, x_1194);
lean_ctor_set(x_1195, 1, x_1185);
return x_1195;
}
else
{
lean_object* x_1196; 
lean_dec(x_1184);
lean_dec(x_1171);
x_1196 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1196, 0, x_5);
lean_ctor_set(x_1196, 1, x_1185);
return x_1196;
}
}
}
}
else
{
uint8_t x_1197; 
lean_dec(x_1171);
lean_dec(x_1169);
lean_dec(x_1168);
lean_dec(x_5);
x_1197 = !lean_is_exclusive(x_1173);
if (x_1197 == 0)
{
return x_1173;
}
else
{
lean_object* x_1198; lean_object* x_1199; lean_object* x_1200; 
x_1198 = lean_ctor_get(x_1173, 0);
x_1199 = lean_ctor_get(x_1173, 1);
lean_inc(x_1199);
lean_inc(x_1198);
lean_dec(x_1173);
x_1200 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1200, 0, x_1198);
lean_ctor_set(x_1200, 1, x_1199);
return x_1200;
}
}
}
else
{
uint8_t x_1201; 
lean_dec(x_1169);
lean_dec(x_1168);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1201 = !lean_is_exclusive(x_1170);
if (x_1201 == 0)
{
return x_1170;
}
else
{
lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; 
x_1202 = lean_ctor_get(x_1170, 0);
x_1203 = lean_ctor_get(x_1170, 1);
lean_inc(x_1203);
lean_inc(x_1202);
lean_dec(x_1170);
x_1204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1204, 0, x_1202);
lean_ctor_set(x_1204, 1, x_1203);
return x_1204;
}
}
}
case 6:
{
lean_object* x_1205; lean_object* x_1206; lean_object* x_1207; uint8_t x_1208; lean_object* x_1209; 
x_1205 = lean_ctor_get(x_5, 0);
lean_inc(x_1205);
x_1206 = lean_ctor_get(x_5, 1);
lean_inc(x_1206);
x_1207 = lean_ctor_get(x_5, 2);
lean_inc(x_1207);
x_1208 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1206);
lean_inc(x_1);
x_1209 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1206, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1209) == 0)
{
lean_object* x_1210; lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; 
x_1210 = lean_ctor_get(x_1209, 0);
lean_inc(x_1210);
x_1211 = lean_ctor_get(x_1209, 1);
lean_inc(x_1211);
lean_dec(x_1209);
x_1212 = lean_unsigned_to_nat(1u);
x_1213 = lean_nat_add(x_6, x_1212);
lean_dec(x_6);
lean_inc(x_1207);
x_1214 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1207, x_1213, x_7, x_8, x_9, x_10, x_11, x_1211);
if (lean_obj_tag(x_1214) == 0)
{
uint8_t x_1215; 
x_1215 = !lean_is_exclusive(x_1214);
if (x_1215 == 0)
{
lean_object* x_1216; lean_object* x_1217; size_t x_1218; size_t x_1219; uint8_t x_1220; 
x_1216 = lean_ctor_get(x_1214, 0);
lean_inc(x_1207);
lean_inc(x_1206);
lean_inc(x_1205);
x_1217 = l_Lean_Expr_lam___override(x_1205, x_1206, x_1207, x_1208);
x_1218 = lean_ptr_addr(x_1206);
lean_dec(x_1206);
x_1219 = lean_ptr_addr(x_1210);
x_1220 = lean_usize_dec_eq(x_1218, x_1219);
if (x_1220 == 0)
{
lean_object* x_1221; 
lean_dec(x_1217);
lean_dec(x_1207);
x_1221 = l_Lean_Expr_lam___override(x_1205, x_1210, x_1216, x_1208);
lean_ctor_set(x_1214, 0, x_1221);
return x_1214;
}
else
{
size_t x_1222; size_t x_1223; uint8_t x_1224; 
x_1222 = lean_ptr_addr(x_1207);
lean_dec(x_1207);
x_1223 = lean_ptr_addr(x_1216);
x_1224 = lean_usize_dec_eq(x_1222, x_1223);
if (x_1224 == 0)
{
lean_object* x_1225; 
lean_dec(x_1217);
x_1225 = l_Lean_Expr_lam___override(x_1205, x_1210, x_1216, x_1208);
lean_ctor_set(x_1214, 0, x_1225);
return x_1214;
}
else
{
uint8_t x_1226; 
x_1226 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_1208, x_1208);
if (x_1226 == 0)
{
lean_object* x_1227; 
lean_dec(x_1217);
x_1227 = l_Lean_Expr_lam___override(x_1205, x_1210, x_1216, x_1208);
lean_ctor_set(x_1214, 0, x_1227);
return x_1214;
}
else
{
lean_dec(x_1216);
lean_dec(x_1210);
lean_dec(x_1205);
lean_ctor_set(x_1214, 0, x_1217);
return x_1214;
}
}
}
}
else
{
lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; size_t x_1231; size_t x_1232; uint8_t x_1233; 
x_1228 = lean_ctor_get(x_1214, 0);
x_1229 = lean_ctor_get(x_1214, 1);
lean_inc(x_1229);
lean_inc(x_1228);
lean_dec(x_1214);
lean_inc(x_1207);
lean_inc(x_1206);
lean_inc(x_1205);
x_1230 = l_Lean_Expr_lam___override(x_1205, x_1206, x_1207, x_1208);
x_1231 = lean_ptr_addr(x_1206);
lean_dec(x_1206);
x_1232 = lean_ptr_addr(x_1210);
x_1233 = lean_usize_dec_eq(x_1231, x_1232);
if (x_1233 == 0)
{
lean_object* x_1234; lean_object* x_1235; 
lean_dec(x_1230);
lean_dec(x_1207);
x_1234 = l_Lean_Expr_lam___override(x_1205, x_1210, x_1228, x_1208);
x_1235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1235, 0, x_1234);
lean_ctor_set(x_1235, 1, x_1229);
return x_1235;
}
else
{
size_t x_1236; size_t x_1237; uint8_t x_1238; 
x_1236 = lean_ptr_addr(x_1207);
lean_dec(x_1207);
x_1237 = lean_ptr_addr(x_1228);
x_1238 = lean_usize_dec_eq(x_1236, x_1237);
if (x_1238 == 0)
{
lean_object* x_1239; lean_object* x_1240; 
lean_dec(x_1230);
x_1239 = l_Lean_Expr_lam___override(x_1205, x_1210, x_1228, x_1208);
x_1240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1240, 0, x_1239);
lean_ctor_set(x_1240, 1, x_1229);
return x_1240;
}
else
{
uint8_t x_1241; 
x_1241 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_1208, x_1208);
if (x_1241 == 0)
{
lean_object* x_1242; lean_object* x_1243; 
lean_dec(x_1230);
x_1242 = l_Lean_Expr_lam___override(x_1205, x_1210, x_1228, x_1208);
x_1243 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1243, 0, x_1242);
lean_ctor_set(x_1243, 1, x_1229);
return x_1243;
}
else
{
lean_object* x_1244; 
lean_dec(x_1228);
lean_dec(x_1210);
lean_dec(x_1205);
x_1244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1244, 0, x_1230);
lean_ctor_set(x_1244, 1, x_1229);
return x_1244;
}
}
}
}
}
else
{
uint8_t x_1245; 
lean_dec(x_1210);
lean_dec(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
x_1245 = !lean_is_exclusive(x_1214);
if (x_1245 == 0)
{
return x_1214;
}
else
{
lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; 
x_1246 = lean_ctor_get(x_1214, 0);
x_1247 = lean_ctor_get(x_1214, 1);
lean_inc(x_1247);
lean_inc(x_1246);
lean_dec(x_1214);
x_1248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1248, 0, x_1246);
lean_ctor_set(x_1248, 1, x_1247);
return x_1248;
}
}
}
else
{
uint8_t x_1249; 
lean_dec(x_1207);
lean_dec(x_1206);
lean_dec(x_1205);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1249 = !lean_is_exclusive(x_1209);
if (x_1249 == 0)
{
return x_1209;
}
else
{
lean_object* x_1250; lean_object* x_1251; lean_object* x_1252; 
x_1250 = lean_ctor_get(x_1209, 0);
x_1251 = lean_ctor_get(x_1209, 1);
lean_inc(x_1251);
lean_inc(x_1250);
lean_dec(x_1209);
x_1252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1252, 0, x_1250);
lean_ctor_set(x_1252, 1, x_1251);
return x_1252;
}
}
}
case 7:
{
lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; uint8_t x_1256; lean_object* x_1257; 
x_1253 = lean_ctor_get(x_5, 0);
lean_inc(x_1253);
x_1254 = lean_ctor_get(x_5, 1);
lean_inc(x_1254);
x_1255 = lean_ctor_get(x_5, 2);
lean_inc(x_1255);
x_1256 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1254);
lean_inc(x_1);
x_1257 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1254, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1257) == 0)
{
lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; 
x_1258 = lean_ctor_get(x_1257, 0);
lean_inc(x_1258);
x_1259 = lean_ctor_get(x_1257, 1);
lean_inc(x_1259);
lean_dec(x_1257);
x_1260 = lean_unsigned_to_nat(1u);
x_1261 = lean_nat_add(x_6, x_1260);
lean_dec(x_6);
lean_inc(x_1255);
x_1262 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1255, x_1261, x_7, x_8, x_9, x_10, x_11, x_1259);
if (lean_obj_tag(x_1262) == 0)
{
uint8_t x_1263; 
x_1263 = !lean_is_exclusive(x_1262);
if (x_1263 == 0)
{
lean_object* x_1264; lean_object* x_1265; size_t x_1266; size_t x_1267; uint8_t x_1268; 
x_1264 = lean_ctor_get(x_1262, 0);
lean_inc(x_1255);
lean_inc(x_1254);
lean_inc(x_1253);
x_1265 = l_Lean_Expr_forallE___override(x_1253, x_1254, x_1255, x_1256);
x_1266 = lean_ptr_addr(x_1254);
lean_dec(x_1254);
x_1267 = lean_ptr_addr(x_1258);
x_1268 = lean_usize_dec_eq(x_1266, x_1267);
if (x_1268 == 0)
{
lean_object* x_1269; 
lean_dec(x_1265);
lean_dec(x_1255);
x_1269 = l_Lean_Expr_forallE___override(x_1253, x_1258, x_1264, x_1256);
lean_ctor_set(x_1262, 0, x_1269);
return x_1262;
}
else
{
size_t x_1270; size_t x_1271; uint8_t x_1272; 
x_1270 = lean_ptr_addr(x_1255);
lean_dec(x_1255);
x_1271 = lean_ptr_addr(x_1264);
x_1272 = lean_usize_dec_eq(x_1270, x_1271);
if (x_1272 == 0)
{
lean_object* x_1273; 
lean_dec(x_1265);
x_1273 = l_Lean_Expr_forallE___override(x_1253, x_1258, x_1264, x_1256);
lean_ctor_set(x_1262, 0, x_1273);
return x_1262;
}
else
{
uint8_t x_1274; 
x_1274 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_1256, x_1256);
if (x_1274 == 0)
{
lean_object* x_1275; 
lean_dec(x_1265);
x_1275 = l_Lean_Expr_forallE___override(x_1253, x_1258, x_1264, x_1256);
lean_ctor_set(x_1262, 0, x_1275);
return x_1262;
}
else
{
lean_dec(x_1264);
lean_dec(x_1258);
lean_dec(x_1253);
lean_ctor_set(x_1262, 0, x_1265);
return x_1262;
}
}
}
}
else
{
lean_object* x_1276; lean_object* x_1277; lean_object* x_1278; size_t x_1279; size_t x_1280; uint8_t x_1281; 
x_1276 = lean_ctor_get(x_1262, 0);
x_1277 = lean_ctor_get(x_1262, 1);
lean_inc(x_1277);
lean_inc(x_1276);
lean_dec(x_1262);
lean_inc(x_1255);
lean_inc(x_1254);
lean_inc(x_1253);
x_1278 = l_Lean_Expr_forallE___override(x_1253, x_1254, x_1255, x_1256);
x_1279 = lean_ptr_addr(x_1254);
lean_dec(x_1254);
x_1280 = lean_ptr_addr(x_1258);
x_1281 = lean_usize_dec_eq(x_1279, x_1280);
if (x_1281 == 0)
{
lean_object* x_1282; lean_object* x_1283; 
lean_dec(x_1278);
lean_dec(x_1255);
x_1282 = l_Lean_Expr_forallE___override(x_1253, x_1258, x_1276, x_1256);
x_1283 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1283, 0, x_1282);
lean_ctor_set(x_1283, 1, x_1277);
return x_1283;
}
else
{
size_t x_1284; size_t x_1285; uint8_t x_1286; 
x_1284 = lean_ptr_addr(x_1255);
lean_dec(x_1255);
x_1285 = lean_ptr_addr(x_1276);
x_1286 = lean_usize_dec_eq(x_1284, x_1285);
if (x_1286 == 0)
{
lean_object* x_1287; lean_object* x_1288; 
lean_dec(x_1278);
x_1287 = l_Lean_Expr_forallE___override(x_1253, x_1258, x_1276, x_1256);
x_1288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1288, 0, x_1287);
lean_ctor_set(x_1288, 1, x_1277);
return x_1288;
}
else
{
uint8_t x_1289; 
x_1289 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_1256, x_1256);
if (x_1289 == 0)
{
lean_object* x_1290; lean_object* x_1291; 
lean_dec(x_1278);
x_1290 = l_Lean_Expr_forallE___override(x_1253, x_1258, x_1276, x_1256);
x_1291 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1291, 0, x_1290);
lean_ctor_set(x_1291, 1, x_1277);
return x_1291;
}
else
{
lean_object* x_1292; 
lean_dec(x_1276);
lean_dec(x_1258);
lean_dec(x_1253);
x_1292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1292, 0, x_1278);
lean_ctor_set(x_1292, 1, x_1277);
return x_1292;
}
}
}
}
}
else
{
uint8_t x_1293; 
lean_dec(x_1258);
lean_dec(x_1255);
lean_dec(x_1254);
lean_dec(x_1253);
x_1293 = !lean_is_exclusive(x_1262);
if (x_1293 == 0)
{
return x_1262;
}
else
{
lean_object* x_1294; lean_object* x_1295; lean_object* x_1296; 
x_1294 = lean_ctor_get(x_1262, 0);
x_1295 = lean_ctor_get(x_1262, 1);
lean_inc(x_1295);
lean_inc(x_1294);
lean_dec(x_1262);
x_1296 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1296, 0, x_1294);
lean_ctor_set(x_1296, 1, x_1295);
return x_1296;
}
}
}
else
{
uint8_t x_1297; 
lean_dec(x_1255);
lean_dec(x_1254);
lean_dec(x_1253);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1297 = !lean_is_exclusive(x_1257);
if (x_1297 == 0)
{
return x_1257;
}
else
{
lean_object* x_1298; lean_object* x_1299; lean_object* x_1300; 
x_1298 = lean_ctor_get(x_1257, 0);
x_1299 = lean_ctor_get(x_1257, 1);
lean_inc(x_1299);
lean_inc(x_1298);
lean_dec(x_1257);
x_1300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1300, 0, x_1298);
lean_ctor_set(x_1300, 1, x_1299);
return x_1300;
}
}
}
case 8:
{
lean_object* x_1301; lean_object* x_1302; lean_object* x_1303; lean_object* x_1304; uint8_t x_1305; lean_object* x_1306; 
x_1301 = lean_ctor_get(x_5, 0);
lean_inc(x_1301);
x_1302 = lean_ctor_get(x_5, 1);
lean_inc(x_1302);
x_1303 = lean_ctor_get(x_5, 2);
lean_inc(x_1303);
x_1304 = lean_ctor_get(x_5, 3);
lean_inc(x_1304);
x_1305 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1302);
lean_inc(x_1);
x_1306 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1302, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1306) == 0)
{
lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; 
x_1307 = lean_ctor_get(x_1306, 0);
lean_inc(x_1307);
x_1308 = lean_ctor_get(x_1306, 1);
lean_inc(x_1308);
lean_dec(x_1306);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1303);
lean_inc(x_1);
x_1309 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1303, x_6, x_7, x_8, x_9, x_10, x_11, x_1308);
if (lean_obj_tag(x_1309) == 0)
{
lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; lean_object* x_1313; lean_object* x_1314; 
x_1310 = lean_ctor_get(x_1309, 0);
lean_inc(x_1310);
x_1311 = lean_ctor_get(x_1309, 1);
lean_inc(x_1311);
lean_dec(x_1309);
x_1312 = lean_unsigned_to_nat(1u);
x_1313 = lean_nat_add(x_6, x_1312);
lean_dec(x_6);
lean_inc(x_1304);
x_1314 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1304, x_1313, x_7, x_8, x_9, x_10, x_11, x_1311);
if (lean_obj_tag(x_1314) == 0)
{
uint8_t x_1315; 
x_1315 = !lean_is_exclusive(x_1314);
if (x_1315 == 0)
{
lean_object* x_1316; lean_object* x_1317; size_t x_1318; size_t x_1319; uint8_t x_1320; 
x_1316 = lean_ctor_get(x_1314, 0);
lean_inc(x_1304);
lean_inc(x_1303);
lean_inc(x_1302);
lean_inc(x_1301);
x_1317 = l_Lean_Expr_letE___override(x_1301, x_1302, x_1303, x_1304, x_1305);
x_1318 = lean_ptr_addr(x_1302);
lean_dec(x_1302);
x_1319 = lean_ptr_addr(x_1307);
x_1320 = lean_usize_dec_eq(x_1318, x_1319);
if (x_1320 == 0)
{
lean_object* x_1321; 
lean_dec(x_1317);
lean_dec(x_1304);
lean_dec(x_1303);
x_1321 = l_Lean_Expr_letE___override(x_1301, x_1307, x_1310, x_1316, x_1305);
lean_ctor_set(x_1314, 0, x_1321);
return x_1314;
}
else
{
size_t x_1322; size_t x_1323; uint8_t x_1324; 
x_1322 = lean_ptr_addr(x_1303);
lean_dec(x_1303);
x_1323 = lean_ptr_addr(x_1310);
x_1324 = lean_usize_dec_eq(x_1322, x_1323);
if (x_1324 == 0)
{
lean_object* x_1325; 
lean_dec(x_1317);
lean_dec(x_1304);
x_1325 = l_Lean_Expr_letE___override(x_1301, x_1307, x_1310, x_1316, x_1305);
lean_ctor_set(x_1314, 0, x_1325);
return x_1314;
}
else
{
size_t x_1326; size_t x_1327; uint8_t x_1328; 
x_1326 = lean_ptr_addr(x_1304);
lean_dec(x_1304);
x_1327 = lean_ptr_addr(x_1316);
x_1328 = lean_usize_dec_eq(x_1326, x_1327);
if (x_1328 == 0)
{
lean_object* x_1329; 
lean_dec(x_1317);
x_1329 = l_Lean_Expr_letE___override(x_1301, x_1307, x_1310, x_1316, x_1305);
lean_ctor_set(x_1314, 0, x_1329);
return x_1314;
}
else
{
lean_dec(x_1316);
lean_dec(x_1310);
lean_dec(x_1307);
lean_dec(x_1301);
lean_ctor_set(x_1314, 0, x_1317);
return x_1314;
}
}
}
}
else
{
lean_object* x_1330; lean_object* x_1331; lean_object* x_1332; size_t x_1333; size_t x_1334; uint8_t x_1335; 
x_1330 = lean_ctor_get(x_1314, 0);
x_1331 = lean_ctor_get(x_1314, 1);
lean_inc(x_1331);
lean_inc(x_1330);
lean_dec(x_1314);
lean_inc(x_1304);
lean_inc(x_1303);
lean_inc(x_1302);
lean_inc(x_1301);
x_1332 = l_Lean_Expr_letE___override(x_1301, x_1302, x_1303, x_1304, x_1305);
x_1333 = lean_ptr_addr(x_1302);
lean_dec(x_1302);
x_1334 = lean_ptr_addr(x_1307);
x_1335 = lean_usize_dec_eq(x_1333, x_1334);
if (x_1335 == 0)
{
lean_object* x_1336; lean_object* x_1337; 
lean_dec(x_1332);
lean_dec(x_1304);
lean_dec(x_1303);
x_1336 = l_Lean_Expr_letE___override(x_1301, x_1307, x_1310, x_1330, x_1305);
x_1337 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1337, 0, x_1336);
lean_ctor_set(x_1337, 1, x_1331);
return x_1337;
}
else
{
size_t x_1338; size_t x_1339; uint8_t x_1340; 
x_1338 = lean_ptr_addr(x_1303);
lean_dec(x_1303);
x_1339 = lean_ptr_addr(x_1310);
x_1340 = lean_usize_dec_eq(x_1338, x_1339);
if (x_1340 == 0)
{
lean_object* x_1341; lean_object* x_1342; 
lean_dec(x_1332);
lean_dec(x_1304);
x_1341 = l_Lean_Expr_letE___override(x_1301, x_1307, x_1310, x_1330, x_1305);
x_1342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1342, 0, x_1341);
lean_ctor_set(x_1342, 1, x_1331);
return x_1342;
}
else
{
size_t x_1343; size_t x_1344; uint8_t x_1345; 
x_1343 = lean_ptr_addr(x_1304);
lean_dec(x_1304);
x_1344 = lean_ptr_addr(x_1330);
x_1345 = lean_usize_dec_eq(x_1343, x_1344);
if (x_1345 == 0)
{
lean_object* x_1346; lean_object* x_1347; 
lean_dec(x_1332);
x_1346 = l_Lean_Expr_letE___override(x_1301, x_1307, x_1310, x_1330, x_1305);
x_1347 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1347, 0, x_1346);
lean_ctor_set(x_1347, 1, x_1331);
return x_1347;
}
else
{
lean_object* x_1348; 
lean_dec(x_1330);
lean_dec(x_1310);
lean_dec(x_1307);
lean_dec(x_1301);
x_1348 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1348, 0, x_1332);
lean_ctor_set(x_1348, 1, x_1331);
return x_1348;
}
}
}
}
}
else
{
uint8_t x_1349; 
lean_dec(x_1310);
lean_dec(x_1307);
lean_dec(x_1304);
lean_dec(x_1303);
lean_dec(x_1302);
lean_dec(x_1301);
x_1349 = !lean_is_exclusive(x_1314);
if (x_1349 == 0)
{
return x_1314;
}
else
{
lean_object* x_1350; lean_object* x_1351; lean_object* x_1352; 
x_1350 = lean_ctor_get(x_1314, 0);
x_1351 = lean_ctor_get(x_1314, 1);
lean_inc(x_1351);
lean_inc(x_1350);
lean_dec(x_1314);
x_1352 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1352, 0, x_1350);
lean_ctor_set(x_1352, 1, x_1351);
return x_1352;
}
}
}
else
{
uint8_t x_1353; 
lean_dec(x_1307);
lean_dec(x_1304);
lean_dec(x_1303);
lean_dec(x_1302);
lean_dec(x_1301);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1353 = !lean_is_exclusive(x_1309);
if (x_1353 == 0)
{
return x_1309;
}
else
{
lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; 
x_1354 = lean_ctor_get(x_1309, 0);
x_1355 = lean_ctor_get(x_1309, 1);
lean_inc(x_1355);
lean_inc(x_1354);
lean_dec(x_1309);
x_1356 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1356, 0, x_1354);
lean_ctor_set(x_1356, 1, x_1355);
return x_1356;
}
}
}
else
{
uint8_t x_1357; 
lean_dec(x_1304);
lean_dec(x_1303);
lean_dec(x_1302);
lean_dec(x_1301);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1357 = !lean_is_exclusive(x_1306);
if (x_1357 == 0)
{
return x_1306;
}
else
{
lean_object* x_1358; lean_object* x_1359; lean_object* x_1360; 
x_1358 = lean_ctor_get(x_1306, 0);
x_1359 = lean_ctor_get(x_1306, 1);
lean_inc(x_1359);
lean_inc(x_1358);
lean_dec(x_1306);
x_1360 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1360, 0, x_1358);
lean_ctor_set(x_1360, 1, x_1359);
return x_1360;
}
}
}
case 10:
{
lean_object* x_1361; lean_object* x_1362; lean_object* x_1363; 
x_1361 = lean_ctor_get(x_5, 0);
lean_inc(x_1361);
x_1362 = lean_ctor_get(x_5, 1);
lean_inc(x_1362);
lean_inc(x_1362);
x_1363 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1362, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1363) == 0)
{
uint8_t x_1364; 
x_1364 = !lean_is_exclusive(x_1363);
if (x_1364 == 0)
{
lean_object* x_1365; size_t x_1366; size_t x_1367; uint8_t x_1368; 
x_1365 = lean_ctor_get(x_1363, 0);
x_1366 = lean_ptr_addr(x_1362);
lean_dec(x_1362);
x_1367 = lean_ptr_addr(x_1365);
x_1368 = lean_usize_dec_eq(x_1366, x_1367);
if (x_1368 == 0)
{
lean_object* x_1369; 
lean_dec(x_5);
x_1369 = l_Lean_Expr_mdata___override(x_1361, x_1365);
lean_ctor_set(x_1363, 0, x_1369);
return x_1363;
}
else
{
lean_dec(x_1365);
lean_dec(x_1361);
lean_ctor_set(x_1363, 0, x_5);
return x_1363;
}
}
else
{
lean_object* x_1370; lean_object* x_1371; size_t x_1372; size_t x_1373; uint8_t x_1374; 
x_1370 = lean_ctor_get(x_1363, 0);
x_1371 = lean_ctor_get(x_1363, 1);
lean_inc(x_1371);
lean_inc(x_1370);
lean_dec(x_1363);
x_1372 = lean_ptr_addr(x_1362);
lean_dec(x_1362);
x_1373 = lean_ptr_addr(x_1370);
x_1374 = lean_usize_dec_eq(x_1372, x_1373);
if (x_1374 == 0)
{
lean_object* x_1375; lean_object* x_1376; 
lean_dec(x_5);
x_1375 = l_Lean_Expr_mdata___override(x_1361, x_1370);
x_1376 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1376, 0, x_1375);
lean_ctor_set(x_1376, 1, x_1371);
return x_1376;
}
else
{
lean_object* x_1377; 
lean_dec(x_1370);
lean_dec(x_1361);
x_1377 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1377, 0, x_5);
lean_ctor_set(x_1377, 1, x_1371);
return x_1377;
}
}
}
else
{
uint8_t x_1378; 
lean_dec(x_1362);
lean_dec(x_1361);
lean_dec(x_5);
x_1378 = !lean_is_exclusive(x_1363);
if (x_1378 == 0)
{
return x_1363;
}
else
{
lean_object* x_1379; lean_object* x_1380; lean_object* x_1381; 
x_1379 = lean_ctor_get(x_1363, 0);
x_1380 = lean_ctor_get(x_1363, 1);
lean_inc(x_1380);
lean_inc(x_1379);
lean_dec(x_1363);
x_1381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1381, 0, x_1379);
lean_ctor_set(x_1381, 1, x_1380);
return x_1381;
}
}
}
case 11:
{
lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; 
x_1382 = lean_ctor_get(x_5, 0);
lean_inc(x_1382);
x_1383 = lean_ctor_get(x_5, 1);
lean_inc(x_1383);
x_1384 = lean_ctor_get(x_5, 2);
lean_inc(x_1384);
lean_inc(x_1384);
x_1385 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1384, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1385) == 0)
{
uint8_t x_1386; 
x_1386 = !lean_is_exclusive(x_1385);
if (x_1386 == 0)
{
lean_object* x_1387; size_t x_1388; size_t x_1389; uint8_t x_1390; 
x_1387 = lean_ctor_get(x_1385, 0);
x_1388 = lean_ptr_addr(x_1384);
lean_dec(x_1384);
x_1389 = lean_ptr_addr(x_1387);
x_1390 = lean_usize_dec_eq(x_1388, x_1389);
if (x_1390 == 0)
{
lean_object* x_1391; 
lean_dec(x_5);
x_1391 = l_Lean_Expr_proj___override(x_1382, x_1383, x_1387);
lean_ctor_set(x_1385, 0, x_1391);
return x_1385;
}
else
{
lean_dec(x_1387);
lean_dec(x_1383);
lean_dec(x_1382);
lean_ctor_set(x_1385, 0, x_5);
return x_1385;
}
}
else
{
lean_object* x_1392; lean_object* x_1393; size_t x_1394; size_t x_1395; uint8_t x_1396; 
x_1392 = lean_ctor_get(x_1385, 0);
x_1393 = lean_ctor_get(x_1385, 1);
lean_inc(x_1393);
lean_inc(x_1392);
lean_dec(x_1385);
x_1394 = lean_ptr_addr(x_1384);
lean_dec(x_1384);
x_1395 = lean_ptr_addr(x_1392);
x_1396 = lean_usize_dec_eq(x_1394, x_1395);
if (x_1396 == 0)
{
lean_object* x_1397; lean_object* x_1398; 
lean_dec(x_5);
x_1397 = l_Lean_Expr_proj___override(x_1382, x_1383, x_1392);
x_1398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1398, 0, x_1397);
lean_ctor_set(x_1398, 1, x_1393);
return x_1398;
}
else
{
lean_object* x_1399; 
lean_dec(x_1392);
lean_dec(x_1383);
lean_dec(x_1382);
x_1399 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1399, 0, x_5);
lean_ctor_set(x_1399, 1, x_1393);
return x_1399;
}
}
}
else
{
uint8_t x_1400; 
lean_dec(x_1384);
lean_dec(x_1383);
lean_dec(x_1382);
lean_dec(x_5);
x_1400 = !lean_is_exclusive(x_1385);
if (x_1400 == 0)
{
return x_1385;
}
else
{
lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; 
x_1401 = lean_ctor_get(x_1385, 0);
x_1402 = lean_ctor_get(x_1385, 1);
lean_inc(x_1402);
lean_inc(x_1401);
lean_dec(x_1385);
x_1403 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1403, 0, x_1401);
lean_ctor_set(x_1403, 1, x_1402);
return x_1403;
}
}
}
default: 
{
lean_object* x_1404; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1404, 0, x_5);
lean_ctor_set(x_1404, 1, x_12);
return x_1404;
}
}
}
block_251:
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
x_72 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_54, x_54);
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
x_87 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_54, x_54);
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
x_120 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_102, x_102);
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
x_135 = l_Lean_beqBinderInfo____x40_Lean_Expr___hyg_413_(x_102, x_102);
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
lean_dec(x_5);
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
lean_object* x_162; lean_object* x_163; size_t x_164; size_t x_165; uint8_t x_166; 
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
x_163 = l_Lean_Expr_letE___override(x_147, x_148, x_149, x_150, x_151);
x_164 = lean_ptr_addr(x_148);
lean_dec(x_148);
x_165 = lean_ptr_addr(x_153);
x_166 = lean_usize_dec_eq(x_164, x_165);
if (x_166 == 0)
{
lean_object* x_167; 
lean_dec(x_163);
lean_dec(x_150);
lean_dec(x_149);
x_167 = l_Lean_Expr_letE___override(x_147, x_153, x_156, x_162, x_151);
lean_ctor_set(x_160, 0, x_167);
return x_160;
}
else
{
size_t x_168; size_t x_169; uint8_t x_170; 
x_168 = lean_ptr_addr(x_149);
lean_dec(x_149);
x_169 = lean_ptr_addr(x_156);
x_170 = lean_usize_dec_eq(x_168, x_169);
if (x_170 == 0)
{
lean_object* x_171; 
lean_dec(x_163);
lean_dec(x_150);
x_171 = l_Lean_Expr_letE___override(x_147, x_153, x_156, x_162, x_151);
lean_ctor_set(x_160, 0, x_171);
return x_160;
}
else
{
size_t x_172; size_t x_173; uint8_t x_174; 
x_172 = lean_ptr_addr(x_150);
lean_dec(x_150);
x_173 = lean_ptr_addr(x_162);
x_174 = lean_usize_dec_eq(x_172, x_173);
if (x_174 == 0)
{
lean_object* x_175; 
lean_dec(x_163);
x_175 = l_Lean_Expr_letE___override(x_147, x_153, x_156, x_162, x_151);
lean_ctor_set(x_160, 0, x_175);
return x_160;
}
else
{
lean_dec(x_162);
lean_dec(x_156);
lean_dec(x_153);
lean_dec(x_147);
lean_ctor_set(x_160, 0, x_163);
return x_160;
}
}
}
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; size_t x_179; size_t x_180; uint8_t x_181; 
x_176 = lean_ctor_get(x_160, 0);
x_177 = lean_ctor_get(x_160, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_160);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_inc(x_147);
x_178 = l_Lean_Expr_letE___override(x_147, x_148, x_149, x_150, x_151);
x_179 = lean_ptr_addr(x_148);
lean_dec(x_148);
x_180 = lean_ptr_addr(x_153);
x_181 = lean_usize_dec_eq(x_179, x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; 
lean_dec(x_178);
lean_dec(x_150);
lean_dec(x_149);
x_182 = l_Lean_Expr_letE___override(x_147, x_153, x_156, x_176, x_151);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_177);
return x_183;
}
else
{
size_t x_184; size_t x_185; uint8_t x_186; 
x_184 = lean_ptr_addr(x_149);
lean_dec(x_149);
x_185 = lean_ptr_addr(x_156);
x_186 = lean_usize_dec_eq(x_184, x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; 
lean_dec(x_178);
lean_dec(x_150);
x_187 = l_Lean_Expr_letE___override(x_147, x_153, x_156, x_176, x_151);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_177);
return x_188;
}
else
{
size_t x_189; size_t x_190; uint8_t x_191; 
x_189 = lean_ptr_addr(x_150);
lean_dec(x_150);
x_190 = lean_ptr_addr(x_176);
x_191 = lean_usize_dec_eq(x_189, x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; 
lean_dec(x_178);
x_192 = l_Lean_Expr_letE___override(x_147, x_153, x_156, x_176, x_151);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_192);
lean_ctor_set(x_193, 1, x_177);
return x_193;
}
else
{
lean_object* x_194; 
lean_dec(x_176);
lean_dec(x_156);
lean_dec(x_153);
lean_dec(x_147);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_178);
lean_ctor_set(x_194, 1, x_177);
return x_194;
}
}
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_156);
lean_dec(x_153);
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
x_195 = !lean_is_exclusive(x_160);
if (x_195 == 0)
{
return x_160;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_160, 0);
x_197 = lean_ctor_get(x_160, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_160);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
uint8_t x_199; 
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
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_155);
if (x_199 == 0)
{
return x_155;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_ctor_get(x_155, 0);
x_201 = lean_ctor_get(x_155, 1);
lean_inc(x_201);
lean_inc(x_200);
lean_dec(x_155);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_200);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
}
}
else
{
uint8_t x_203; 
lean_dec(x_150);
lean_dec(x_149);
lean_dec(x_148);
lean_dec(x_147);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_203 = !lean_is_exclusive(x_152);
if (x_203 == 0)
{
return x_152;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_152, 0);
x_205 = lean_ctor_get(x_152, 1);
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_152);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_204);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
case 10:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_5, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_5, 1);
lean_inc(x_208);
lean_inc(x_208);
x_209 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_208, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_209) == 0)
{
uint8_t x_210; 
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
lean_object* x_211; size_t x_212; size_t x_213; uint8_t x_214; 
x_211 = lean_ctor_get(x_209, 0);
x_212 = lean_ptr_addr(x_208);
lean_dec(x_208);
x_213 = lean_ptr_addr(x_211);
x_214 = lean_usize_dec_eq(x_212, x_213);
if (x_214 == 0)
{
lean_object* x_215; 
lean_dec(x_5);
x_215 = l_Lean_Expr_mdata___override(x_207, x_211);
lean_ctor_set(x_209, 0, x_215);
return x_209;
}
else
{
lean_dec(x_211);
lean_dec(x_207);
lean_ctor_set(x_209, 0, x_5);
return x_209;
}
}
else
{
lean_object* x_216; lean_object* x_217; size_t x_218; size_t x_219; uint8_t x_220; 
x_216 = lean_ctor_get(x_209, 0);
x_217 = lean_ctor_get(x_209, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_209);
x_218 = lean_ptr_addr(x_208);
lean_dec(x_208);
x_219 = lean_ptr_addr(x_216);
x_220 = lean_usize_dec_eq(x_218, x_219);
if (x_220 == 0)
{
lean_object* x_221; lean_object* x_222; 
lean_dec(x_5);
x_221 = l_Lean_Expr_mdata___override(x_207, x_216);
x_222 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_222, 0, x_221);
lean_ctor_set(x_222, 1, x_217);
return x_222;
}
else
{
lean_object* x_223; 
lean_dec(x_216);
lean_dec(x_207);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_5);
lean_ctor_set(x_223, 1, x_217);
return x_223;
}
}
}
else
{
uint8_t x_224; 
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_5);
x_224 = !lean_is_exclusive(x_209);
if (x_224 == 0)
{
return x_209;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_209, 0);
x_226 = lean_ctor_get(x_209, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_209);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
case 11:
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_228 = lean_ctor_get(x_5, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_5, 1);
lean_inc(x_229);
x_230 = lean_ctor_get(x_5, 2);
lean_inc(x_230);
lean_inc(x_230);
x_231 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_230, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_231) == 0)
{
uint8_t x_232; 
x_232 = !lean_is_exclusive(x_231);
if (x_232 == 0)
{
lean_object* x_233; size_t x_234; size_t x_235; uint8_t x_236; 
x_233 = lean_ctor_get(x_231, 0);
x_234 = lean_ptr_addr(x_230);
lean_dec(x_230);
x_235 = lean_ptr_addr(x_233);
x_236 = lean_usize_dec_eq(x_234, x_235);
if (x_236 == 0)
{
lean_object* x_237; 
lean_dec(x_5);
x_237 = l_Lean_Expr_proj___override(x_228, x_229, x_233);
lean_ctor_set(x_231, 0, x_237);
return x_231;
}
else
{
lean_dec(x_233);
lean_dec(x_229);
lean_dec(x_228);
lean_ctor_set(x_231, 0, x_5);
return x_231;
}
}
else
{
lean_object* x_238; lean_object* x_239; size_t x_240; size_t x_241; uint8_t x_242; 
x_238 = lean_ctor_get(x_231, 0);
x_239 = lean_ctor_get(x_231, 1);
lean_inc(x_239);
lean_inc(x_238);
lean_dec(x_231);
x_240 = lean_ptr_addr(x_230);
lean_dec(x_230);
x_241 = lean_ptr_addr(x_238);
x_242 = lean_usize_dec_eq(x_240, x_241);
if (x_242 == 0)
{
lean_object* x_243; lean_object* x_244; 
lean_dec(x_5);
x_243 = l_Lean_Expr_proj___override(x_228, x_229, x_238);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_239);
return x_244;
}
else
{
lean_object* x_245; 
lean_dec(x_238);
lean_dec(x_229);
lean_dec(x_228);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_5);
lean_ctor_set(x_245, 1, x_239);
return x_245;
}
}
}
else
{
uint8_t x_246; 
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_5);
x_246 = !lean_is_exclusive(x_231);
if (x_246 == 0)
{
return x_231;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_231, 0);
x_248 = lean_ctor_get(x_231, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_231);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
default: 
{
lean_object* x_250; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_5);
lean_ctor_set(x_250, 1, x_12);
return x_250;
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
x_34 = l_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1336_(x_3, x_33);
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
x_80 = l_Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1336_(x_3, x_79);
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
