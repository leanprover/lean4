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
uint8_t l___private_Init_MetaTypes_0__Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1175_(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_headNumArgs_go(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
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
uint8_t l_Lean_Meta_Occurrences_contains(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Expr_isFVar(lean_object*);
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
x_252 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_67_(x_251, x_3);
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
lean_object* x_258; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
lean_inc(x_5);
x_258 = l_Lean_Meta_isExprDefEq(x_5, x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_258) == 0)
{
lean_object* x_259; uint8_t x_260; 
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_unbox(x_259);
lean_dec(x_259);
if (x_260 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_261 = lean_ctor_get(x_258, 1);
lean_inc(x_261);
lean_dec(x_258);
x_262 = lean_ctor_get(x_5, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_5, 1);
lean_inc(x_263);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_262);
lean_inc(x_1);
x_264 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_262, x_6, x_7, x_8, x_9, x_10, x_11, x_261);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
lean_dec(x_264);
lean_inc(x_263);
x_267 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_263, x_6, x_7, x_8, x_9, x_10, x_11, x_266);
if (lean_obj_tag(x_267) == 0)
{
uint8_t x_268; 
x_268 = !lean_is_exclusive(x_267);
if (x_268 == 0)
{
lean_object* x_269; size_t x_270; size_t x_271; uint8_t x_272; 
x_269 = lean_ctor_get(x_267, 0);
x_270 = lean_ptr_addr(x_262);
lean_dec(x_262);
x_271 = lean_ptr_addr(x_265);
x_272 = lean_usize_dec_eq(x_270, x_271);
if (x_272 == 0)
{
lean_object* x_273; 
lean_dec(x_263);
lean_dec(x_5);
x_273 = l_Lean_Expr_app___override(x_265, x_269);
lean_ctor_set(x_267, 0, x_273);
return x_267;
}
else
{
size_t x_274; size_t x_275; uint8_t x_276; 
x_274 = lean_ptr_addr(x_263);
lean_dec(x_263);
x_275 = lean_ptr_addr(x_269);
x_276 = lean_usize_dec_eq(x_274, x_275);
if (x_276 == 0)
{
lean_object* x_277; 
lean_dec(x_5);
x_277 = l_Lean_Expr_app___override(x_265, x_269);
lean_ctor_set(x_267, 0, x_277);
return x_267;
}
else
{
lean_dec(x_269);
lean_dec(x_265);
lean_ctor_set(x_267, 0, x_5);
return x_267;
}
}
}
else
{
lean_object* x_278; lean_object* x_279; size_t x_280; size_t x_281; uint8_t x_282; 
x_278 = lean_ctor_get(x_267, 0);
x_279 = lean_ctor_get(x_267, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_267);
x_280 = lean_ptr_addr(x_262);
lean_dec(x_262);
x_281 = lean_ptr_addr(x_265);
x_282 = lean_usize_dec_eq(x_280, x_281);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; 
lean_dec(x_263);
lean_dec(x_5);
x_283 = l_Lean_Expr_app___override(x_265, x_278);
x_284 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_284, 0, x_283);
lean_ctor_set(x_284, 1, x_279);
return x_284;
}
else
{
size_t x_285; size_t x_286; uint8_t x_287; 
x_285 = lean_ptr_addr(x_263);
lean_dec(x_263);
x_286 = lean_ptr_addr(x_278);
x_287 = lean_usize_dec_eq(x_285, x_286);
if (x_287 == 0)
{
lean_object* x_288; lean_object* x_289; 
lean_dec(x_5);
x_288 = l_Lean_Expr_app___override(x_265, x_278);
x_289 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_279);
return x_289;
}
else
{
lean_object* x_290; 
lean_dec(x_278);
lean_dec(x_265);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_5);
lean_ctor_set(x_290, 1, x_279);
return x_290;
}
}
}
}
else
{
uint8_t x_291; 
lean_dec(x_265);
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_5);
x_291 = !lean_is_exclusive(x_267);
if (x_291 == 0)
{
return x_267;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_267, 0);
x_293 = lean_ctor_get(x_267, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_267);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
return x_294;
}
}
}
else
{
uint8_t x_295; 
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_295 = !lean_is_exclusive(x_264);
if (x_295 == 0)
{
return x_264;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_264, 0);
x_297 = lean_ctor_get(x_264, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_264);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
return x_298;
}
}
}
case 6:
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; lean_object* x_304; 
x_299 = lean_ctor_get(x_258, 1);
lean_inc(x_299);
lean_dec(x_258);
x_300 = lean_ctor_get(x_5, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_5, 1);
lean_inc(x_301);
x_302 = lean_ctor_get(x_5, 2);
lean_inc(x_302);
x_303 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_301);
lean_inc(x_1);
x_304 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_301, x_6, x_7, x_8, x_9, x_10, x_11, x_299);
if (lean_obj_tag(x_304) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_305 = lean_ctor_get(x_304, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_304, 1);
lean_inc(x_306);
lean_dec(x_304);
x_307 = lean_unsigned_to_nat(1u);
x_308 = lean_nat_add(x_6, x_307);
lean_dec(x_6);
lean_inc(x_302);
x_309 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_302, x_308, x_7, x_8, x_9, x_10, x_11, x_306);
if (lean_obj_tag(x_309) == 0)
{
uint8_t x_310; 
x_310 = !lean_is_exclusive(x_309);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; size_t x_313; size_t x_314; uint8_t x_315; 
x_311 = lean_ctor_get(x_309, 0);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
x_312 = l_Lean_Expr_lam___override(x_300, x_301, x_302, x_303);
x_313 = lean_ptr_addr(x_301);
lean_dec(x_301);
x_314 = lean_ptr_addr(x_305);
x_315 = lean_usize_dec_eq(x_313, x_314);
if (x_315 == 0)
{
lean_object* x_316; 
lean_dec(x_312);
lean_dec(x_302);
x_316 = l_Lean_Expr_lam___override(x_300, x_305, x_311, x_303);
lean_ctor_set(x_309, 0, x_316);
return x_309;
}
else
{
size_t x_317; size_t x_318; uint8_t x_319; 
x_317 = lean_ptr_addr(x_302);
lean_dec(x_302);
x_318 = lean_ptr_addr(x_311);
x_319 = lean_usize_dec_eq(x_317, x_318);
if (x_319 == 0)
{
lean_object* x_320; 
lean_dec(x_312);
x_320 = l_Lean_Expr_lam___override(x_300, x_305, x_311, x_303);
lean_ctor_set(x_309, 0, x_320);
return x_309;
}
else
{
uint8_t x_321; 
x_321 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_303, x_303);
if (x_321 == 0)
{
lean_object* x_322; 
lean_dec(x_312);
x_322 = l_Lean_Expr_lam___override(x_300, x_305, x_311, x_303);
lean_ctor_set(x_309, 0, x_322);
return x_309;
}
else
{
lean_dec(x_311);
lean_dec(x_305);
lean_dec(x_300);
lean_ctor_set(x_309, 0, x_312);
return x_309;
}
}
}
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; size_t x_326; size_t x_327; uint8_t x_328; 
x_323 = lean_ctor_get(x_309, 0);
x_324 = lean_ctor_get(x_309, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_309);
lean_inc(x_302);
lean_inc(x_301);
lean_inc(x_300);
x_325 = l_Lean_Expr_lam___override(x_300, x_301, x_302, x_303);
x_326 = lean_ptr_addr(x_301);
lean_dec(x_301);
x_327 = lean_ptr_addr(x_305);
x_328 = lean_usize_dec_eq(x_326, x_327);
if (x_328 == 0)
{
lean_object* x_329; lean_object* x_330; 
lean_dec(x_325);
lean_dec(x_302);
x_329 = l_Lean_Expr_lam___override(x_300, x_305, x_323, x_303);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_324);
return x_330;
}
else
{
size_t x_331; size_t x_332; uint8_t x_333; 
x_331 = lean_ptr_addr(x_302);
lean_dec(x_302);
x_332 = lean_ptr_addr(x_323);
x_333 = lean_usize_dec_eq(x_331, x_332);
if (x_333 == 0)
{
lean_object* x_334; lean_object* x_335; 
lean_dec(x_325);
x_334 = l_Lean_Expr_lam___override(x_300, x_305, x_323, x_303);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_324);
return x_335;
}
else
{
uint8_t x_336; 
x_336 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_303, x_303);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; 
lean_dec(x_325);
x_337 = l_Lean_Expr_lam___override(x_300, x_305, x_323, x_303);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_337);
lean_ctor_set(x_338, 1, x_324);
return x_338;
}
else
{
lean_object* x_339; 
lean_dec(x_323);
lean_dec(x_305);
lean_dec(x_300);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_325);
lean_ctor_set(x_339, 1, x_324);
return x_339;
}
}
}
}
}
else
{
uint8_t x_340; 
lean_dec(x_305);
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
x_340 = !lean_is_exclusive(x_309);
if (x_340 == 0)
{
return x_309;
}
else
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_341 = lean_ctor_get(x_309, 0);
x_342 = lean_ctor_get(x_309, 1);
lean_inc(x_342);
lean_inc(x_341);
lean_dec(x_309);
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
lean_dec(x_302);
lean_dec(x_301);
lean_dec(x_300);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_344 = !lean_is_exclusive(x_304);
if (x_344 == 0)
{
return x_304;
}
else
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; 
x_345 = lean_ctor_get(x_304, 0);
x_346 = lean_ctor_get(x_304, 1);
lean_inc(x_346);
lean_inc(x_345);
lean_dec(x_304);
x_347 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
return x_347;
}
}
}
case 7:
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; lean_object* x_353; 
x_348 = lean_ctor_get(x_258, 1);
lean_inc(x_348);
lean_dec(x_258);
x_349 = lean_ctor_get(x_5, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_5, 1);
lean_inc(x_350);
x_351 = lean_ctor_get(x_5, 2);
lean_inc(x_351);
x_352 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_350);
lean_inc(x_1);
x_353 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_350, x_6, x_7, x_8, x_9, x_10, x_11, x_348);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_353, 1);
lean_inc(x_355);
lean_dec(x_353);
x_356 = lean_unsigned_to_nat(1u);
x_357 = lean_nat_add(x_6, x_356);
lean_dec(x_6);
lean_inc(x_351);
x_358 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_351, x_357, x_7, x_8, x_9, x_10, x_11, x_355);
if (lean_obj_tag(x_358) == 0)
{
uint8_t x_359; 
x_359 = !lean_is_exclusive(x_358);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; size_t x_362; size_t x_363; uint8_t x_364; 
x_360 = lean_ctor_get(x_358, 0);
lean_inc(x_351);
lean_inc(x_350);
lean_inc(x_349);
x_361 = l_Lean_Expr_forallE___override(x_349, x_350, x_351, x_352);
x_362 = lean_ptr_addr(x_350);
lean_dec(x_350);
x_363 = lean_ptr_addr(x_354);
x_364 = lean_usize_dec_eq(x_362, x_363);
if (x_364 == 0)
{
lean_object* x_365; 
lean_dec(x_361);
lean_dec(x_351);
x_365 = l_Lean_Expr_forallE___override(x_349, x_354, x_360, x_352);
lean_ctor_set(x_358, 0, x_365);
return x_358;
}
else
{
size_t x_366; size_t x_367; uint8_t x_368; 
x_366 = lean_ptr_addr(x_351);
lean_dec(x_351);
x_367 = lean_ptr_addr(x_360);
x_368 = lean_usize_dec_eq(x_366, x_367);
if (x_368 == 0)
{
lean_object* x_369; 
lean_dec(x_361);
x_369 = l_Lean_Expr_forallE___override(x_349, x_354, x_360, x_352);
lean_ctor_set(x_358, 0, x_369);
return x_358;
}
else
{
uint8_t x_370; 
x_370 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_352, x_352);
if (x_370 == 0)
{
lean_object* x_371; 
lean_dec(x_361);
x_371 = l_Lean_Expr_forallE___override(x_349, x_354, x_360, x_352);
lean_ctor_set(x_358, 0, x_371);
return x_358;
}
else
{
lean_dec(x_360);
lean_dec(x_354);
lean_dec(x_349);
lean_ctor_set(x_358, 0, x_361);
return x_358;
}
}
}
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; size_t x_375; size_t x_376; uint8_t x_377; 
x_372 = lean_ctor_get(x_358, 0);
x_373 = lean_ctor_get(x_358, 1);
lean_inc(x_373);
lean_inc(x_372);
lean_dec(x_358);
lean_inc(x_351);
lean_inc(x_350);
lean_inc(x_349);
x_374 = l_Lean_Expr_forallE___override(x_349, x_350, x_351, x_352);
x_375 = lean_ptr_addr(x_350);
lean_dec(x_350);
x_376 = lean_ptr_addr(x_354);
x_377 = lean_usize_dec_eq(x_375, x_376);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; 
lean_dec(x_374);
lean_dec(x_351);
x_378 = l_Lean_Expr_forallE___override(x_349, x_354, x_372, x_352);
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_378);
lean_ctor_set(x_379, 1, x_373);
return x_379;
}
else
{
size_t x_380; size_t x_381; uint8_t x_382; 
x_380 = lean_ptr_addr(x_351);
lean_dec(x_351);
x_381 = lean_ptr_addr(x_372);
x_382 = lean_usize_dec_eq(x_380, x_381);
if (x_382 == 0)
{
lean_object* x_383; lean_object* x_384; 
lean_dec(x_374);
x_383 = l_Lean_Expr_forallE___override(x_349, x_354, x_372, x_352);
x_384 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_384, 0, x_383);
lean_ctor_set(x_384, 1, x_373);
return x_384;
}
else
{
uint8_t x_385; 
x_385 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_352, x_352);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; 
lean_dec(x_374);
x_386 = l_Lean_Expr_forallE___override(x_349, x_354, x_372, x_352);
x_387 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_373);
return x_387;
}
else
{
lean_object* x_388; 
lean_dec(x_372);
lean_dec(x_354);
lean_dec(x_349);
x_388 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_388, 0, x_374);
lean_ctor_set(x_388, 1, x_373);
return x_388;
}
}
}
}
}
else
{
uint8_t x_389; 
lean_dec(x_354);
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_349);
x_389 = !lean_is_exclusive(x_358);
if (x_389 == 0)
{
return x_358;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_358, 0);
x_391 = lean_ctor_get(x_358, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_358);
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
lean_dec(x_351);
lean_dec(x_350);
lean_dec(x_349);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_393 = !lean_is_exclusive(x_353);
if (x_393 == 0)
{
return x_353;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_353, 0);
x_395 = lean_ctor_get(x_353, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_353);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
}
case 8:
{
lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; lean_object* x_403; 
x_397 = lean_ctor_get(x_258, 1);
lean_inc(x_397);
lean_dec(x_258);
x_398 = lean_ctor_get(x_5, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_5, 1);
lean_inc(x_399);
x_400 = lean_ctor_get(x_5, 2);
lean_inc(x_400);
x_401 = lean_ctor_get(x_5, 3);
lean_inc(x_401);
x_402 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_399);
lean_inc(x_1);
x_403 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_399, x_6, x_7, x_8, x_9, x_10, x_11, x_397);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_404 = lean_ctor_get(x_403, 0);
lean_inc(x_404);
x_405 = lean_ctor_get(x_403, 1);
lean_inc(x_405);
lean_dec(x_403);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_400);
lean_inc(x_1);
x_406 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_400, x_6, x_7, x_8, x_9, x_10, x_11, x_405);
if (lean_obj_tag(x_406) == 0)
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
lean_dec(x_406);
x_409 = lean_unsigned_to_nat(1u);
x_410 = lean_nat_add(x_6, x_409);
lean_dec(x_6);
lean_inc(x_401);
x_411 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_401, x_410, x_7, x_8, x_9, x_10, x_11, x_408);
if (lean_obj_tag(x_411) == 0)
{
uint8_t x_412; 
x_412 = !lean_is_exclusive(x_411);
if (x_412 == 0)
{
lean_object* x_413; size_t x_414; size_t x_415; uint8_t x_416; 
x_413 = lean_ctor_get(x_411, 0);
x_414 = lean_ptr_addr(x_399);
lean_dec(x_399);
x_415 = lean_ptr_addr(x_404);
x_416 = lean_usize_dec_eq(x_414, x_415);
if (x_416 == 0)
{
lean_object* x_417; 
lean_dec(x_401);
lean_dec(x_400);
lean_dec(x_5);
x_417 = l_Lean_Expr_letE___override(x_398, x_404, x_407, x_413, x_402);
lean_ctor_set(x_411, 0, x_417);
return x_411;
}
else
{
size_t x_418; size_t x_419; uint8_t x_420; 
x_418 = lean_ptr_addr(x_400);
lean_dec(x_400);
x_419 = lean_ptr_addr(x_407);
x_420 = lean_usize_dec_eq(x_418, x_419);
if (x_420 == 0)
{
lean_object* x_421; 
lean_dec(x_401);
lean_dec(x_5);
x_421 = l_Lean_Expr_letE___override(x_398, x_404, x_407, x_413, x_402);
lean_ctor_set(x_411, 0, x_421);
return x_411;
}
else
{
size_t x_422; size_t x_423; uint8_t x_424; 
x_422 = lean_ptr_addr(x_401);
lean_dec(x_401);
x_423 = lean_ptr_addr(x_413);
x_424 = lean_usize_dec_eq(x_422, x_423);
if (x_424 == 0)
{
lean_object* x_425; 
lean_dec(x_5);
x_425 = l_Lean_Expr_letE___override(x_398, x_404, x_407, x_413, x_402);
lean_ctor_set(x_411, 0, x_425);
return x_411;
}
else
{
lean_dec(x_413);
lean_dec(x_407);
lean_dec(x_404);
lean_dec(x_398);
lean_ctor_set(x_411, 0, x_5);
return x_411;
}
}
}
}
else
{
lean_object* x_426; lean_object* x_427; size_t x_428; size_t x_429; uint8_t x_430; 
x_426 = lean_ctor_get(x_411, 0);
x_427 = lean_ctor_get(x_411, 1);
lean_inc(x_427);
lean_inc(x_426);
lean_dec(x_411);
x_428 = lean_ptr_addr(x_399);
lean_dec(x_399);
x_429 = lean_ptr_addr(x_404);
x_430 = lean_usize_dec_eq(x_428, x_429);
if (x_430 == 0)
{
lean_object* x_431; lean_object* x_432; 
lean_dec(x_401);
lean_dec(x_400);
lean_dec(x_5);
x_431 = l_Lean_Expr_letE___override(x_398, x_404, x_407, x_426, x_402);
x_432 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_432, 0, x_431);
lean_ctor_set(x_432, 1, x_427);
return x_432;
}
else
{
size_t x_433; size_t x_434; uint8_t x_435; 
x_433 = lean_ptr_addr(x_400);
lean_dec(x_400);
x_434 = lean_ptr_addr(x_407);
x_435 = lean_usize_dec_eq(x_433, x_434);
if (x_435 == 0)
{
lean_object* x_436; lean_object* x_437; 
lean_dec(x_401);
lean_dec(x_5);
x_436 = l_Lean_Expr_letE___override(x_398, x_404, x_407, x_426, x_402);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_436);
lean_ctor_set(x_437, 1, x_427);
return x_437;
}
else
{
size_t x_438; size_t x_439; uint8_t x_440; 
x_438 = lean_ptr_addr(x_401);
lean_dec(x_401);
x_439 = lean_ptr_addr(x_426);
x_440 = lean_usize_dec_eq(x_438, x_439);
if (x_440 == 0)
{
lean_object* x_441; lean_object* x_442; 
lean_dec(x_5);
x_441 = l_Lean_Expr_letE___override(x_398, x_404, x_407, x_426, x_402);
x_442 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_442, 0, x_441);
lean_ctor_set(x_442, 1, x_427);
return x_442;
}
else
{
lean_object* x_443; 
lean_dec(x_426);
lean_dec(x_407);
lean_dec(x_404);
lean_dec(x_398);
x_443 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_443, 0, x_5);
lean_ctor_set(x_443, 1, x_427);
return x_443;
}
}
}
}
}
else
{
uint8_t x_444; 
lean_dec(x_407);
lean_dec(x_404);
lean_dec(x_401);
lean_dec(x_400);
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_5);
x_444 = !lean_is_exclusive(x_411);
if (x_444 == 0)
{
return x_411;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_411, 0);
x_446 = lean_ctor_get(x_411, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_411);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
}
else
{
uint8_t x_448; 
lean_dec(x_404);
lean_dec(x_401);
lean_dec(x_400);
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_448 = !lean_is_exclusive(x_406);
if (x_448 == 0)
{
return x_406;
}
else
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_406, 0);
x_450 = lean_ctor_get(x_406, 1);
lean_inc(x_450);
lean_inc(x_449);
lean_dec(x_406);
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
lean_dec(x_401);
lean_dec(x_400);
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_452 = !lean_is_exclusive(x_403);
if (x_452 == 0)
{
return x_403;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; 
x_453 = lean_ctor_get(x_403, 0);
x_454 = lean_ctor_get(x_403, 1);
lean_inc(x_454);
lean_inc(x_453);
lean_dec(x_403);
x_455 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_455, 0, x_453);
lean_ctor_set(x_455, 1, x_454);
return x_455;
}
}
}
case 10:
{
lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_456 = lean_ctor_get(x_258, 1);
lean_inc(x_456);
lean_dec(x_258);
x_457 = lean_ctor_get(x_5, 0);
lean_inc(x_457);
x_458 = lean_ctor_get(x_5, 1);
lean_inc(x_458);
lean_inc(x_458);
x_459 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_458, x_6, x_7, x_8, x_9, x_10, x_11, x_456);
if (lean_obj_tag(x_459) == 0)
{
uint8_t x_460; 
x_460 = !lean_is_exclusive(x_459);
if (x_460 == 0)
{
lean_object* x_461; size_t x_462; size_t x_463; uint8_t x_464; 
x_461 = lean_ctor_get(x_459, 0);
x_462 = lean_ptr_addr(x_458);
lean_dec(x_458);
x_463 = lean_ptr_addr(x_461);
x_464 = lean_usize_dec_eq(x_462, x_463);
if (x_464 == 0)
{
lean_object* x_465; 
lean_dec(x_5);
x_465 = l_Lean_Expr_mdata___override(x_457, x_461);
lean_ctor_set(x_459, 0, x_465);
return x_459;
}
else
{
lean_dec(x_461);
lean_dec(x_457);
lean_ctor_set(x_459, 0, x_5);
return x_459;
}
}
else
{
lean_object* x_466; lean_object* x_467; size_t x_468; size_t x_469; uint8_t x_470; 
x_466 = lean_ctor_get(x_459, 0);
x_467 = lean_ctor_get(x_459, 1);
lean_inc(x_467);
lean_inc(x_466);
lean_dec(x_459);
x_468 = lean_ptr_addr(x_458);
lean_dec(x_458);
x_469 = lean_ptr_addr(x_466);
x_470 = lean_usize_dec_eq(x_468, x_469);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; 
lean_dec(x_5);
x_471 = l_Lean_Expr_mdata___override(x_457, x_466);
x_472 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_472, 0, x_471);
lean_ctor_set(x_472, 1, x_467);
return x_472;
}
else
{
lean_object* x_473; 
lean_dec(x_466);
lean_dec(x_457);
x_473 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_473, 0, x_5);
lean_ctor_set(x_473, 1, x_467);
return x_473;
}
}
}
else
{
uint8_t x_474; 
lean_dec(x_458);
lean_dec(x_457);
lean_dec(x_5);
x_474 = !lean_is_exclusive(x_459);
if (x_474 == 0)
{
return x_459;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = lean_ctor_get(x_459, 0);
x_476 = lean_ctor_get(x_459, 1);
lean_inc(x_476);
lean_inc(x_475);
lean_dec(x_459);
x_477 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_477, 0, x_475);
lean_ctor_set(x_477, 1, x_476);
return x_477;
}
}
}
case 11:
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_478 = lean_ctor_get(x_258, 1);
lean_inc(x_478);
lean_dec(x_258);
x_479 = lean_ctor_get(x_5, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_5, 1);
lean_inc(x_480);
x_481 = lean_ctor_get(x_5, 2);
lean_inc(x_481);
lean_inc(x_481);
x_482 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_481, x_6, x_7, x_8, x_9, x_10, x_11, x_478);
if (lean_obj_tag(x_482) == 0)
{
uint8_t x_483; 
x_483 = !lean_is_exclusive(x_482);
if (x_483 == 0)
{
lean_object* x_484; size_t x_485; size_t x_486; uint8_t x_487; 
x_484 = lean_ctor_get(x_482, 0);
x_485 = lean_ptr_addr(x_481);
lean_dec(x_481);
x_486 = lean_ptr_addr(x_484);
x_487 = lean_usize_dec_eq(x_485, x_486);
if (x_487 == 0)
{
lean_object* x_488; 
lean_dec(x_5);
x_488 = l_Lean_Expr_proj___override(x_479, x_480, x_484);
lean_ctor_set(x_482, 0, x_488);
return x_482;
}
else
{
lean_dec(x_484);
lean_dec(x_480);
lean_dec(x_479);
lean_ctor_set(x_482, 0, x_5);
return x_482;
}
}
else
{
lean_object* x_489; lean_object* x_490; size_t x_491; size_t x_492; uint8_t x_493; 
x_489 = lean_ctor_get(x_482, 0);
x_490 = lean_ctor_get(x_482, 1);
lean_inc(x_490);
lean_inc(x_489);
lean_dec(x_482);
x_491 = lean_ptr_addr(x_481);
lean_dec(x_481);
x_492 = lean_ptr_addr(x_489);
x_493 = lean_usize_dec_eq(x_491, x_492);
if (x_493 == 0)
{
lean_object* x_494; lean_object* x_495; 
lean_dec(x_5);
x_494 = l_Lean_Expr_proj___override(x_479, x_480, x_489);
x_495 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_495, 0, x_494);
lean_ctor_set(x_495, 1, x_490);
return x_495;
}
else
{
lean_object* x_496; 
lean_dec(x_489);
lean_dec(x_480);
lean_dec(x_479);
x_496 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_496, 0, x_5);
lean_ctor_set(x_496, 1, x_490);
return x_496;
}
}
}
else
{
uint8_t x_497; 
lean_dec(x_481);
lean_dec(x_480);
lean_dec(x_479);
lean_dec(x_5);
x_497 = !lean_is_exclusive(x_482);
if (x_497 == 0)
{
return x_482;
}
else
{
lean_object* x_498; lean_object* x_499; lean_object* x_500; 
x_498 = lean_ctor_get(x_482, 0);
x_499 = lean_ctor_get(x_482, 1);
lean_inc(x_499);
lean_inc(x_498);
lean_dec(x_482);
x_500 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_500, 0, x_498);
lean_ctor_set(x_500, 1, x_499);
return x_500;
}
}
}
default: 
{
uint8_t x_501; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_501 = !lean_is_exclusive(x_258);
if (x_501 == 0)
{
lean_object* x_502; 
x_502 = lean_ctor_get(x_258, 0);
lean_dec(x_502);
lean_ctor_set(x_258, 0, x_5);
return x_258;
}
else
{
lean_object* x_503; lean_object* x_504; 
x_503 = lean_ctor_get(x_258, 1);
lean_inc(x_503);
lean_dec(x_258);
x_504 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_504, 0, x_5);
lean_ctor_set(x_504, 1, x_503);
return x_504;
}
}
}
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; uint8_t x_512; 
x_505 = lean_ctor_get(x_258, 1);
lean_inc(x_505);
lean_dec(x_258);
x_506 = lean_st_ref_get(x_7, x_505);
x_507 = lean_ctor_get(x_506, 0);
lean_inc(x_507);
x_508 = lean_ctor_get(x_506, 1);
lean_inc(x_508);
lean_dec(x_506);
x_509 = lean_unsigned_to_nat(1u);
x_510 = lean_nat_add(x_507, x_509);
x_511 = lean_st_ref_set(x_7, x_510, x_508);
x_512 = !lean_is_exclusive(x_511);
if (x_512 == 0)
{
lean_object* x_513; lean_object* x_514; uint8_t x_515; 
x_513 = lean_ctor_get(x_511, 1);
x_514 = lean_ctor_get(x_511, 0);
lean_dec(x_514);
x_515 = l_Lean_Meta_Occurrences_contains(x_2, x_507);
lean_dec(x_507);
if (x_515 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; 
lean_free_object(x_511);
x_516 = lean_ctor_get(x_5, 0);
lean_inc(x_516);
x_517 = lean_ctor_get(x_5, 1);
lean_inc(x_517);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_516);
lean_inc(x_1);
x_518 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_516, x_6, x_7, x_8, x_9, x_10, x_11, x_513);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; 
x_519 = lean_ctor_get(x_518, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_518, 1);
lean_inc(x_520);
lean_dec(x_518);
lean_inc(x_517);
x_521 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_517, x_6, x_7, x_8, x_9, x_10, x_11, x_520);
if (lean_obj_tag(x_521) == 0)
{
uint8_t x_522; 
x_522 = !lean_is_exclusive(x_521);
if (x_522 == 0)
{
lean_object* x_523; size_t x_524; size_t x_525; uint8_t x_526; 
x_523 = lean_ctor_get(x_521, 0);
x_524 = lean_ptr_addr(x_516);
lean_dec(x_516);
x_525 = lean_ptr_addr(x_519);
x_526 = lean_usize_dec_eq(x_524, x_525);
if (x_526 == 0)
{
lean_object* x_527; 
lean_dec(x_517);
lean_dec(x_5);
x_527 = l_Lean_Expr_app___override(x_519, x_523);
lean_ctor_set(x_521, 0, x_527);
return x_521;
}
else
{
size_t x_528; size_t x_529; uint8_t x_530; 
x_528 = lean_ptr_addr(x_517);
lean_dec(x_517);
x_529 = lean_ptr_addr(x_523);
x_530 = lean_usize_dec_eq(x_528, x_529);
if (x_530 == 0)
{
lean_object* x_531; 
lean_dec(x_5);
x_531 = l_Lean_Expr_app___override(x_519, x_523);
lean_ctor_set(x_521, 0, x_531);
return x_521;
}
else
{
lean_dec(x_523);
lean_dec(x_519);
lean_ctor_set(x_521, 0, x_5);
return x_521;
}
}
}
else
{
lean_object* x_532; lean_object* x_533; size_t x_534; size_t x_535; uint8_t x_536; 
x_532 = lean_ctor_get(x_521, 0);
x_533 = lean_ctor_get(x_521, 1);
lean_inc(x_533);
lean_inc(x_532);
lean_dec(x_521);
x_534 = lean_ptr_addr(x_516);
lean_dec(x_516);
x_535 = lean_ptr_addr(x_519);
x_536 = lean_usize_dec_eq(x_534, x_535);
if (x_536 == 0)
{
lean_object* x_537; lean_object* x_538; 
lean_dec(x_517);
lean_dec(x_5);
x_537 = l_Lean_Expr_app___override(x_519, x_532);
x_538 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_538, 0, x_537);
lean_ctor_set(x_538, 1, x_533);
return x_538;
}
else
{
size_t x_539; size_t x_540; uint8_t x_541; 
x_539 = lean_ptr_addr(x_517);
lean_dec(x_517);
x_540 = lean_ptr_addr(x_532);
x_541 = lean_usize_dec_eq(x_539, x_540);
if (x_541 == 0)
{
lean_object* x_542; lean_object* x_543; 
lean_dec(x_5);
x_542 = l_Lean_Expr_app___override(x_519, x_532);
x_543 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_543, 0, x_542);
lean_ctor_set(x_543, 1, x_533);
return x_543;
}
else
{
lean_object* x_544; 
lean_dec(x_532);
lean_dec(x_519);
x_544 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_544, 0, x_5);
lean_ctor_set(x_544, 1, x_533);
return x_544;
}
}
}
}
else
{
uint8_t x_545; 
lean_dec(x_519);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_5);
x_545 = !lean_is_exclusive(x_521);
if (x_545 == 0)
{
return x_521;
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; 
x_546 = lean_ctor_get(x_521, 0);
x_547 = lean_ctor_get(x_521, 1);
lean_inc(x_547);
lean_inc(x_546);
lean_dec(x_521);
x_548 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_548, 0, x_546);
lean_ctor_set(x_548, 1, x_547);
return x_548;
}
}
}
else
{
uint8_t x_549; 
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_549 = !lean_is_exclusive(x_518);
if (x_549 == 0)
{
return x_518;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_550 = lean_ctor_get(x_518, 0);
x_551 = lean_ctor_get(x_518, 1);
lean_inc(x_551);
lean_inc(x_550);
lean_dec(x_518);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
return x_552;
}
}
}
case 6:
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; uint8_t x_556; lean_object* x_557; 
lean_free_object(x_511);
x_553 = lean_ctor_get(x_5, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_5, 1);
lean_inc(x_554);
x_555 = lean_ctor_get(x_5, 2);
lean_inc(x_555);
x_556 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_554);
lean_inc(x_1);
x_557 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_554, x_6, x_7, x_8, x_9, x_10, x_11, x_513);
if (lean_obj_tag(x_557) == 0)
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; 
x_558 = lean_ctor_get(x_557, 0);
lean_inc(x_558);
x_559 = lean_ctor_get(x_557, 1);
lean_inc(x_559);
lean_dec(x_557);
x_560 = lean_nat_add(x_6, x_509);
lean_dec(x_6);
lean_inc(x_555);
x_561 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_555, x_560, x_7, x_8, x_9, x_10, x_11, x_559);
if (lean_obj_tag(x_561) == 0)
{
uint8_t x_562; 
x_562 = !lean_is_exclusive(x_561);
if (x_562 == 0)
{
lean_object* x_563; lean_object* x_564; size_t x_565; size_t x_566; uint8_t x_567; 
x_563 = lean_ctor_get(x_561, 0);
lean_inc(x_555);
lean_inc(x_554);
lean_inc(x_553);
x_564 = l_Lean_Expr_lam___override(x_553, x_554, x_555, x_556);
x_565 = lean_ptr_addr(x_554);
lean_dec(x_554);
x_566 = lean_ptr_addr(x_558);
x_567 = lean_usize_dec_eq(x_565, x_566);
if (x_567 == 0)
{
lean_object* x_568; 
lean_dec(x_564);
lean_dec(x_555);
x_568 = l_Lean_Expr_lam___override(x_553, x_558, x_563, x_556);
lean_ctor_set(x_561, 0, x_568);
return x_561;
}
else
{
size_t x_569; size_t x_570; uint8_t x_571; 
x_569 = lean_ptr_addr(x_555);
lean_dec(x_555);
x_570 = lean_ptr_addr(x_563);
x_571 = lean_usize_dec_eq(x_569, x_570);
if (x_571 == 0)
{
lean_object* x_572; 
lean_dec(x_564);
x_572 = l_Lean_Expr_lam___override(x_553, x_558, x_563, x_556);
lean_ctor_set(x_561, 0, x_572);
return x_561;
}
else
{
uint8_t x_573; 
x_573 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_556, x_556);
if (x_573 == 0)
{
lean_object* x_574; 
lean_dec(x_564);
x_574 = l_Lean_Expr_lam___override(x_553, x_558, x_563, x_556);
lean_ctor_set(x_561, 0, x_574);
return x_561;
}
else
{
lean_dec(x_563);
lean_dec(x_558);
lean_dec(x_553);
lean_ctor_set(x_561, 0, x_564);
return x_561;
}
}
}
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; size_t x_578; size_t x_579; uint8_t x_580; 
x_575 = lean_ctor_get(x_561, 0);
x_576 = lean_ctor_get(x_561, 1);
lean_inc(x_576);
lean_inc(x_575);
lean_dec(x_561);
lean_inc(x_555);
lean_inc(x_554);
lean_inc(x_553);
x_577 = l_Lean_Expr_lam___override(x_553, x_554, x_555, x_556);
x_578 = lean_ptr_addr(x_554);
lean_dec(x_554);
x_579 = lean_ptr_addr(x_558);
x_580 = lean_usize_dec_eq(x_578, x_579);
if (x_580 == 0)
{
lean_object* x_581; lean_object* x_582; 
lean_dec(x_577);
lean_dec(x_555);
x_581 = l_Lean_Expr_lam___override(x_553, x_558, x_575, x_556);
x_582 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_582, 0, x_581);
lean_ctor_set(x_582, 1, x_576);
return x_582;
}
else
{
size_t x_583; size_t x_584; uint8_t x_585; 
x_583 = lean_ptr_addr(x_555);
lean_dec(x_555);
x_584 = lean_ptr_addr(x_575);
x_585 = lean_usize_dec_eq(x_583, x_584);
if (x_585 == 0)
{
lean_object* x_586; lean_object* x_587; 
lean_dec(x_577);
x_586 = l_Lean_Expr_lam___override(x_553, x_558, x_575, x_556);
x_587 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_587, 0, x_586);
lean_ctor_set(x_587, 1, x_576);
return x_587;
}
else
{
uint8_t x_588; 
x_588 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_556, x_556);
if (x_588 == 0)
{
lean_object* x_589; lean_object* x_590; 
lean_dec(x_577);
x_589 = l_Lean_Expr_lam___override(x_553, x_558, x_575, x_556);
x_590 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_590, 0, x_589);
lean_ctor_set(x_590, 1, x_576);
return x_590;
}
else
{
lean_object* x_591; 
lean_dec(x_575);
lean_dec(x_558);
lean_dec(x_553);
x_591 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_591, 0, x_577);
lean_ctor_set(x_591, 1, x_576);
return x_591;
}
}
}
}
}
else
{
uint8_t x_592; 
lean_dec(x_558);
lean_dec(x_555);
lean_dec(x_554);
lean_dec(x_553);
x_592 = !lean_is_exclusive(x_561);
if (x_592 == 0)
{
return x_561;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; 
x_593 = lean_ctor_get(x_561, 0);
x_594 = lean_ctor_get(x_561, 1);
lean_inc(x_594);
lean_inc(x_593);
lean_dec(x_561);
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
lean_dec(x_555);
lean_dec(x_554);
lean_dec(x_553);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_596 = !lean_is_exclusive(x_557);
if (x_596 == 0)
{
return x_557;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_597 = lean_ctor_get(x_557, 0);
x_598 = lean_ctor_get(x_557, 1);
lean_inc(x_598);
lean_inc(x_597);
lean_dec(x_557);
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_597);
lean_ctor_set(x_599, 1, x_598);
return x_599;
}
}
}
case 7:
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; uint8_t x_603; lean_object* x_604; 
lean_free_object(x_511);
x_600 = lean_ctor_get(x_5, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_5, 1);
lean_inc(x_601);
x_602 = lean_ctor_get(x_5, 2);
lean_inc(x_602);
x_603 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_601);
lean_inc(x_1);
x_604 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_601, x_6, x_7, x_8, x_9, x_10, x_11, x_513);
if (lean_obj_tag(x_604) == 0)
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; 
x_605 = lean_ctor_get(x_604, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_604, 1);
lean_inc(x_606);
lean_dec(x_604);
x_607 = lean_nat_add(x_6, x_509);
lean_dec(x_6);
lean_inc(x_602);
x_608 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_602, x_607, x_7, x_8, x_9, x_10, x_11, x_606);
if (lean_obj_tag(x_608) == 0)
{
uint8_t x_609; 
x_609 = !lean_is_exclusive(x_608);
if (x_609 == 0)
{
lean_object* x_610; lean_object* x_611; size_t x_612; size_t x_613; uint8_t x_614; 
x_610 = lean_ctor_get(x_608, 0);
lean_inc(x_602);
lean_inc(x_601);
lean_inc(x_600);
x_611 = l_Lean_Expr_forallE___override(x_600, x_601, x_602, x_603);
x_612 = lean_ptr_addr(x_601);
lean_dec(x_601);
x_613 = lean_ptr_addr(x_605);
x_614 = lean_usize_dec_eq(x_612, x_613);
if (x_614 == 0)
{
lean_object* x_615; 
lean_dec(x_611);
lean_dec(x_602);
x_615 = l_Lean_Expr_forallE___override(x_600, x_605, x_610, x_603);
lean_ctor_set(x_608, 0, x_615);
return x_608;
}
else
{
size_t x_616; size_t x_617; uint8_t x_618; 
x_616 = lean_ptr_addr(x_602);
lean_dec(x_602);
x_617 = lean_ptr_addr(x_610);
x_618 = lean_usize_dec_eq(x_616, x_617);
if (x_618 == 0)
{
lean_object* x_619; 
lean_dec(x_611);
x_619 = l_Lean_Expr_forallE___override(x_600, x_605, x_610, x_603);
lean_ctor_set(x_608, 0, x_619);
return x_608;
}
else
{
uint8_t x_620; 
x_620 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_603, x_603);
if (x_620 == 0)
{
lean_object* x_621; 
lean_dec(x_611);
x_621 = l_Lean_Expr_forallE___override(x_600, x_605, x_610, x_603);
lean_ctor_set(x_608, 0, x_621);
return x_608;
}
else
{
lean_dec(x_610);
lean_dec(x_605);
lean_dec(x_600);
lean_ctor_set(x_608, 0, x_611);
return x_608;
}
}
}
}
else
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; size_t x_625; size_t x_626; uint8_t x_627; 
x_622 = lean_ctor_get(x_608, 0);
x_623 = lean_ctor_get(x_608, 1);
lean_inc(x_623);
lean_inc(x_622);
lean_dec(x_608);
lean_inc(x_602);
lean_inc(x_601);
lean_inc(x_600);
x_624 = l_Lean_Expr_forallE___override(x_600, x_601, x_602, x_603);
x_625 = lean_ptr_addr(x_601);
lean_dec(x_601);
x_626 = lean_ptr_addr(x_605);
x_627 = lean_usize_dec_eq(x_625, x_626);
if (x_627 == 0)
{
lean_object* x_628; lean_object* x_629; 
lean_dec(x_624);
lean_dec(x_602);
x_628 = l_Lean_Expr_forallE___override(x_600, x_605, x_622, x_603);
x_629 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_629, 0, x_628);
lean_ctor_set(x_629, 1, x_623);
return x_629;
}
else
{
size_t x_630; size_t x_631; uint8_t x_632; 
x_630 = lean_ptr_addr(x_602);
lean_dec(x_602);
x_631 = lean_ptr_addr(x_622);
x_632 = lean_usize_dec_eq(x_630, x_631);
if (x_632 == 0)
{
lean_object* x_633; lean_object* x_634; 
lean_dec(x_624);
x_633 = l_Lean_Expr_forallE___override(x_600, x_605, x_622, x_603);
x_634 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_634, 0, x_633);
lean_ctor_set(x_634, 1, x_623);
return x_634;
}
else
{
uint8_t x_635; 
x_635 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_603, x_603);
if (x_635 == 0)
{
lean_object* x_636; lean_object* x_637; 
lean_dec(x_624);
x_636 = l_Lean_Expr_forallE___override(x_600, x_605, x_622, x_603);
x_637 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_637, 0, x_636);
lean_ctor_set(x_637, 1, x_623);
return x_637;
}
else
{
lean_object* x_638; 
lean_dec(x_622);
lean_dec(x_605);
lean_dec(x_600);
x_638 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_638, 0, x_624);
lean_ctor_set(x_638, 1, x_623);
return x_638;
}
}
}
}
}
else
{
uint8_t x_639; 
lean_dec(x_605);
lean_dec(x_602);
lean_dec(x_601);
lean_dec(x_600);
x_639 = !lean_is_exclusive(x_608);
if (x_639 == 0)
{
return x_608;
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; 
x_640 = lean_ctor_get(x_608, 0);
x_641 = lean_ctor_get(x_608, 1);
lean_inc(x_641);
lean_inc(x_640);
lean_dec(x_608);
x_642 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_642, 0, x_640);
lean_ctor_set(x_642, 1, x_641);
return x_642;
}
}
}
else
{
uint8_t x_643; 
lean_dec(x_602);
lean_dec(x_601);
lean_dec(x_600);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_643 = !lean_is_exclusive(x_604);
if (x_643 == 0)
{
return x_604;
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_644 = lean_ctor_get(x_604, 0);
x_645 = lean_ctor_get(x_604, 1);
lean_inc(x_645);
lean_inc(x_644);
lean_dec(x_604);
x_646 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_646, 0, x_644);
lean_ctor_set(x_646, 1, x_645);
return x_646;
}
}
}
case 8:
{
lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; uint8_t x_651; lean_object* x_652; 
lean_free_object(x_511);
x_647 = lean_ctor_get(x_5, 0);
lean_inc(x_647);
x_648 = lean_ctor_get(x_5, 1);
lean_inc(x_648);
x_649 = lean_ctor_get(x_5, 2);
lean_inc(x_649);
x_650 = lean_ctor_get(x_5, 3);
lean_inc(x_650);
x_651 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_648);
lean_inc(x_1);
x_652 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_648, x_6, x_7, x_8, x_9, x_10, x_11, x_513);
if (lean_obj_tag(x_652) == 0)
{
lean_object* x_653; lean_object* x_654; lean_object* x_655; 
x_653 = lean_ctor_get(x_652, 0);
lean_inc(x_653);
x_654 = lean_ctor_get(x_652, 1);
lean_inc(x_654);
lean_dec(x_652);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_649);
lean_inc(x_1);
x_655 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_649, x_6, x_7, x_8, x_9, x_10, x_11, x_654);
if (lean_obj_tag(x_655) == 0)
{
lean_object* x_656; lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_656 = lean_ctor_get(x_655, 0);
lean_inc(x_656);
x_657 = lean_ctor_get(x_655, 1);
lean_inc(x_657);
lean_dec(x_655);
x_658 = lean_nat_add(x_6, x_509);
lean_dec(x_6);
lean_inc(x_650);
x_659 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_650, x_658, x_7, x_8, x_9, x_10, x_11, x_657);
if (lean_obj_tag(x_659) == 0)
{
uint8_t x_660; 
x_660 = !lean_is_exclusive(x_659);
if (x_660 == 0)
{
lean_object* x_661; size_t x_662; size_t x_663; uint8_t x_664; 
x_661 = lean_ctor_get(x_659, 0);
x_662 = lean_ptr_addr(x_648);
lean_dec(x_648);
x_663 = lean_ptr_addr(x_653);
x_664 = lean_usize_dec_eq(x_662, x_663);
if (x_664 == 0)
{
lean_object* x_665; 
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_5);
x_665 = l_Lean_Expr_letE___override(x_647, x_653, x_656, x_661, x_651);
lean_ctor_set(x_659, 0, x_665);
return x_659;
}
else
{
size_t x_666; size_t x_667; uint8_t x_668; 
x_666 = lean_ptr_addr(x_649);
lean_dec(x_649);
x_667 = lean_ptr_addr(x_656);
x_668 = lean_usize_dec_eq(x_666, x_667);
if (x_668 == 0)
{
lean_object* x_669; 
lean_dec(x_650);
lean_dec(x_5);
x_669 = l_Lean_Expr_letE___override(x_647, x_653, x_656, x_661, x_651);
lean_ctor_set(x_659, 0, x_669);
return x_659;
}
else
{
size_t x_670; size_t x_671; uint8_t x_672; 
x_670 = lean_ptr_addr(x_650);
lean_dec(x_650);
x_671 = lean_ptr_addr(x_661);
x_672 = lean_usize_dec_eq(x_670, x_671);
if (x_672 == 0)
{
lean_object* x_673; 
lean_dec(x_5);
x_673 = l_Lean_Expr_letE___override(x_647, x_653, x_656, x_661, x_651);
lean_ctor_set(x_659, 0, x_673);
return x_659;
}
else
{
lean_dec(x_661);
lean_dec(x_656);
lean_dec(x_653);
lean_dec(x_647);
lean_ctor_set(x_659, 0, x_5);
return x_659;
}
}
}
}
else
{
lean_object* x_674; lean_object* x_675; size_t x_676; size_t x_677; uint8_t x_678; 
x_674 = lean_ctor_get(x_659, 0);
x_675 = lean_ctor_get(x_659, 1);
lean_inc(x_675);
lean_inc(x_674);
lean_dec(x_659);
x_676 = lean_ptr_addr(x_648);
lean_dec(x_648);
x_677 = lean_ptr_addr(x_653);
x_678 = lean_usize_dec_eq(x_676, x_677);
if (x_678 == 0)
{
lean_object* x_679; lean_object* x_680; 
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_5);
x_679 = l_Lean_Expr_letE___override(x_647, x_653, x_656, x_674, x_651);
x_680 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_680, 0, x_679);
lean_ctor_set(x_680, 1, x_675);
return x_680;
}
else
{
size_t x_681; size_t x_682; uint8_t x_683; 
x_681 = lean_ptr_addr(x_649);
lean_dec(x_649);
x_682 = lean_ptr_addr(x_656);
x_683 = lean_usize_dec_eq(x_681, x_682);
if (x_683 == 0)
{
lean_object* x_684; lean_object* x_685; 
lean_dec(x_650);
lean_dec(x_5);
x_684 = l_Lean_Expr_letE___override(x_647, x_653, x_656, x_674, x_651);
x_685 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_685, 0, x_684);
lean_ctor_set(x_685, 1, x_675);
return x_685;
}
else
{
size_t x_686; size_t x_687; uint8_t x_688; 
x_686 = lean_ptr_addr(x_650);
lean_dec(x_650);
x_687 = lean_ptr_addr(x_674);
x_688 = lean_usize_dec_eq(x_686, x_687);
if (x_688 == 0)
{
lean_object* x_689; lean_object* x_690; 
lean_dec(x_5);
x_689 = l_Lean_Expr_letE___override(x_647, x_653, x_656, x_674, x_651);
x_690 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_690, 0, x_689);
lean_ctor_set(x_690, 1, x_675);
return x_690;
}
else
{
lean_object* x_691; 
lean_dec(x_674);
lean_dec(x_656);
lean_dec(x_653);
lean_dec(x_647);
x_691 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_691, 0, x_5);
lean_ctor_set(x_691, 1, x_675);
return x_691;
}
}
}
}
}
else
{
uint8_t x_692; 
lean_dec(x_656);
lean_dec(x_653);
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_648);
lean_dec(x_647);
lean_dec(x_5);
x_692 = !lean_is_exclusive(x_659);
if (x_692 == 0)
{
return x_659;
}
else
{
lean_object* x_693; lean_object* x_694; lean_object* x_695; 
x_693 = lean_ctor_get(x_659, 0);
x_694 = lean_ctor_get(x_659, 1);
lean_inc(x_694);
lean_inc(x_693);
lean_dec(x_659);
x_695 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_695, 0, x_693);
lean_ctor_set(x_695, 1, x_694);
return x_695;
}
}
}
else
{
uint8_t x_696; 
lean_dec(x_653);
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_648);
lean_dec(x_647);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_696 = !lean_is_exclusive(x_655);
if (x_696 == 0)
{
return x_655;
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; 
x_697 = lean_ctor_get(x_655, 0);
x_698 = lean_ctor_get(x_655, 1);
lean_inc(x_698);
lean_inc(x_697);
lean_dec(x_655);
x_699 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_699, 0, x_697);
lean_ctor_set(x_699, 1, x_698);
return x_699;
}
}
}
else
{
uint8_t x_700; 
lean_dec(x_650);
lean_dec(x_649);
lean_dec(x_648);
lean_dec(x_647);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_700 = !lean_is_exclusive(x_652);
if (x_700 == 0)
{
return x_652;
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; 
x_701 = lean_ctor_get(x_652, 0);
x_702 = lean_ctor_get(x_652, 1);
lean_inc(x_702);
lean_inc(x_701);
lean_dec(x_652);
x_703 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_703, 0, x_701);
lean_ctor_set(x_703, 1, x_702);
return x_703;
}
}
}
case 10:
{
lean_object* x_704; lean_object* x_705; lean_object* x_706; 
lean_free_object(x_511);
x_704 = lean_ctor_get(x_5, 0);
lean_inc(x_704);
x_705 = lean_ctor_get(x_5, 1);
lean_inc(x_705);
lean_inc(x_705);
x_706 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_705, x_6, x_7, x_8, x_9, x_10, x_11, x_513);
if (lean_obj_tag(x_706) == 0)
{
uint8_t x_707; 
x_707 = !lean_is_exclusive(x_706);
if (x_707 == 0)
{
lean_object* x_708; size_t x_709; size_t x_710; uint8_t x_711; 
x_708 = lean_ctor_get(x_706, 0);
x_709 = lean_ptr_addr(x_705);
lean_dec(x_705);
x_710 = lean_ptr_addr(x_708);
x_711 = lean_usize_dec_eq(x_709, x_710);
if (x_711 == 0)
{
lean_object* x_712; 
lean_dec(x_5);
x_712 = l_Lean_Expr_mdata___override(x_704, x_708);
lean_ctor_set(x_706, 0, x_712);
return x_706;
}
else
{
lean_dec(x_708);
lean_dec(x_704);
lean_ctor_set(x_706, 0, x_5);
return x_706;
}
}
else
{
lean_object* x_713; lean_object* x_714; size_t x_715; size_t x_716; uint8_t x_717; 
x_713 = lean_ctor_get(x_706, 0);
x_714 = lean_ctor_get(x_706, 1);
lean_inc(x_714);
lean_inc(x_713);
lean_dec(x_706);
x_715 = lean_ptr_addr(x_705);
lean_dec(x_705);
x_716 = lean_ptr_addr(x_713);
x_717 = lean_usize_dec_eq(x_715, x_716);
if (x_717 == 0)
{
lean_object* x_718; lean_object* x_719; 
lean_dec(x_5);
x_718 = l_Lean_Expr_mdata___override(x_704, x_713);
x_719 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_719, 0, x_718);
lean_ctor_set(x_719, 1, x_714);
return x_719;
}
else
{
lean_object* x_720; 
lean_dec(x_713);
lean_dec(x_704);
x_720 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_720, 0, x_5);
lean_ctor_set(x_720, 1, x_714);
return x_720;
}
}
}
else
{
uint8_t x_721; 
lean_dec(x_705);
lean_dec(x_704);
lean_dec(x_5);
x_721 = !lean_is_exclusive(x_706);
if (x_721 == 0)
{
return x_706;
}
else
{
lean_object* x_722; lean_object* x_723; lean_object* x_724; 
x_722 = lean_ctor_get(x_706, 0);
x_723 = lean_ctor_get(x_706, 1);
lean_inc(x_723);
lean_inc(x_722);
lean_dec(x_706);
x_724 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_724, 0, x_722);
lean_ctor_set(x_724, 1, x_723);
return x_724;
}
}
}
case 11:
{
lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
lean_free_object(x_511);
x_725 = lean_ctor_get(x_5, 0);
lean_inc(x_725);
x_726 = lean_ctor_get(x_5, 1);
lean_inc(x_726);
x_727 = lean_ctor_get(x_5, 2);
lean_inc(x_727);
lean_inc(x_727);
x_728 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_727, x_6, x_7, x_8, x_9, x_10, x_11, x_513);
if (lean_obj_tag(x_728) == 0)
{
uint8_t x_729; 
x_729 = !lean_is_exclusive(x_728);
if (x_729 == 0)
{
lean_object* x_730; size_t x_731; size_t x_732; uint8_t x_733; 
x_730 = lean_ctor_get(x_728, 0);
x_731 = lean_ptr_addr(x_727);
lean_dec(x_727);
x_732 = lean_ptr_addr(x_730);
x_733 = lean_usize_dec_eq(x_731, x_732);
if (x_733 == 0)
{
lean_object* x_734; 
lean_dec(x_5);
x_734 = l_Lean_Expr_proj___override(x_725, x_726, x_730);
lean_ctor_set(x_728, 0, x_734);
return x_728;
}
else
{
lean_dec(x_730);
lean_dec(x_726);
lean_dec(x_725);
lean_ctor_set(x_728, 0, x_5);
return x_728;
}
}
else
{
lean_object* x_735; lean_object* x_736; size_t x_737; size_t x_738; uint8_t x_739; 
x_735 = lean_ctor_get(x_728, 0);
x_736 = lean_ctor_get(x_728, 1);
lean_inc(x_736);
lean_inc(x_735);
lean_dec(x_728);
x_737 = lean_ptr_addr(x_727);
lean_dec(x_727);
x_738 = lean_ptr_addr(x_735);
x_739 = lean_usize_dec_eq(x_737, x_738);
if (x_739 == 0)
{
lean_object* x_740; lean_object* x_741; 
lean_dec(x_5);
x_740 = l_Lean_Expr_proj___override(x_725, x_726, x_735);
x_741 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_741, 0, x_740);
lean_ctor_set(x_741, 1, x_736);
return x_741;
}
else
{
lean_object* x_742; 
lean_dec(x_735);
lean_dec(x_726);
lean_dec(x_725);
x_742 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_742, 0, x_5);
lean_ctor_set(x_742, 1, x_736);
return x_742;
}
}
}
else
{
uint8_t x_743; 
lean_dec(x_727);
lean_dec(x_726);
lean_dec(x_725);
lean_dec(x_5);
x_743 = !lean_is_exclusive(x_728);
if (x_743 == 0)
{
return x_728;
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; 
x_744 = lean_ctor_get(x_728, 0);
x_745 = lean_ctor_get(x_728, 1);
lean_inc(x_745);
lean_inc(x_744);
lean_dec(x_728);
x_746 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_746, 0, x_744);
lean_ctor_set(x_746, 1, x_745);
return x_746;
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
lean_ctor_set(x_511, 0, x_5);
return x_511;
}
}
}
else
{
lean_object* x_747; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_747 = l_Lean_Expr_bvar___override(x_6);
lean_ctor_set(x_511, 0, x_747);
return x_511;
}
}
else
{
lean_object* x_748; uint8_t x_749; 
x_748 = lean_ctor_get(x_511, 1);
lean_inc(x_748);
lean_dec(x_511);
x_749 = l_Lean_Meta_Occurrences_contains(x_2, x_507);
lean_dec(x_507);
if (x_749 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; 
x_750 = lean_ctor_get(x_5, 0);
lean_inc(x_750);
x_751 = lean_ctor_get(x_5, 1);
lean_inc(x_751);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_750);
lean_inc(x_1);
x_752 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_750, x_6, x_7, x_8, x_9, x_10, x_11, x_748);
if (lean_obj_tag(x_752) == 0)
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; 
x_753 = lean_ctor_get(x_752, 0);
lean_inc(x_753);
x_754 = lean_ctor_get(x_752, 1);
lean_inc(x_754);
lean_dec(x_752);
lean_inc(x_751);
x_755 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_751, x_6, x_7, x_8, x_9, x_10, x_11, x_754);
if (lean_obj_tag(x_755) == 0)
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; size_t x_759; size_t x_760; uint8_t x_761; 
x_756 = lean_ctor_get(x_755, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_755, 1);
lean_inc(x_757);
if (lean_is_exclusive(x_755)) {
 lean_ctor_release(x_755, 0);
 lean_ctor_release(x_755, 1);
 x_758 = x_755;
} else {
 lean_dec_ref(x_755);
 x_758 = lean_box(0);
}
x_759 = lean_ptr_addr(x_750);
lean_dec(x_750);
x_760 = lean_ptr_addr(x_753);
x_761 = lean_usize_dec_eq(x_759, x_760);
if (x_761 == 0)
{
lean_object* x_762; lean_object* x_763; 
lean_dec(x_751);
lean_dec(x_5);
x_762 = l_Lean_Expr_app___override(x_753, x_756);
if (lean_is_scalar(x_758)) {
 x_763 = lean_alloc_ctor(0, 2, 0);
} else {
 x_763 = x_758;
}
lean_ctor_set(x_763, 0, x_762);
lean_ctor_set(x_763, 1, x_757);
return x_763;
}
else
{
size_t x_764; size_t x_765; uint8_t x_766; 
x_764 = lean_ptr_addr(x_751);
lean_dec(x_751);
x_765 = lean_ptr_addr(x_756);
x_766 = lean_usize_dec_eq(x_764, x_765);
if (x_766 == 0)
{
lean_object* x_767; lean_object* x_768; 
lean_dec(x_5);
x_767 = l_Lean_Expr_app___override(x_753, x_756);
if (lean_is_scalar(x_758)) {
 x_768 = lean_alloc_ctor(0, 2, 0);
} else {
 x_768 = x_758;
}
lean_ctor_set(x_768, 0, x_767);
lean_ctor_set(x_768, 1, x_757);
return x_768;
}
else
{
lean_object* x_769; 
lean_dec(x_756);
lean_dec(x_753);
if (lean_is_scalar(x_758)) {
 x_769 = lean_alloc_ctor(0, 2, 0);
} else {
 x_769 = x_758;
}
lean_ctor_set(x_769, 0, x_5);
lean_ctor_set(x_769, 1, x_757);
return x_769;
}
}
}
else
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; 
lean_dec(x_753);
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_5);
x_770 = lean_ctor_get(x_755, 0);
lean_inc(x_770);
x_771 = lean_ctor_get(x_755, 1);
lean_inc(x_771);
if (lean_is_exclusive(x_755)) {
 lean_ctor_release(x_755, 0);
 lean_ctor_release(x_755, 1);
 x_772 = x_755;
} else {
 lean_dec_ref(x_755);
 x_772 = lean_box(0);
}
if (lean_is_scalar(x_772)) {
 x_773 = lean_alloc_ctor(1, 2, 0);
} else {
 x_773 = x_772;
}
lean_ctor_set(x_773, 0, x_770);
lean_ctor_set(x_773, 1, x_771);
return x_773;
}
}
else
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; 
lean_dec(x_751);
lean_dec(x_750);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_774 = lean_ctor_get(x_752, 0);
lean_inc(x_774);
x_775 = lean_ctor_get(x_752, 1);
lean_inc(x_775);
if (lean_is_exclusive(x_752)) {
 lean_ctor_release(x_752, 0);
 lean_ctor_release(x_752, 1);
 x_776 = x_752;
} else {
 lean_dec_ref(x_752);
 x_776 = lean_box(0);
}
if (lean_is_scalar(x_776)) {
 x_777 = lean_alloc_ctor(1, 2, 0);
} else {
 x_777 = x_776;
}
lean_ctor_set(x_777, 0, x_774);
lean_ctor_set(x_777, 1, x_775);
return x_777;
}
}
case 6:
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; uint8_t x_781; lean_object* x_782; 
x_778 = lean_ctor_get(x_5, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_5, 1);
lean_inc(x_779);
x_780 = lean_ctor_get(x_5, 2);
lean_inc(x_780);
x_781 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_779);
lean_inc(x_1);
x_782 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_779, x_6, x_7, x_8, x_9, x_10, x_11, x_748);
if (lean_obj_tag(x_782) == 0)
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; 
x_783 = lean_ctor_get(x_782, 0);
lean_inc(x_783);
x_784 = lean_ctor_get(x_782, 1);
lean_inc(x_784);
lean_dec(x_782);
x_785 = lean_nat_add(x_6, x_509);
lean_dec(x_6);
lean_inc(x_780);
x_786 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_780, x_785, x_7, x_8, x_9, x_10, x_11, x_784);
if (lean_obj_tag(x_786) == 0)
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; size_t x_791; size_t x_792; uint8_t x_793; 
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
lean_inc(x_780);
lean_inc(x_779);
lean_inc(x_778);
x_790 = l_Lean_Expr_lam___override(x_778, x_779, x_780, x_781);
x_791 = lean_ptr_addr(x_779);
lean_dec(x_779);
x_792 = lean_ptr_addr(x_783);
x_793 = lean_usize_dec_eq(x_791, x_792);
if (x_793 == 0)
{
lean_object* x_794; lean_object* x_795; 
lean_dec(x_790);
lean_dec(x_780);
x_794 = l_Lean_Expr_lam___override(x_778, x_783, x_787, x_781);
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
size_t x_796; size_t x_797; uint8_t x_798; 
x_796 = lean_ptr_addr(x_780);
lean_dec(x_780);
x_797 = lean_ptr_addr(x_787);
x_798 = lean_usize_dec_eq(x_796, x_797);
if (x_798 == 0)
{
lean_object* x_799; lean_object* x_800; 
lean_dec(x_790);
x_799 = l_Lean_Expr_lam___override(x_778, x_783, x_787, x_781);
if (lean_is_scalar(x_789)) {
 x_800 = lean_alloc_ctor(0, 2, 0);
} else {
 x_800 = x_789;
}
lean_ctor_set(x_800, 0, x_799);
lean_ctor_set(x_800, 1, x_788);
return x_800;
}
else
{
uint8_t x_801; 
x_801 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_781, x_781);
if (x_801 == 0)
{
lean_object* x_802; lean_object* x_803; 
lean_dec(x_790);
x_802 = l_Lean_Expr_lam___override(x_778, x_783, x_787, x_781);
if (lean_is_scalar(x_789)) {
 x_803 = lean_alloc_ctor(0, 2, 0);
} else {
 x_803 = x_789;
}
lean_ctor_set(x_803, 0, x_802);
lean_ctor_set(x_803, 1, x_788);
return x_803;
}
else
{
lean_object* x_804; 
lean_dec(x_787);
lean_dec(x_783);
lean_dec(x_778);
if (lean_is_scalar(x_789)) {
 x_804 = lean_alloc_ctor(0, 2, 0);
} else {
 x_804 = x_789;
}
lean_ctor_set(x_804, 0, x_790);
lean_ctor_set(x_804, 1, x_788);
return x_804;
}
}
}
}
else
{
lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; 
lean_dec(x_783);
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_778);
x_805 = lean_ctor_get(x_786, 0);
lean_inc(x_805);
x_806 = lean_ctor_get(x_786, 1);
lean_inc(x_806);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 x_807 = x_786;
} else {
 lean_dec_ref(x_786);
 x_807 = lean_box(0);
}
if (lean_is_scalar(x_807)) {
 x_808 = lean_alloc_ctor(1, 2, 0);
} else {
 x_808 = x_807;
}
lean_ctor_set(x_808, 0, x_805);
lean_ctor_set(x_808, 1, x_806);
return x_808;
}
}
else
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; 
lean_dec(x_780);
lean_dec(x_779);
lean_dec(x_778);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_809 = lean_ctor_get(x_782, 0);
lean_inc(x_809);
x_810 = lean_ctor_get(x_782, 1);
lean_inc(x_810);
if (lean_is_exclusive(x_782)) {
 lean_ctor_release(x_782, 0);
 lean_ctor_release(x_782, 1);
 x_811 = x_782;
} else {
 lean_dec_ref(x_782);
 x_811 = lean_box(0);
}
if (lean_is_scalar(x_811)) {
 x_812 = lean_alloc_ctor(1, 2, 0);
} else {
 x_812 = x_811;
}
lean_ctor_set(x_812, 0, x_809);
lean_ctor_set(x_812, 1, x_810);
return x_812;
}
}
case 7:
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; uint8_t x_816; lean_object* x_817; 
x_813 = lean_ctor_get(x_5, 0);
lean_inc(x_813);
x_814 = lean_ctor_get(x_5, 1);
lean_inc(x_814);
x_815 = lean_ctor_get(x_5, 2);
lean_inc(x_815);
x_816 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_814);
lean_inc(x_1);
x_817 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_814, x_6, x_7, x_8, x_9, x_10, x_11, x_748);
if (lean_obj_tag(x_817) == 0)
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; 
x_818 = lean_ctor_get(x_817, 0);
lean_inc(x_818);
x_819 = lean_ctor_get(x_817, 1);
lean_inc(x_819);
lean_dec(x_817);
x_820 = lean_nat_add(x_6, x_509);
lean_dec(x_6);
lean_inc(x_815);
x_821 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_815, x_820, x_7, x_8, x_9, x_10, x_11, x_819);
if (lean_obj_tag(x_821) == 0)
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; size_t x_826; size_t x_827; uint8_t x_828; 
x_822 = lean_ctor_get(x_821, 0);
lean_inc(x_822);
x_823 = lean_ctor_get(x_821, 1);
lean_inc(x_823);
if (lean_is_exclusive(x_821)) {
 lean_ctor_release(x_821, 0);
 lean_ctor_release(x_821, 1);
 x_824 = x_821;
} else {
 lean_dec_ref(x_821);
 x_824 = lean_box(0);
}
lean_inc(x_815);
lean_inc(x_814);
lean_inc(x_813);
x_825 = l_Lean_Expr_forallE___override(x_813, x_814, x_815, x_816);
x_826 = lean_ptr_addr(x_814);
lean_dec(x_814);
x_827 = lean_ptr_addr(x_818);
x_828 = lean_usize_dec_eq(x_826, x_827);
if (x_828 == 0)
{
lean_object* x_829; lean_object* x_830; 
lean_dec(x_825);
lean_dec(x_815);
x_829 = l_Lean_Expr_forallE___override(x_813, x_818, x_822, x_816);
if (lean_is_scalar(x_824)) {
 x_830 = lean_alloc_ctor(0, 2, 0);
} else {
 x_830 = x_824;
}
lean_ctor_set(x_830, 0, x_829);
lean_ctor_set(x_830, 1, x_823);
return x_830;
}
else
{
size_t x_831; size_t x_832; uint8_t x_833; 
x_831 = lean_ptr_addr(x_815);
lean_dec(x_815);
x_832 = lean_ptr_addr(x_822);
x_833 = lean_usize_dec_eq(x_831, x_832);
if (x_833 == 0)
{
lean_object* x_834; lean_object* x_835; 
lean_dec(x_825);
x_834 = l_Lean_Expr_forallE___override(x_813, x_818, x_822, x_816);
if (lean_is_scalar(x_824)) {
 x_835 = lean_alloc_ctor(0, 2, 0);
} else {
 x_835 = x_824;
}
lean_ctor_set(x_835, 0, x_834);
lean_ctor_set(x_835, 1, x_823);
return x_835;
}
else
{
uint8_t x_836; 
x_836 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_816, x_816);
if (x_836 == 0)
{
lean_object* x_837; lean_object* x_838; 
lean_dec(x_825);
x_837 = l_Lean_Expr_forallE___override(x_813, x_818, x_822, x_816);
if (lean_is_scalar(x_824)) {
 x_838 = lean_alloc_ctor(0, 2, 0);
} else {
 x_838 = x_824;
}
lean_ctor_set(x_838, 0, x_837);
lean_ctor_set(x_838, 1, x_823);
return x_838;
}
else
{
lean_object* x_839; 
lean_dec(x_822);
lean_dec(x_818);
lean_dec(x_813);
if (lean_is_scalar(x_824)) {
 x_839 = lean_alloc_ctor(0, 2, 0);
} else {
 x_839 = x_824;
}
lean_ctor_set(x_839, 0, x_825);
lean_ctor_set(x_839, 1, x_823);
return x_839;
}
}
}
}
else
{
lean_object* x_840; lean_object* x_841; lean_object* x_842; lean_object* x_843; 
lean_dec(x_818);
lean_dec(x_815);
lean_dec(x_814);
lean_dec(x_813);
x_840 = lean_ctor_get(x_821, 0);
lean_inc(x_840);
x_841 = lean_ctor_get(x_821, 1);
lean_inc(x_841);
if (lean_is_exclusive(x_821)) {
 lean_ctor_release(x_821, 0);
 lean_ctor_release(x_821, 1);
 x_842 = x_821;
} else {
 lean_dec_ref(x_821);
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
else
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; 
lean_dec(x_815);
lean_dec(x_814);
lean_dec(x_813);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_844 = lean_ctor_get(x_817, 0);
lean_inc(x_844);
x_845 = lean_ctor_get(x_817, 1);
lean_inc(x_845);
if (lean_is_exclusive(x_817)) {
 lean_ctor_release(x_817, 0);
 lean_ctor_release(x_817, 1);
 x_846 = x_817;
} else {
 lean_dec_ref(x_817);
 x_846 = lean_box(0);
}
if (lean_is_scalar(x_846)) {
 x_847 = lean_alloc_ctor(1, 2, 0);
} else {
 x_847 = x_846;
}
lean_ctor_set(x_847, 0, x_844);
lean_ctor_set(x_847, 1, x_845);
return x_847;
}
}
case 8:
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; uint8_t x_852; lean_object* x_853; 
x_848 = lean_ctor_get(x_5, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_5, 1);
lean_inc(x_849);
x_850 = lean_ctor_get(x_5, 2);
lean_inc(x_850);
x_851 = lean_ctor_get(x_5, 3);
lean_inc(x_851);
x_852 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_849);
lean_inc(x_1);
x_853 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_849, x_6, x_7, x_8, x_9, x_10, x_11, x_748);
if (lean_obj_tag(x_853) == 0)
{
lean_object* x_854; lean_object* x_855; lean_object* x_856; 
x_854 = lean_ctor_get(x_853, 0);
lean_inc(x_854);
x_855 = lean_ctor_get(x_853, 1);
lean_inc(x_855);
lean_dec(x_853);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_850);
lean_inc(x_1);
x_856 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_850, x_6, x_7, x_8, x_9, x_10, x_11, x_855);
if (lean_obj_tag(x_856) == 0)
{
lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; 
x_857 = lean_ctor_get(x_856, 0);
lean_inc(x_857);
x_858 = lean_ctor_get(x_856, 1);
lean_inc(x_858);
lean_dec(x_856);
x_859 = lean_nat_add(x_6, x_509);
lean_dec(x_6);
lean_inc(x_851);
x_860 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_851, x_859, x_7, x_8, x_9, x_10, x_11, x_858);
if (lean_obj_tag(x_860) == 0)
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; size_t x_864; size_t x_865; uint8_t x_866; 
x_861 = lean_ctor_get(x_860, 0);
lean_inc(x_861);
x_862 = lean_ctor_get(x_860, 1);
lean_inc(x_862);
if (lean_is_exclusive(x_860)) {
 lean_ctor_release(x_860, 0);
 lean_ctor_release(x_860, 1);
 x_863 = x_860;
} else {
 lean_dec_ref(x_860);
 x_863 = lean_box(0);
}
x_864 = lean_ptr_addr(x_849);
lean_dec(x_849);
x_865 = lean_ptr_addr(x_854);
x_866 = lean_usize_dec_eq(x_864, x_865);
if (x_866 == 0)
{
lean_object* x_867; lean_object* x_868; 
lean_dec(x_851);
lean_dec(x_850);
lean_dec(x_5);
x_867 = l_Lean_Expr_letE___override(x_848, x_854, x_857, x_861, x_852);
if (lean_is_scalar(x_863)) {
 x_868 = lean_alloc_ctor(0, 2, 0);
} else {
 x_868 = x_863;
}
lean_ctor_set(x_868, 0, x_867);
lean_ctor_set(x_868, 1, x_862);
return x_868;
}
else
{
size_t x_869; size_t x_870; uint8_t x_871; 
x_869 = lean_ptr_addr(x_850);
lean_dec(x_850);
x_870 = lean_ptr_addr(x_857);
x_871 = lean_usize_dec_eq(x_869, x_870);
if (x_871 == 0)
{
lean_object* x_872; lean_object* x_873; 
lean_dec(x_851);
lean_dec(x_5);
x_872 = l_Lean_Expr_letE___override(x_848, x_854, x_857, x_861, x_852);
if (lean_is_scalar(x_863)) {
 x_873 = lean_alloc_ctor(0, 2, 0);
} else {
 x_873 = x_863;
}
lean_ctor_set(x_873, 0, x_872);
lean_ctor_set(x_873, 1, x_862);
return x_873;
}
else
{
size_t x_874; size_t x_875; uint8_t x_876; 
x_874 = lean_ptr_addr(x_851);
lean_dec(x_851);
x_875 = lean_ptr_addr(x_861);
x_876 = lean_usize_dec_eq(x_874, x_875);
if (x_876 == 0)
{
lean_object* x_877; lean_object* x_878; 
lean_dec(x_5);
x_877 = l_Lean_Expr_letE___override(x_848, x_854, x_857, x_861, x_852);
if (lean_is_scalar(x_863)) {
 x_878 = lean_alloc_ctor(0, 2, 0);
} else {
 x_878 = x_863;
}
lean_ctor_set(x_878, 0, x_877);
lean_ctor_set(x_878, 1, x_862);
return x_878;
}
else
{
lean_object* x_879; 
lean_dec(x_861);
lean_dec(x_857);
lean_dec(x_854);
lean_dec(x_848);
if (lean_is_scalar(x_863)) {
 x_879 = lean_alloc_ctor(0, 2, 0);
} else {
 x_879 = x_863;
}
lean_ctor_set(x_879, 0, x_5);
lean_ctor_set(x_879, 1, x_862);
return x_879;
}
}
}
}
else
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; 
lean_dec(x_857);
lean_dec(x_854);
lean_dec(x_851);
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_848);
lean_dec(x_5);
x_880 = lean_ctor_get(x_860, 0);
lean_inc(x_880);
x_881 = lean_ctor_get(x_860, 1);
lean_inc(x_881);
if (lean_is_exclusive(x_860)) {
 lean_ctor_release(x_860, 0);
 lean_ctor_release(x_860, 1);
 x_882 = x_860;
} else {
 lean_dec_ref(x_860);
 x_882 = lean_box(0);
}
if (lean_is_scalar(x_882)) {
 x_883 = lean_alloc_ctor(1, 2, 0);
} else {
 x_883 = x_882;
}
lean_ctor_set(x_883, 0, x_880);
lean_ctor_set(x_883, 1, x_881);
return x_883;
}
}
else
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; 
lean_dec(x_854);
lean_dec(x_851);
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_848);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_884 = lean_ctor_get(x_856, 0);
lean_inc(x_884);
x_885 = lean_ctor_get(x_856, 1);
lean_inc(x_885);
if (lean_is_exclusive(x_856)) {
 lean_ctor_release(x_856, 0);
 lean_ctor_release(x_856, 1);
 x_886 = x_856;
} else {
 lean_dec_ref(x_856);
 x_886 = lean_box(0);
}
if (lean_is_scalar(x_886)) {
 x_887 = lean_alloc_ctor(1, 2, 0);
} else {
 x_887 = x_886;
}
lean_ctor_set(x_887, 0, x_884);
lean_ctor_set(x_887, 1, x_885);
return x_887;
}
}
else
{
lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; 
lean_dec(x_851);
lean_dec(x_850);
lean_dec(x_849);
lean_dec(x_848);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_888 = lean_ctor_get(x_853, 0);
lean_inc(x_888);
x_889 = lean_ctor_get(x_853, 1);
lean_inc(x_889);
if (lean_is_exclusive(x_853)) {
 lean_ctor_release(x_853, 0);
 lean_ctor_release(x_853, 1);
 x_890 = x_853;
} else {
 lean_dec_ref(x_853);
 x_890 = lean_box(0);
}
if (lean_is_scalar(x_890)) {
 x_891 = lean_alloc_ctor(1, 2, 0);
} else {
 x_891 = x_890;
}
lean_ctor_set(x_891, 0, x_888);
lean_ctor_set(x_891, 1, x_889);
return x_891;
}
}
case 10:
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_892 = lean_ctor_get(x_5, 0);
lean_inc(x_892);
x_893 = lean_ctor_get(x_5, 1);
lean_inc(x_893);
lean_inc(x_893);
x_894 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_893, x_6, x_7, x_8, x_9, x_10, x_11, x_748);
if (lean_obj_tag(x_894) == 0)
{
lean_object* x_895; lean_object* x_896; lean_object* x_897; size_t x_898; size_t x_899; uint8_t x_900; 
x_895 = lean_ctor_get(x_894, 0);
lean_inc(x_895);
x_896 = lean_ctor_get(x_894, 1);
lean_inc(x_896);
if (lean_is_exclusive(x_894)) {
 lean_ctor_release(x_894, 0);
 lean_ctor_release(x_894, 1);
 x_897 = x_894;
} else {
 lean_dec_ref(x_894);
 x_897 = lean_box(0);
}
x_898 = lean_ptr_addr(x_893);
lean_dec(x_893);
x_899 = lean_ptr_addr(x_895);
x_900 = lean_usize_dec_eq(x_898, x_899);
if (x_900 == 0)
{
lean_object* x_901; lean_object* x_902; 
lean_dec(x_5);
x_901 = l_Lean_Expr_mdata___override(x_892, x_895);
if (lean_is_scalar(x_897)) {
 x_902 = lean_alloc_ctor(0, 2, 0);
} else {
 x_902 = x_897;
}
lean_ctor_set(x_902, 0, x_901);
lean_ctor_set(x_902, 1, x_896);
return x_902;
}
else
{
lean_object* x_903; 
lean_dec(x_895);
lean_dec(x_892);
if (lean_is_scalar(x_897)) {
 x_903 = lean_alloc_ctor(0, 2, 0);
} else {
 x_903 = x_897;
}
lean_ctor_set(x_903, 0, x_5);
lean_ctor_set(x_903, 1, x_896);
return x_903;
}
}
else
{
lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; 
lean_dec(x_893);
lean_dec(x_892);
lean_dec(x_5);
x_904 = lean_ctor_get(x_894, 0);
lean_inc(x_904);
x_905 = lean_ctor_get(x_894, 1);
lean_inc(x_905);
if (lean_is_exclusive(x_894)) {
 lean_ctor_release(x_894, 0);
 lean_ctor_release(x_894, 1);
 x_906 = x_894;
} else {
 lean_dec_ref(x_894);
 x_906 = lean_box(0);
}
if (lean_is_scalar(x_906)) {
 x_907 = lean_alloc_ctor(1, 2, 0);
} else {
 x_907 = x_906;
}
lean_ctor_set(x_907, 0, x_904);
lean_ctor_set(x_907, 1, x_905);
return x_907;
}
}
case 11:
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; 
x_908 = lean_ctor_get(x_5, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_5, 1);
lean_inc(x_909);
x_910 = lean_ctor_get(x_5, 2);
lean_inc(x_910);
lean_inc(x_910);
x_911 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_910, x_6, x_7, x_8, x_9, x_10, x_11, x_748);
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
x_915 = lean_ptr_addr(x_910);
lean_dec(x_910);
x_916 = lean_ptr_addr(x_912);
x_917 = lean_usize_dec_eq(x_915, x_916);
if (x_917 == 0)
{
lean_object* x_918; lean_object* x_919; 
lean_dec(x_5);
x_918 = l_Lean_Expr_proj___override(x_908, x_909, x_912);
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
lean_object* x_920; 
lean_dec(x_912);
lean_dec(x_909);
lean_dec(x_908);
if (lean_is_scalar(x_914)) {
 x_920 = lean_alloc_ctor(0, 2, 0);
} else {
 x_920 = x_914;
}
lean_ctor_set(x_920, 0, x_5);
lean_ctor_set(x_920, 1, x_913);
return x_920;
}
}
else
{
lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; 
lean_dec(x_910);
lean_dec(x_909);
lean_dec(x_908);
lean_dec(x_5);
x_921 = lean_ctor_get(x_911, 0);
lean_inc(x_921);
x_922 = lean_ctor_get(x_911, 1);
lean_inc(x_922);
if (lean_is_exclusive(x_911)) {
 lean_ctor_release(x_911, 0);
 lean_ctor_release(x_911, 1);
 x_923 = x_911;
} else {
 lean_dec_ref(x_911);
 x_923 = lean_box(0);
}
if (lean_is_scalar(x_923)) {
 x_924 = lean_alloc_ctor(1, 2, 0);
} else {
 x_924 = x_923;
}
lean_ctor_set(x_924, 0, x_921);
lean_ctor_set(x_924, 1, x_922);
return x_924;
}
}
default: 
{
lean_object* x_925; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_925 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_925, 0, x_5);
lean_ctor_set(x_925, 1, x_748);
return x_925;
}
}
}
else
{
lean_object* x_926; lean_object* x_927; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_926 = l_Lean_Expr_bvar___override(x_6);
x_927 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_927, 0, x_926);
lean_ctor_set(x_927, 1, x_748);
return x_927;
}
}
}
}
else
{
uint8_t x_928; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_928 = !lean_is_exclusive(x_258);
if (x_928 == 0)
{
return x_258;
}
else
{
lean_object* x_929; lean_object* x_930; lean_object* x_931; 
x_929 = lean_ctor_get(x_258, 0);
x_930 = lean_ctor_get(x_258, 1);
lean_inc(x_930);
lean_inc(x_929);
lean_dec(x_258);
x_931 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_931, 0, x_929);
lean_ctor_set(x_931, 1, x_930);
return x_931;
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
lean_object* x_932; lean_object* x_933; lean_object* x_934; 
x_932 = lean_ctor_get(x_5, 0);
lean_inc(x_932);
x_933 = lean_ctor_get(x_5, 1);
lean_inc(x_933);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_932);
lean_inc(x_1);
x_934 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_932, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_934) == 0)
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; 
x_935 = lean_ctor_get(x_934, 0);
lean_inc(x_935);
x_936 = lean_ctor_get(x_934, 1);
lean_inc(x_936);
lean_dec(x_934);
lean_inc(x_933);
x_937 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_933, x_6, x_7, x_8, x_9, x_10, x_11, x_936);
if (lean_obj_tag(x_937) == 0)
{
uint8_t x_938; 
x_938 = !lean_is_exclusive(x_937);
if (x_938 == 0)
{
lean_object* x_939; size_t x_940; size_t x_941; uint8_t x_942; 
x_939 = lean_ctor_get(x_937, 0);
x_940 = lean_ptr_addr(x_932);
lean_dec(x_932);
x_941 = lean_ptr_addr(x_935);
x_942 = lean_usize_dec_eq(x_940, x_941);
if (x_942 == 0)
{
lean_object* x_943; 
lean_dec(x_933);
lean_dec(x_5);
x_943 = l_Lean_Expr_app___override(x_935, x_939);
lean_ctor_set(x_937, 0, x_943);
return x_937;
}
else
{
size_t x_944; size_t x_945; uint8_t x_946; 
x_944 = lean_ptr_addr(x_933);
lean_dec(x_933);
x_945 = lean_ptr_addr(x_939);
x_946 = lean_usize_dec_eq(x_944, x_945);
if (x_946 == 0)
{
lean_object* x_947; 
lean_dec(x_5);
x_947 = l_Lean_Expr_app___override(x_935, x_939);
lean_ctor_set(x_937, 0, x_947);
return x_937;
}
else
{
lean_dec(x_939);
lean_dec(x_935);
lean_ctor_set(x_937, 0, x_5);
return x_937;
}
}
}
else
{
lean_object* x_948; lean_object* x_949; size_t x_950; size_t x_951; uint8_t x_952; 
x_948 = lean_ctor_get(x_937, 0);
x_949 = lean_ctor_get(x_937, 1);
lean_inc(x_949);
lean_inc(x_948);
lean_dec(x_937);
x_950 = lean_ptr_addr(x_932);
lean_dec(x_932);
x_951 = lean_ptr_addr(x_935);
x_952 = lean_usize_dec_eq(x_950, x_951);
if (x_952 == 0)
{
lean_object* x_953; lean_object* x_954; 
lean_dec(x_933);
lean_dec(x_5);
x_953 = l_Lean_Expr_app___override(x_935, x_948);
x_954 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_954, 0, x_953);
lean_ctor_set(x_954, 1, x_949);
return x_954;
}
else
{
size_t x_955; size_t x_956; uint8_t x_957; 
x_955 = lean_ptr_addr(x_933);
lean_dec(x_933);
x_956 = lean_ptr_addr(x_948);
x_957 = lean_usize_dec_eq(x_955, x_956);
if (x_957 == 0)
{
lean_object* x_958; lean_object* x_959; 
lean_dec(x_5);
x_958 = l_Lean_Expr_app___override(x_935, x_948);
x_959 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_959, 0, x_958);
lean_ctor_set(x_959, 1, x_949);
return x_959;
}
else
{
lean_object* x_960; 
lean_dec(x_948);
lean_dec(x_935);
x_960 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_960, 0, x_5);
lean_ctor_set(x_960, 1, x_949);
return x_960;
}
}
}
}
else
{
uint8_t x_961; 
lean_dec(x_935);
lean_dec(x_933);
lean_dec(x_932);
lean_dec(x_5);
x_961 = !lean_is_exclusive(x_937);
if (x_961 == 0)
{
return x_937;
}
else
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; 
x_962 = lean_ctor_get(x_937, 0);
x_963 = lean_ctor_get(x_937, 1);
lean_inc(x_963);
lean_inc(x_962);
lean_dec(x_937);
x_964 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_964, 0, x_962);
lean_ctor_set(x_964, 1, x_963);
return x_964;
}
}
}
else
{
uint8_t x_965; 
lean_dec(x_933);
lean_dec(x_932);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_965 = !lean_is_exclusive(x_934);
if (x_965 == 0)
{
return x_934;
}
else
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; 
x_966 = lean_ctor_get(x_934, 0);
x_967 = lean_ctor_get(x_934, 1);
lean_inc(x_967);
lean_inc(x_966);
lean_dec(x_934);
x_968 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_968, 0, x_966);
lean_ctor_set(x_968, 1, x_967);
return x_968;
}
}
}
case 6:
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; uint8_t x_972; lean_object* x_973; 
x_969 = lean_ctor_get(x_5, 0);
lean_inc(x_969);
x_970 = lean_ctor_get(x_5, 1);
lean_inc(x_970);
x_971 = lean_ctor_get(x_5, 2);
lean_inc(x_971);
x_972 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_970);
lean_inc(x_1);
x_973 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_970, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_973) == 0)
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; 
x_974 = lean_ctor_get(x_973, 0);
lean_inc(x_974);
x_975 = lean_ctor_get(x_973, 1);
lean_inc(x_975);
lean_dec(x_973);
x_976 = lean_unsigned_to_nat(1u);
x_977 = lean_nat_add(x_6, x_976);
lean_dec(x_6);
lean_inc(x_971);
x_978 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_971, x_977, x_7, x_8, x_9, x_10, x_11, x_975);
if (lean_obj_tag(x_978) == 0)
{
uint8_t x_979; 
x_979 = !lean_is_exclusive(x_978);
if (x_979 == 0)
{
lean_object* x_980; lean_object* x_981; size_t x_982; size_t x_983; uint8_t x_984; 
x_980 = lean_ctor_get(x_978, 0);
lean_inc(x_971);
lean_inc(x_970);
lean_inc(x_969);
x_981 = l_Lean_Expr_lam___override(x_969, x_970, x_971, x_972);
x_982 = lean_ptr_addr(x_970);
lean_dec(x_970);
x_983 = lean_ptr_addr(x_974);
x_984 = lean_usize_dec_eq(x_982, x_983);
if (x_984 == 0)
{
lean_object* x_985; 
lean_dec(x_981);
lean_dec(x_971);
x_985 = l_Lean_Expr_lam___override(x_969, x_974, x_980, x_972);
lean_ctor_set(x_978, 0, x_985);
return x_978;
}
else
{
size_t x_986; size_t x_987; uint8_t x_988; 
x_986 = lean_ptr_addr(x_971);
lean_dec(x_971);
x_987 = lean_ptr_addr(x_980);
x_988 = lean_usize_dec_eq(x_986, x_987);
if (x_988 == 0)
{
lean_object* x_989; 
lean_dec(x_981);
x_989 = l_Lean_Expr_lam___override(x_969, x_974, x_980, x_972);
lean_ctor_set(x_978, 0, x_989);
return x_978;
}
else
{
uint8_t x_990; 
x_990 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_972, x_972);
if (x_990 == 0)
{
lean_object* x_991; 
lean_dec(x_981);
x_991 = l_Lean_Expr_lam___override(x_969, x_974, x_980, x_972);
lean_ctor_set(x_978, 0, x_991);
return x_978;
}
else
{
lean_dec(x_980);
lean_dec(x_974);
lean_dec(x_969);
lean_ctor_set(x_978, 0, x_981);
return x_978;
}
}
}
}
else
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; size_t x_995; size_t x_996; uint8_t x_997; 
x_992 = lean_ctor_get(x_978, 0);
x_993 = lean_ctor_get(x_978, 1);
lean_inc(x_993);
lean_inc(x_992);
lean_dec(x_978);
lean_inc(x_971);
lean_inc(x_970);
lean_inc(x_969);
x_994 = l_Lean_Expr_lam___override(x_969, x_970, x_971, x_972);
x_995 = lean_ptr_addr(x_970);
lean_dec(x_970);
x_996 = lean_ptr_addr(x_974);
x_997 = lean_usize_dec_eq(x_995, x_996);
if (x_997 == 0)
{
lean_object* x_998; lean_object* x_999; 
lean_dec(x_994);
lean_dec(x_971);
x_998 = l_Lean_Expr_lam___override(x_969, x_974, x_992, x_972);
x_999 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_999, 0, x_998);
lean_ctor_set(x_999, 1, x_993);
return x_999;
}
else
{
size_t x_1000; size_t x_1001; uint8_t x_1002; 
x_1000 = lean_ptr_addr(x_971);
lean_dec(x_971);
x_1001 = lean_ptr_addr(x_992);
x_1002 = lean_usize_dec_eq(x_1000, x_1001);
if (x_1002 == 0)
{
lean_object* x_1003; lean_object* x_1004; 
lean_dec(x_994);
x_1003 = l_Lean_Expr_lam___override(x_969, x_974, x_992, x_972);
x_1004 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1004, 0, x_1003);
lean_ctor_set(x_1004, 1, x_993);
return x_1004;
}
else
{
uint8_t x_1005; 
x_1005 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_972, x_972);
if (x_1005 == 0)
{
lean_object* x_1006; lean_object* x_1007; 
lean_dec(x_994);
x_1006 = l_Lean_Expr_lam___override(x_969, x_974, x_992, x_972);
x_1007 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1007, 0, x_1006);
lean_ctor_set(x_1007, 1, x_993);
return x_1007;
}
else
{
lean_object* x_1008; 
lean_dec(x_992);
lean_dec(x_974);
lean_dec(x_969);
x_1008 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1008, 0, x_994);
lean_ctor_set(x_1008, 1, x_993);
return x_1008;
}
}
}
}
}
else
{
uint8_t x_1009; 
lean_dec(x_974);
lean_dec(x_971);
lean_dec(x_970);
lean_dec(x_969);
x_1009 = !lean_is_exclusive(x_978);
if (x_1009 == 0)
{
return x_978;
}
else
{
lean_object* x_1010; lean_object* x_1011; lean_object* x_1012; 
x_1010 = lean_ctor_get(x_978, 0);
x_1011 = lean_ctor_get(x_978, 1);
lean_inc(x_1011);
lean_inc(x_1010);
lean_dec(x_978);
x_1012 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1012, 0, x_1010);
lean_ctor_set(x_1012, 1, x_1011);
return x_1012;
}
}
}
else
{
uint8_t x_1013; 
lean_dec(x_971);
lean_dec(x_970);
lean_dec(x_969);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1013 = !lean_is_exclusive(x_973);
if (x_1013 == 0)
{
return x_973;
}
else
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
x_1014 = lean_ctor_get(x_973, 0);
x_1015 = lean_ctor_get(x_973, 1);
lean_inc(x_1015);
lean_inc(x_1014);
lean_dec(x_973);
x_1016 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1016, 0, x_1014);
lean_ctor_set(x_1016, 1, x_1015);
return x_1016;
}
}
}
case 7:
{
lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; uint8_t x_1020; lean_object* x_1021; 
x_1017 = lean_ctor_get(x_5, 0);
lean_inc(x_1017);
x_1018 = lean_ctor_get(x_5, 1);
lean_inc(x_1018);
x_1019 = lean_ctor_get(x_5, 2);
lean_inc(x_1019);
x_1020 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1018);
lean_inc(x_1);
x_1021 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1018, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1021) == 0)
{
lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; lean_object* x_1025; lean_object* x_1026; 
x_1022 = lean_ctor_get(x_1021, 0);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_1021, 1);
lean_inc(x_1023);
lean_dec(x_1021);
x_1024 = lean_unsigned_to_nat(1u);
x_1025 = lean_nat_add(x_6, x_1024);
lean_dec(x_6);
lean_inc(x_1019);
x_1026 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1019, x_1025, x_7, x_8, x_9, x_10, x_11, x_1023);
if (lean_obj_tag(x_1026) == 0)
{
uint8_t x_1027; 
x_1027 = !lean_is_exclusive(x_1026);
if (x_1027 == 0)
{
lean_object* x_1028; lean_object* x_1029; size_t x_1030; size_t x_1031; uint8_t x_1032; 
x_1028 = lean_ctor_get(x_1026, 0);
lean_inc(x_1019);
lean_inc(x_1018);
lean_inc(x_1017);
x_1029 = l_Lean_Expr_forallE___override(x_1017, x_1018, x_1019, x_1020);
x_1030 = lean_ptr_addr(x_1018);
lean_dec(x_1018);
x_1031 = lean_ptr_addr(x_1022);
x_1032 = lean_usize_dec_eq(x_1030, x_1031);
if (x_1032 == 0)
{
lean_object* x_1033; 
lean_dec(x_1029);
lean_dec(x_1019);
x_1033 = l_Lean_Expr_forallE___override(x_1017, x_1022, x_1028, x_1020);
lean_ctor_set(x_1026, 0, x_1033);
return x_1026;
}
else
{
size_t x_1034; size_t x_1035; uint8_t x_1036; 
x_1034 = lean_ptr_addr(x_1019);
lean_dec(x_1019);
x_1035 = lean_ptr_addr(x_1028);
x_1036 = lean_usize_dec_eq(x_1034, x_1035);
if (x_1036 == 0)
{
lean_object* x_1037; 
lean_dec(x_1029);
x_1037 = l_Lean_Expr_forallE___override(x_1017, x_1022, x_1028, x_1020);
lean_ctor_set(x_1026, 0, x_1037);
return x_1026;
}
else
{
uint8_t x_1038; 
x_1038 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_1020, x_1020);
if (x_1038 == 0)
{
lean_object* x_1039; 
lean_dec(x_1029);
x_1039 = l_Lean_Expr_forallE___override(x_1017, x_1022, x_1028, x_1020);
lean_ctor_set(x_1026, 0, x_1039);
return x_1026;
}
else
{
lean_dec(x_1028);
lean_dec(x_1022);
lean_dec(x_1017);
lean_ctor_set(x_1026, 0, x_1029);
return x_1026;
}
}
}
}
else
{
lean_object* x_1040; lean_object* x_1041; lean_object* x_1042; size_t x_1043; size_t x_1044; uint8_t x_1045; 
x_1040 = lean_ctor_get(x_1026, 0);
x_1041 = lean_ctor_get(x_1026, 1);
lean_inc(x_1041);
lean_inc(x_1040);
lean_dec(x_1026);
lean_inc(x_1019);
lean_inc(x_1018);
lean_inc(x_1017);
x_1042 = l_Lean_Expr_forallE___override(x_1017, x_1018, x_1019, x_1020);
x_1043 = lean_ptr_addr(x_1018);
lean_dec(x_1018);
x_1044 = lean_ptr_addr(x_1022);
x_1045 = lean_usize_dec_eq(x_1043, x_1044);
if (x_1045 == 0)
{
lean_object* x_1046; lean_object* x_1047; 
lean_dec(x_1042);
lean_dec(x_1019);
x_1046 = l_Lean_Expr_forallE___override(x_1017, x_1022, x_1040, x_1020);
x_1047 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1047, 0, x_1046);
lean_ctor_set(x_1047, 1, x_1041);
return x_1047;
}
else
{
size_t x_1048; size_t x_1049; uint8_t x_1050; 
x_1048 = lean_ptr_addr(x_1019);
lean_dec(x_1019);
x_1049 = lean_ptr_addr(x_1040);
x_1050 = lean_usize_dec_eq(x_1048, x_1049);
if (x_1050 == 0)
{
lean_object* x_1051; lean_object* x_1052; 
lean_dec(x_1042);
x_1051 = l_Lean_Expr_forallE___override(x_1017, x_1022, x_1040, x_1020);
x_1052 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1052, 0, x_1051);
lean_ctor_set(x_1052, 1, x_1041);
return x_1052;
}
else
{
uint8_t x_1053; 
x_1053 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_473_(x_1020, x_1020);
if (x_1053 == 0)
{
lean_object* x_1054; lean_object* x_1055; 
lean_dec(x_1042);
x_1054 = l_Lean_Expr_forallE___override(x_1017, x_1022, x_1040, x_1020);
x_1055 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1055, 0, x_1054);
lean_ctor_set(x_1055, 1, x_1041);
return x_1055;
}
else
{
lean_object* x_1056; 
lean_dec(x_1040);
lean_dec(x_1022);
lean_dec(x_1017);
x_1056 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1056, 0, x_1042);
lean_ctor_set(x_1056, 1, x_1041);
return x_1056;
}
}
}
}
}
else
{
uint8_t x_1057; 
lean_dec(x_1022);
lean_dec(x_1019);
lean_dec(x_1018);
lean_dec(x_1017);
x_1057 = !lean_is_exclusive(x_1026);
if (x_1057 == 0)
{
return x_1026;
}
else
{
lean_object* x_1058; lean_object* x_1059; lean_object* x_1060; 
x_1058 = lean_ctor_get(x_1026, 0);
x_1059 = lean_ctor_get(x_1026, 1);
lean_inc(x_1059);
lean_inc(x_1058);
lean_dec(x_1026);
x_1060 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1060, 0, x_1058);
lean_ctor_set(x_1060, 1, x_1059);
return x_1060;
}
}
}
else
{
uint8_t x_1061; 
lean_dec(x_1019);
lean_dec(x_1018);
lean_dec(x_1017);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1061 = !lean_is_exclusive(x_1021);
if (x_1061 == 0)
{
return x_1021;
}
else
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; 
x_1062 = lean_ctor_get(x_1021, 0);
x_1063 = lean_ctor_get(x_1021, 1);
lean_inc(x_1063);
lean_inc(x_1062);
lean_dec(x_1021);
x_1064 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1064, 0, x_1062);
lean_ctor_set(x_1064, 1, x_1063);
return x_1064;
}
}
}
case 8:
{
lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; uint8_t x_1069; lean_object* x_1070; 
x_1065 = lean_ctor_get(x_5, 0);
lean_inc(x_1065);
x_1066 = lean_ctor_get(x_5, 1);
lean_inc(x_1066);
x_1067 = lean_ctor_get(x_5, 2);
lean_inc(x_1067);
x_1068 = lean_ctor_get(x_5, 3);
lean_inc(x_1068);
x_1069 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1066);
lean_inc(x_1);
x_1070 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1066, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1070) == 0)
{
lean_object* x_1071; lean_object* x_1072; lean_object* x_1073; 
x_1071 = lean_ctor_get(x_1070, 0);
lean_inc(x_1071);
x_1072 = lean_ctor_get(x_1070, 1);
lean_inc(x_1072);
lean_dec(x_1070);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1067);
lean_inc(x_1);
x_1073 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1067, x_6, x_7, x_8, x_9, x_10, x_11, x_1072);
if (lean_obj_tag(x_1073) == 0)
{
lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; 
x_1074 = lean_ctor_get(x_1073, 0);
lean_inc(x_1074);
x_1075 = lean_ctor_get(x_1073, 1);
lean_inc(x_1075);
lean_dec(x_1073);
x_1076 = lean_unsigned_to_nat(1u);
x_1077 = lean_nat_add(x_6, x_1076);
lean_dec(x_6);
lean_inc(x_1068);
x_1078 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1068, x_1077, x_7, x_8, x_9, x_10, x_11, x_1075);
if (lean_obj_tag(x_1078) == 0)
{
uint8_t x_1079; 
x_1079 = !lean_is_exclusive(x_1078);
if (x_1079 == 0)
{
lean_object* x_1080; size_t x_1081; size_t x_1082; uint8_t x_1083; 
x_1080 = lean_ctor_get(x_1078, 0);
x_1081 = lean_ptr_addr(x_1066);
lean_dec(x_1066);
x_1082 = lean_ptr_addr(x_1071);
x_1083 = lean_usize_dec_eq(x_1081, x_1082);
if (x_1083 == 0)
{
lean_object* x_1084; 
lean_dec(x_1068);
lean_dec(x_1067);
lean_dec(x_5);
x_1084 = l_Lean_Expr_letE___override(x_1065, x_1071, x_1074, x_1080, x_1069);
lean_ctor_set(x_1078, 0, x_1084);
return x_1078;
}
else
{
size_t x_1085; size_t x_1086; uint8_t x_1087; 
x_1085 = lean_ptr_addr(x_1067);
lean_dec(x_1067);
x_1086 = lean_ptr_addr(x_1074);
x_1087 = lean_usize_dec_eq(x_1085, x_1086);
if (x_1087 == 0)
{
lean_object* x_1088; 
lean_dec(x_1068);
lean_dec(x_5);
x_1088 = l_Lean_Expr_letE___override(x_1065, x_1071, x_1074, x_1080, x_1069);
lean_ctor_set(x_1078, 0, x_1088);
return x_1078;
}
else
{
size_t x_1089; size_t x_1090; uint8_t x_1091; 
x_1089 = lean_ptr_addr(x_1068);
lean_dec(x_1068);
x_1090 = lean_ptr_addr(x_1080);
x_1091 = lean_usize_dec_eq(x_1089, x_1090);
if (x_1091 == 0)
{
lean_object* x_1092; 
lean_dec(x_5);
x_1092 = l_Lean_Expr_letE___override(x_1065, x_1071, x_1074, x_1080, x_1069);
lean_ctor_set(x_1078, 0, x_1092);
return x_1078;
}
else
{
lean_dec(x_1080);
lean_dec(x_1074);
lean_dec(x_1071);
lean_dec(x_1065);
lean_ctor_set(x_1078, 0, x_5);
return x_1078;
}
}
}
}
else
{
lean_object* x_1093; lean_object* x_1094; size_t x_1095; size_t x_1096; uint8_t x_1097; 
x_1093 = lean_ctor_get(x_1078, 0);
x_1094 = lean_ctor_get(x_1078, 1);
lean_inc(x_1094);
lean_inc(x_1093);
lean_dec(x_1078);
x_1095 = lean_ptr_addr(x_1066);
lean_dec(x_1066);
x_1096 = lean_ptr_addr(x_1071);
x_1097 = lean_usize_dec_eq(x_1095, x_1096);
if (x_1097 == 0)
{
lean_object* x_1098; lean_object* x_1099; 
lean_dec(x_1068);
lean_dec(x_1067);
lean_dec(x_5);
x_1098 = l_Lean_Expr_letE___override(x_1065, x_1071, x_1074, x_1093, x_1069);
x_1099 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1099, 0, x_1098);
lean_ctor_set(x_1099, 1, x_1094);
return x_1099;
}
else
{
size_t x_1100; size_t x_1101; uint8_t x_1102; 
x_1100 = lean_ptr_addr(x_1067);
lean_dec(x_1067);
x_1101 = lean_ptr_addr(x_1074);
x_1102 = lean_usize_dec_eq(x_1100, x_1101);
if (x_1102 == 0)
{
lean_object* x_1103; lean_object* x_1104; 
lean_dec(x_1068);
lean_dec(x_5);
x_1103 = l_Lean_Expr_letE___override(x_1065, x_1071, x_1074, x_1093, x_1069);
x_1104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1104, 0, x_1103);
lean_ctor_set(x_1104, 1, x_1094);
return x_1104;
}
else
{
size_t x_1105; size_t x_1106; uint8_t x_1107; 
x_1105 = lean_ptr_addr(x_1068);
lean_dec(x_1068);
x_1106 = lean_ptr_addr(x_1093);
x_1107 = lean_usize_dec_eq(x_1105, x_1106);
if (x_1107 == 0)
{
lean_object* x_1108; lean_object* x_1109; 
lean_dec(x_5);
x_1108 = l_Lean_Expr_letE___override(x_1065, x_1071, x_1074, x_1093, x_1069);
x_1109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1109, 0, x_1108);
lean_ctor_set(x_1109, 1, x_1094);
return x_1109;
}
else
{
lean_object* x_1110; 
lean_dec(x_1093);
lean_dec(x_1074);
lean_dec(x_1071);
lean_dec(x_1065);
x_1110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1110, 0, x_5);
lean_ctor_set(x_1110, 1, x_1094);
return x_1110;
}
}
}
}
}
else
{
uint8_t x_1111; 
lean_dec(x_1074);
lean_dec(x_1071);
lean_dec(x_1068);
lean_dec(x_1067);
lean_dec(x_1066);
lean_dec(x_1065);
lean_dec(x_5);
x_1111 = !lean_is_exclusive(x_1078);
if (x_1111 == 0)
{
return x_1078;
}
else
{
lean_object* x_1112; lean_object* x_1113; lean_object* x_1114; 
x_1112 = lean_ctor_get(x_1078, 0);
x_1113 = lean_ctor_get(x_1078, 1);
lean_inc(x_1113);
lean_inc(x_1112);
lean_dec(x_1078);
x_1114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1114, 0, x_1112);
lean_ctor_set(x_1114, 1, x_1113);
return x_1114;
}
}
}
else
{
uint8_t x_1115; 
lean_dec(x_1071);
lean_dec(x_1068);
lean_dec(x_1067);
lean_dec(x_1066);
lean_dec(x_1065);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1115 = !lean_is_exclusive(x_1073);
if (x_1115 == 0)
{
return x_1073;
}
else
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
x_1116 = lean_ctor_get(x_1073, 0);
x_1117 = lean_ctor_get(x_1073, 1);
lean_inc(x_1117);
lean_inc(x_1116);
lean_dec(x_1073);
x_1118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1118, 0, x_1116);
lean_ctor_set(x_1118, 1, x_1117);
return x_1118;
}
}
}
else
{
uint8_t x_1119; 
lean_dec(x_1068);
lean_dec(x_1067);
lean_dec(x_1066);
lean_dec(x_1065);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1119 = !lean_is_exclusive(x_1070);
if (x_1119 == 0)
{
return x_1070;
}
else
{
lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; 
x_1120 = lean_ctor_get(x_1070, 0);
x_1121 = lean_ctor_get(x_1070, 1);
lean_inc(x_1121);
lean_inc(x_1120);
lean_dec(x_1070);
x_1122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1122, 0, x_1120);
lean_ctor_set(x_1122, 1, x_1121);
return x_1122;
}
}
}
case 10:
{
lean_object* x_1123; lean_object* x_1124; lean_object* x_1125; 
x_1123 = lean_ctor_get(x_5, 0);
lean_inc(x_1123);
x_1124 = lean_ctor_get(x_5, 1);
lean_inc(x_1124);
lean_inc(x_1124);
x_1125 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1124, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1125) == 0)
{
uint8_t x_1126; 
x_1126 = !lean_is_exclusive(x_1125);
if (x_1126 == 0)
{
lean_object* x_1127; size_t x_1128; size_t x_1129; uint8_t x_1130; 
x_1127 = lean_ctor_get(x_1125, 0);
x_1128 = lean_ptr_addr(x_1124);
lean_dec(x_1124);
x_1129 = lean_ptr_addr(x_1127);
x_1130 = lean_usize_dec_eq(x_1128, x_1129);
if (x_1130 == 0)
{
lean_object* x_1131; 
lean_dec(x_5);
x_1131 = l_Lean_Expr_mdata___override(x_1123, x_1127);
lean_ctor_set(x_1125, 0, x_1131);
return x_1125;
}
else
{
lean_dec(x_1127);
lean_dec(x_1123);
lean_ctor_set(x_1125, 0, x_5);
return x_1125;
}
}
else
{
lean_object* x_1132; lean_object* x_1133; size_t x_1134; size_t x_1135; uint8_t x_1136; 
x_1132 = lean_ctor_get(x_1125, 0);
x_1133 = lean_ctor_get(x_1125, 1);
lean_inc(x_1133);
lean_inc(x_1132);
lean_dec(x_1125);
x_1134 = lean_ptr_addr(x_1124);
lean_dec(x_1124);
x_1135 = lean_ptr_addr(x_1132);
x_1136 = lean_usize_dec_eq(x_1134, x_1135);
if (x_1136 == 0)
{
lean_object* x_1137; lean_object* x_1138; 
lean_dec(x_5);
x_1137 = l_Lean_Expr_mdata___override(x_1123, x_1132);
x_1138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1138, 0, x_1137);
lean_ctor_set(x_1138, 1, x_1133);
return x_1138;
}
else
{
lean_object* x_1139; 
lean_dec(x_1132);
lean_dec(x_1123);
x_1139 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1139, 0, x_5);
lean_ctor_set(x_1139, 1, x_1133);
return x_1139;
}
}
}
else
{
uint8_t x_1140; 
lean_dec(x_1124);
lean_dec(x_1123);
lean_dec(x_5);
x_1140 = !lean_is_exclusive(x_1125);
if (x_1140 == 0)
{
return x_1125;
}
else
{
lean_object* x_1141; lean_object* x_1142; lean_object* x_1143; 
x_1141 = lean_ctor_get(x_1125, 0);
x_1142 = lean_ctor_get(x_1125, 1);
lean_inc(x_1142);
lean_inc(x_1141);
lean_dec(x_1125);
x_1143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1143, 0, x_1141);
lean_ctor_set(x_1143, 1, x_1142);
return x_1143;
}
}
}
case 11:
{
lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
x_1144 = lean_ctor_get(x_5, 0);
lean_inc(x_1144);
x_1145 = lean_ctor_get(x_5, 1);
lean_inc(x_1145);
x_1146 = lean_ctor_get(x_5, 2);
lean_inc(x_1146);
lean_inc(x_1146);
x_1147 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1146, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1147) == 0)
{
uint8_t x_1148; 
x_1148 = !lean_is_exclusive(x_1147);
if (x_1148 == 0)
{
lean_object* x_1149; size_t x_1150; size_t x_1151; uint8_t x_1152; 
x_1149 = lean_ctor_get(x_1147, 0);
x_1150 = lean_ptr_addr(x_1146);
lean_dec(x_1146);
x_1151 = lean_ptr_addr(x_1149);
x_1152 = lean_usize_dec_eq(x_1150, x_1151);
if (x_1152 == 0)
{
lean_object* x_1153; 
lean_dec(x_5);
x_1153 = l_Lean_Expr_proj___override(x_1144, x_1145, x_1149);
lean_ctor_set(x_1147, 0, x_1153);
return x_1147;
}
else
{
lean_dec(x_1149);
lean_dec(x_1145);
lean_dec(x_1144);
lean_ctor_set(x_1147, 0, x_5);
return x_1147;
}
}
else
{
lean_object* x_1154; lean_object* x_1155; size_t x_1156; size_t x_1157; uint8_t x_1158; 
x_1154 = lean_ctor_get(x_1147, 0);
x_1155 = lean_ctor_get(x_1147, 1);
lean_inc(x_1155);
lean_inc(x_1154);
lean_dec(x_1147);
x_1156 = lean_ptr_addr(x_1146);
lean_dec(x_1146);
x_1157 = lean_ptr_addr(x_1154);
x_1158 = lean_usize_dec_eq(x_1156, x_1157);
if (x_1158 == 0)
{
lean_object* x_1159; lean_object* x_1160; 
lean_dec(x_5);
x_1159 = l_Lean_Expr_proj___override(x_1144, x_1145, x_1154);
x_1160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1160, 0, x_1159);
lean_ctor_set(x_1160, 1, x_1155);
return x_1160;
}
else
{
lean_object* x_1161; 
lean_dec(x_1154);
lean_dec(x_1145);
lean_dec(x_1144);
x_1161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1161, 0, x_5);
lean_ctor_set(x_1161, 1, x_1155);
return x_1161;
}
}
}
else
{
uint8_t x_1162; 
lean_dec(x_1146);
lean_dec(x_1145);
lean_dec(x_1144);
lean_dec(x_5);
x_1162 = !lean_is_exclusive(x_1147);
if (x_1162 == 0)
{
return x_1147;
}
else
{
lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; 
x_1163 = lean_ctor_get(x_1147, 0);
x_1164 = lean_ctor_get(x_1147, 1);
lean_inc(x_1164);
lean_inc(x_1163);
lean_dec(x_1147);
x_1165 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1165, 0, x_1163);
lean_ctor_set(x_1165, 1, x_1164);
return x_1165;
}
}
}
default: 
{
lean_object* x_1166; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1166, 0, x_5);
lean_ctor_set(x_1166, 1, x_12);
return x_1166;
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
lean_dec(x_3);
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
lean_inc(x_3);
x_34 = l___private_Init_MetaTypes_0__Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1175_(x_3, x_33);
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
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_dec(x_3);
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
lean_inc(x_3);
x_79 = l___private_Init_MetaTypes_0__Lean_Meta_beqOccurrences____x40_Init_MetaTypes___hyg_1175_(x_3, x_78);
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
lean_dec(x_3);
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
lean_dec(x_3);
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
