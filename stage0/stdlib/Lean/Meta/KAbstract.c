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
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headNumArgs_go(lean_object*, lean_object*);
uint8_t l_Lean_Occurrences_contains(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_67_(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Occurrences_0__Lean_beqOccurrences____x40_Lean_Data_Occurrences___hyg_32_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(uint8_t, uint8_t);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_kabstract___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_kabstract___closed__1;
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
x_321 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_303, x_303);
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
x_336 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_303, x_303);
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
x_370 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_352, x_352);
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
x_385 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_352, x_352);
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
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; uint8_t x_516; 
x_505 = lean_ctor_get(x_258, 1);
lean_inc(x_505);
lean_dec(x_258);
x_506 = lean_st_ref_get(x_11, x_505);
x_507 = lean_ctor_get(x_506, 1);
lean_inc(x_507);
lean_dec(x_506);
x_508 = lean_st_ref_get(x_7, x_507);
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_508, 1);
lean_inc(x_510);
lean_dec(x_508);
x_511 = lean_unsigned_to_nat(1u);
x_512 = lean_nat_add(x_509, x_511);
x_513 = lean_st_ref_get(x_11, x_510);
x_514 = lean_ctor_get(x_513, 1);
lean_inc(x_514);
lean_dec(x_513);
x_515 = lean_st_ref_set(x_7, x_512, x_514);
x_516 = !lean_is_exclusive(x_515);
if (x_516 == 0)
{
lean_object* x_517; lean_object* x_518; uint8_t x_519; 
x_517 = lean_ctor_get(x_515, 1);
x_518 = lean_ctor_get(x_515, 0);
lean_dec(x_518);
x_519 = l_Lean_Occurrences_contains(x_2, x_509);
lean_dec(x_509);
if (x_519 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_free_object(x_515);
x_520 = lean_ctor_get(x_5, 0);
lean_inc(x_520);
x_521 = lean_ctor_get(x_5, 1);
lean_inc(x_521);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_520);
lean_inc(x_1);
x_522 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_520, x_6, x_7, x_8, x_9, x_10, x_11, x_517);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_523 = lean_ctor_get(x_522, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_522, 1);
lean_inc(x_524);
lean_dec(x_522);
lean_inc(x_521);
x_525 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_521, x_6, x_7, x_8, x_9, x_10, x_11, x_524);
if (lean_obj_tag(x_525) == 0)
{
uint8_t x_526; 
x_526 = !lean_is_exclusive(x_525);
if (x_526 == 0)
{
lean_object* x_527; size_t x_528; size_t x_529; uint8_t x_530; 
x_527 = lean_ctor_get(x_525, 0);
x_528 = lean_ptr_addr(x_520);
lean_dec(x_520);
x_529 = lean_ptr_addr(x_523);
x_530 = lean_usize_dec_eq(x_528, x_529);
if (x_530 == 0)
{
lean_object* x_531; 
lean_dec(x_521);
lean_dec(x_5);
x_531 = l_Lean_Expr_app___override(x_523, x_527);
lean_ctor_set(x_525, 0, x_531);
return x_525;
}
else
{
size_t x_532; size_t x_533; uint8_t x_534; 
x_532 = lean_ptr_addr(x_521);
lean_dec(x_521);
x_533 = lean_ptr_addr(x_527);
x_534 = lean_usize_dec_eq(x_532, x_533);
if (x_534 == 0)
{
lean_object* x_535; 
lean_dec(x_5);
x_535 = l_Lean_Expr_app___override(x_523, x_527);
lean_ctor_set(x_525, 0, x_535);
return x_525;
}
else
{
lean_dec(x_527);
lean_dec(x_523);
lean_ctor_set(x_525, 0, x_5);
return x_525;
}
}
}
else
{
lean_object* x_536; lean_object* x_537; size_t x_538; size_t x_539; uint8_t x_540; 
x_536 = lean_ctor_get(x_525, 0);
x_537 = lean_ctor_get(x_525, 1);
lean_inc(x_537);
lean_inc(x_536);
lean_dec(x_525);
x_538 = lean_ptr_addr(x_520);
lean_dec(x_520);
x_539 = lean_ptr_addr(x_523);
x_540 = lean_usize_dec_eq(x_538, x_539);
if (x_540 == 0)
{
lean_object* x_541; lean_object* x_542; 
lean_dec(x_521);
lean_dec(x_5);
x_541 = l_Lean_Expr_app___override(x_523, x_536);
x_542 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_542, 0, x_541);
lean_ctor_set(x_542, 1, x_537);
return x_542;
}
else
{
size_t x_543; size_t x_544; uint8_t x_545; 
x_543 = lean_ptr_addr(x_521);
lean_dec(x_521);
x_544 = lean_ptr_addr(x_536);
x_545 = lean_usize_dec_eq(x_543, x_544);
if (x_545 == 0)
{
lean_object* x_546; lean_object* x_547; 
lean_dec(x_5);
x_546 = l_Lean_Expr_app___override(x_523, x_536);
x_547 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_547, 0, x_546);
lean_ctor_set(x_547, 1, x_537);
return x_547;
}
else
{
lean_object* x_548; 
lean_dec(x_536);
lean_dec(x_523);
x_548 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_548, 0, x_5);
lean_ctor_set(x_548, 1, x_537);
return x_548;
}
}
}
}
else
{
uint8_t x_549; 
lean_dec(x_523);
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_5);
x_549 = !lean_is_exclusive(x_525);
if (x_549 == 0)
{
return x_525;
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_550 = lean_ctor_get(x_525, 0);
x_551 = lean_ctor_get(x_525, 1);
lean_inc(x_551);
lean_inc(x_550);
lean_dec(x_525);
x_552 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_552, 0, x_550);
lean_ctor_set(x_552, 1, x_551);
return x_552;
}
}
}
else
{
uint8_t x_553; 
lean_dec(x_521);
lean_dec(x_520);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_553 = !lean_is_exclusive(x_522);
if (x_553 == 0)
{
return x_522;
}
else
{
lean_object* x_554; lean_object* x_555; lean_object* x_556; 
x_554 = lean_ctor_get(x_522, 0);
x_555 = lean_ctor_get(x_522, 1);
lean_inc(x_555);
lean_inc(x_554);
lean_dec(x_522);
x_556 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_556, 0, x_554);
lean_ctor_set(x_556, 1, x_555);
return x_556;
}
}
}
case 6:
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; uint8_t x_560; lean_object* x_561; 
lean_free_object(x_515);
x_557 = lean_ctor_get(x_5, 0);
lean_inc(x_557);
x_558 = lean_ctor_get(x_5, 1);
lean_inc(x_558);
x_559 = lean_ctor_get(x_5, 2);
lean_inc(x_559);
x_560 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_558);
lean_inc(x_1);
x_561 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_558, x_6, x_7, x_8, x_9, x_10, x_11, x_517);
if (lean_obj_tag(x_561) == 0)
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; 
x_562 = lean_ctor_get(x_561, 0);
lean_inc(x_562);
x_563 = lean_ctor_get(x_561, 1);
lean_inc(x_563);
lean_dec(x_561);
x_564 = lean_nat_add(x_6, x_511);
lean_dec(x_6);
lean_inc(x_559);
x_565 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_559, x_564, x_7, x_8, x_9, x_10, x_11, x_563);
if (lean_obj_tag(x_565) == 0)
{
uint8_t x_566; 
x_566 = !lean_is_exclusive(x_565);
if (x_566 == 0)
{
lean_object* x_567; lean_object* x_568; size_t x_569; size_t x_570; uint8_t x_571; 
x_567 = lean_ctor_get(x_565, 0);
lean_inc(x_559);
lean_inc(x_558);
lean_inc(x_557);
x_568 = l_Lean_Expr_lam___override(x_557, x_558, x_559, x_560);
x_569 = lean_ptr_addr(x_558);
lean_dec(x_558);
x_570 = lean_ptr_addr(x_562);
x_571 = lean_usize_dec_eq(x_569, x_570);
if (x_571 == 0)
{
lean_object* x_572; 
lean_dec(x_568);
lean_dec(x_559);
x_572 = l_Lean_Expr_lam___override(x_557, x_562, x_567, x_560);
lean_ctor_set(x_565, 0, x_572);
return x_565;
}
else
{
size_t x_573; size_t x_574; uint8_t x_575; 
x_573 = lean_ptr_addr(x_559);
lean_dec(x_559);
x_574 = lean_ptr_addr(x_567);
x_575 = lean_usize_dec_eq(x_573, x_574);
if (x_575 == 0)
{
lean_object* x_576; 
lean_dec(x_568);
x_576 = l_Lean_Expr_lam___override(x_557, x_562, x_567, x_560);
lean_ctor_set(x_565, 0, x_576);
return x_565;
}
else
{
uint8_t x_577; 
x_577 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_560, x_560);
if (x_577 == 0)
{
lean_object* x_578; 
lean_dec(x_568);
x_578 = l_Lean_Expr_lam___override(x_557, x_562, x_567, x_560);
lean_ctor_set(x_565, 0, x_578);
return x_565;
}
else
{
lean_dec(x_567);
lean_dec(x_562);
lean_dec(x_557);
lean_ctor_set(x_565, 0, x_568);
return x_565;
}
}
}
}
else
{
lean_object* x_579; lean_object* x_580; lean_object* x_581; size_t x_582; size_t x_583; uint8_t x_584; 
x_579 = lean_ctor_get(x_565, 0);
x_580 = lean_ctor_get(x_565, 1);
lean_inc(x_580);
lean_inc(x_579);
lean_dec(x_565);
lean_inc(x_559);
lean_inc(x_558);
lean_inc(x_557);
x_581 = l_Lean_Expr_lam___override(x_557, x_558, x_559, x_560);
x_582 = lean_ptr_addr(x_558);
lean_dec(x_558);
x_583 = lean_ptr_addr(x_562);
x_584 = lean_usize_dec_eq(x_582, x_583);
if (x_584 == 0)
{
lean_object* x_585; lean_object* x_586; 
lean_dec(x_581);
lean_dec(x_559);
x_585 = l_Lean_Expr_lam___override(x_557, x_562, x_579, x_560);
x_586 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_586, 0, x_585);
lean_ctor_set(x_586, 1, x_580);
return x_586;
}
else
{
size_t x_587; size_t x_588; uint8_t x_589; 
x_587 = lean_ptr_addr(x_559);
lean_dec(x_559);
x_588 = lean_ptr_addr(x_579);
x_589 = lean_usize_dec_eq(x_587, x_588);
if (x_589 == 0)
{
lean_object* x_590; lean_object* x_591; 
lean_dec(x_581);
x_590 = l_Lean_Expr_lam___override(x_557, x_562, x_579, x_560);
x_591 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_591, 0, x_590);
lean_ctor_set(x_591, 1, x_580);
return x_591;
}
else
{
uint8_t x_592; 
x_592 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_560, x_560);
if (x_592 == 0)
{
lean_object* x_593; lean_object* x_594; 
lean_dec(x_581);
x_593 = l_Lean_Expr_lam___override(x_557, x_562, x_579, x_560);
x_594 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_594, 0, x_593);
lean_ctor_set(x_594, 1, x_580);
return x_594;
}
else
{
lean_object* x_595; 
lean_dec(x_579);
lean_dec(x_562);
lean_dec(x_557);
x_595 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_595, 0, x_581);
lean_ctor_set(x_595, 1, x_580);
return x_595;
}
}
}
}
}
else
{
uint8_t x_596; 
lean_dec(x_562);
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_557);
x_596 = !lean_is_exclusive(x_565);
if (x_596 == 0)
{
return x_565;
}
else
{
lean_object* x_597; lean_object* x_598; lean_object* x_599; 
x_597 = lean_ctor_get(x_565, 0);
x_598 = lean_ctor_get(x_565, 1);
lean_inc(x_598);
lean_inc(x_597);
lean_dec(x_565);
x_599 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_599, 0, x_597);
lean_ctor_set(x_599, 1, x_598);
return x_599;
}
}
}
else
{
uint8_t x_600; 
lean_dec(x_559);
lean_dec(x_558);
lean_dec(x_557);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_600 = !lean_is_exclusive(x_561);
if (x_600 == 0)
{
return x_561;
}
else
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; 
x_601 = lean_ctor_get(x_561, 0);
x_602 = lean_ctor_get(x_561, 1);
lean_inc(x_602);
lean_inc(x_601);
lean_dec(x_561);
x_603 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_603, 0, x_601);
lean_ctor_set(x_603, 1, x_602);
return x_603;
}
}
}
case 7:
{
lean_object* x_604; lean_object* x_605; lean_object* x_606; uint8_t x_607; lean_object* x_608; 
lean_free_object(x_515);
x_604 = lean_ctor_get(x_5, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_5, 1);
lean_inc(x_605);
x_606 = lean_ctor_get(x_5, 2);
lean_inc(x_606);
x_607 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_605);
lean_inc(x_1);
x_608 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_605, x_6, x_7, x_8, x_9, x_10, x_11, x_517);
if (lean_obj_tag(x_608) == 0)
{
lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
x_609 = lean_ctor_get(x_608, 0);
lean_inc(x_609);
x_610 = lean_ctor_get(x_608, 1);
lean_inc(x_610);
lean_dec(x_608);
x_611 = lean_nat_add(x_6, x_511);
lean_dec(x_6);
lean_inc(x_606);
x_612 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_606, x_611, x_7, x_8, x_9, x_10, x_11, x_610);
if (lean_obj_tag(x_612) == 0)
{
uint8_t x_613; 
x_613 = !lean_is_exclusive(x_612);
if (x_613 == 0)
{
lean_object* x_614; lean_object* x_615; size_t x_616; size_t x_617; uint8_t x_618; 
x_614 = lean_ctor_get(x_612, 0);
lean_inc(x_606);
lean_inc(x_605);
lean_inc(x_604);
x_615 = l_Lean_Expr_forallE___override(x_604, x_605, x_606, x_607);
x_616 = lean_ptr_addr(x_605);
lean_dec(x_605);
x_617 = lean_ptr_addr(x_609);
x_618 = lean_usize_dec_eq(x_616, x_617);
if (x_618 == 0)
{
lean_object* x_619; 
lean_dec(x_615);
lean_dec(x_606);
x_619 = l_Lean_Expr_forallE___override(x_604, x_609, x_614, x_607);
lean_ctor_set(x_612, 0, x_619);
return x_612;
}
else
{
size_t x_620; size_t x_621; uint8_t x_622; 
x_620 = lean_ptr_addr(x_606);
lean_dec(x_606);
x_621 = lean_ptr_addr(x_614);
x_622 = lean_usize_dec_eq(x_620, x_621);
if (x_622 == 0)
{
lean_object* x_623; 
lean_dec(x_615);
x_623 = l_Lean_Expr_forallE___override(x_604, x_609, x_614, x_607);
lean_ctor_set(x_612, 0, x_623);
return x_612;
}
else
{
uint8_t x_624; 
x_624 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_607, x_607);
if (x_624 == 0)
{
lean_object* x_625; 
lean_dec(x_615);
x_625 = l_Lean_Expr_forallE___override(x_604, x_609, x_614, x_607);
lean_ctor_set(x_612, 0, x_625);
return x_612;
}
else
{
lean_dec(x_614);
lean_dec(x_609);
lean_dec(x_604);
lean_ctor_set(x_612, 0, x_615);
return x_612;
}
}
}
}
else
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; size_t x_629; size_t x_630; uint8_t x_631; 
x_626 = lean_ctor_get(x_612, 0);
x_627 = lean_ctor_get(x_612, 1);
lean_inc(x_627);
lean_inc(x_626);
lean_dec(x_612);
lean_inc(x_606);
lean_inc(x_605);
lean_inc(x_604);
x_628 = l_Lean_Expr_forallE___override(x_604, x_605, x_606, x_607);
x_629 = lean_ptr_addr(x_605);
lean_dec(x_605);
x_630 = lean_ptr_addr(x_609);
x_631 = lean_usize_dec_eq(x_629, x_630);
if (x_631 == 0)
{
lean_object* x_632; lean_object* x_633; 
lean_dec(x_628);
lean_dec(x_606);
x_632 = l_Lean_Expr_forallE___override(x_604, x_609, x_626, x_607);
x_633 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_633, 0, x_632);
lean_ctor_set(x_633, 1, x_627);
return x_633;
}
else
{
size_t x_634; size_t x_635; uint8_t x_636; 
x_634 = lean_ptr_addr(x_606);
lean_dec(x_606);
x_635 = lean_ptr_addr(x_626);
x_636 = lean_usize_dec_eq(x_634, x_635);
if (x_636 == 0)
{
lean_object* x_637; lean_object* x_638; 
lean_dec(x_628);
x_637 = l_Lean_Expr_forallE___override(x_604, x_609, x_626, x_607);
x_638 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_638, 0, x_637);
lean_ctor_set(x_638, 1, x_627);
return x_638;
}
else
{
uint8_t x_639; 
x_639 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_607, x_607);
if (x_639 == 0)
{
lean_object* x_640; lean_object* x_641; 
lean_dec(x_628);
x_640 = l_Lean_Expr_forallE___override(x_604, x_609, x_626, x_607);
x_641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_641, 0, x_640);
lean_ctor_set(x_641, 1, x_627);
return x_641;
}
else
{
lean_object* x_642; 
lean_dec(x_626);
lean_dec(x_609);
lean_dec(x_604);
x_642 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_642, 0, x_628);
lean_ctor_set(x_642, 1, x_627);
return x_642;
}
}
}
}
}
else
{
uint8_t x_643; 
lean_dec(x_609);
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_604);
x_643 = !lean_is_exclusive(x_612);
if (x_643 == 0)
{
return x_612;
}
else
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_644 = lean_ctor_get(x_612, 0);
x_645 = lean_ctor_get(x_612, 1);
lean_inc(x_645);
lean_inc(x_644);
lean_dec(x_612);
x_646 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_646, 0, x_644);
lean_ctor_set(x_646, 1, x_645);
return x_646;
}
}
}
else
{
uint8_t x_647; 
lean_dec(x_606);
lean_dec(x_605);
lean_dec(x_604);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_647 = !lean_is_exclusive(x_608);
if (x_647 == 0)
{
return x_608;
}
else
{
lean_object* x_648; lean_object* x_649; lean_object* x_650; 
x_648 = lean_ctor_get(x_608, 0);
x_649 = lean_ctor_get(x_608, 1);
lean_inc(x_649);
lean_inc(x_648);
lean_dec(x_608);
x_650 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_650, 0, x_648);
lean_ctor_set(x_650, 1, x_649);
return x_650;
}
}
}
case 8:
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; uint8_t x_655; lean_object* x_656; 
lean_free_object(x_515);
x_651 = lean_ctor_get(x_5, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_5, 1);
lean_inc(x_652);
x_653 = lean_ctor_get(x_5, 2);
lean_inc(x_653);
x_654 = lean_ctor_get(x_5, 3);
lean_inc(x_654);
x_655 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_652);
lean_inc(x_1);
x_656 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_652, x_6, x_7, x_8, x_9, x_10, x_11, x_517);
if (lean_obj_tag(x_656) == 0)
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; 
x_657 = lean_ctor_get(x_656, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_656, 1);
lean_inc(x_658);
lean_dec(x_656);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_653);
lean_inc(x_1);
x_659 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_653, x_6, x_7, x_8, x_9, x_10, x_11, x_658);
if (lean_obj_tag(x_659) == 0)
{
lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
x_660 = lean_ctor_get(x_659, 0);
lean_inc(x_660);
x_661 = lean_ctor_get(x_659, 1);
lean_inc(x_661);
lean_dec(x_659);
x_662 = lean_nat_add(x_6, x_511);
lean_dec(x_6);
lean_inc(x_654);
x_663 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_654, x_662, x_7, x_8, x_9, x_10, x_11, x_661);
if (lean_obj_tag(x_663) == 0)
{
uint8_t x_664; 
x_664 = !lean_is_exclusive(x_663);
if (x_664 == 0)
{
lean_object* x_665; size_t x_666; size_t x_667; uint8_t x_668; 
x_665 = lean_ctor_get(x_663, 0);
x_666 = lean_ptr_addr(x_652);
lean_dec(x_652);
x_667 = lean_ptr_addr(x_657);
x_668 = lean_usize_dec_eq(x_666, x_667);
if (x_668 == 0)
{
lean_object* x_669; 
lean_dec(x_654);
lean_dec(x_653);
lean_dec(x_5);
x_669 = l_Lean_Expr_letE___override(x_651, x_657, x_660, x_665, x_655);
lean_ctor_set(x_663, 0, x_669);
return x_663;
}
else
{
size_t x_670; size_t x_671; uint8_t x_672; 
x_670 = lean_ptr_addr(x_653);
lean_dec(x_653);
x_671 = lean_ptr_addr(x_660);
x_672 = lean_usize_dec_eq(x_670, x_671);
if (x_672 == 0)
{
lean_object* x_673; 
lean_dec(x_654);
lean_dec(x_5);
x_673 = l_Lean_Expr_letE___override(x_651, x_657, x_660, x_665, x_655);
lean_ctor_set(x_663, 0, x_673);
return x_663;
}
else
{
size_t x_674; size_t x_675; uint8_t x_676; 
x_674 = lean_ptr_addr(x_654);
lean_dec(x_654);
x_675 = lean_ptr_addr(x_665);
x_676 = lean_usize_dec_eq(x_674, x_675);
if (x_676 == 0)
{
lean_object* x_677; 
lean_dec(x_5);
x_677 = l_Lean_Expr_letE___override(x_651, x_657, x_660, x_665, x_655);
lean_ctor_set(x_663, 0, x_677);
return x_663;
}
else
{
lean_dec(x_665);
lean_dec(x_660);
lean_dec(x_657);
lean_dec(x_651);
lean_ctor_set(x_663, 0, x_5);
return x_663;
}
}
}
}
else
{
lean_object* x_678; lean_object* x_679; size_t x_680; size_t x_681; uint8_t x_682; 
x_678 = lean_ctor_get(x_663, 0);
x_679 = lean_ctor_get(x_663, 1);
lean_inc(x_679);
lean_inc(x_678);
lean_dec(x_663);
x_680 = lean_ptr_addr(x_652);
lean_dec(x_652);
x_681 = lean_ptr_addr(x_657);
x_682 = lean_usize_dec_eq(x_680, x_681);
if (x_682 == 0)
{
lean_object* x_683; lean_object* x_684; 
lean_dec(x_654);
lean_dec(x_653);
lean_dec(x_5);
x_683 = l_Lean_Expr_letE___override(x_651, x_657, x_660, x_678, x_655);
x_684 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_684, 0, x_683);
lean_ctor_set(x_684, 1, x_679);
return x_684;
}
else
{
size_t x_685; size_t x_686; uint8_t x_687; 
x_685 = lean_ptr_addr(x_653);
lean_dec(x_653);
x_686 = lean_ptr_addr(x_660);
x_687 = lean_usize_dec_eq(x_685, x_686);
if (x_687 == 0)
{
lean_object* x_688; lean_object* x_689; 
lean_dec(x_654);
lean_dec(x_5);
x_688 = l_Lean_Expr_letE___override(x_651, x_657, x_660, x_678, x_655);
x_689 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_689, 0, x_688);
lean_ctor_set(x_689, 1, x_679);
return x_689;
}
else
{
size_t x_690; size_t x_691; uint8_t x_692; 
x_690 = lean_ptr_addr(x_654);
lean_dec(x_654);
x_691 = lean_ptr_addr(x_678);
x_692 = lean_usize_dec_eq(x_690, x_691);
if (x_692 == 0)
{
lean_object* x_693; lean_object* x_694; 
lean_dec(x_5);
x_693 = l_Lean_Expr_letE___override(x_651, x_657, x_660, x_678, x_655);
x_694 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_694, 0, x_693);
lean_ctor_set(x_694, 1, x_679);
return x_694;
}
else
{
lean_object* x_695; 
lean_dec(x_678);
lean_dec(x_660);
lean_dec(x_657);
lean_dec(x_651);
x_695 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_695, 0, x_5);
lean_ctor_set(x_695, 1, x_679);
return x_695;
}
}
}
}
}
else
{
uint8_t x_696; 
lean_dec(x_660);
lean_dec(x_657);
lean_dec(x_654);
lean_dec(x_653);
lean_dec(x_652);
lean_dec(x_651);
lean_dec(x_5);
x_696 = !lean_is_exclusive(x_663);
if (x_696 == 0)
{
return x_663;
}
else
{
lean_object* x_697; lean_object* x_698; lean_object* x_699; 
x_697 = lean_ctor_get(x_663, 0);
x_698 = lean_ctor_get(x_663, 1);
lean_inc(x_698);
lean_inc(x_697);
lean_dec(x_663);
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
lean_dec(x_657);
lean_dec(x_654);
lean_dec(x_653);
lean_dec(x_652);
lean_dec(x_651);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_700 = !lean_is_exclusive(x_659);
if (x_700 == 0)
{
return x_659;
}
else
{
lean_object* x_701; lean_object* x_702; lean_object* x_703; 
x_701 = lean_ctor_get(x_659, 0);
x_702 = lean_ctor_get(x_659, 1);
lean_inc(x_702);
lean_inc(x_701);
lean_dec(x_659);
x_703 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_703, 0, x_701);
lean_ctor_set(x_703, 1, x_702);
return x_703;
}
}
}
else
{
uint8_t x_704; 
lean_dec(x_654);
lean_dec(x_653);
lean_dec(x_652);
lean_dec(x_651);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_704 = !lean_is_exclusive(x_656);
if (x_704 == 0)
{
return x_656;
}
else
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; 
x_705 = lean_ctor_get(x_656, 0);
x_706 = lean_ctor_get(x_656, 1);
lean_inc(x_706);
lean_inc(x_705);
lean_dec(x_656);
x_707 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_707, 0, x_705);
lean_ctor_set(x_707, 1, x_706);
return x_707;
}
}
}
case 10:
{
lean_object* x_708; lean_object* x_709; lean_object* x_710; 
lean_free_object(x_515);
x_708 = lean_ctor_get(x_5, 0);
lean_inc(x_708);
x_709 = lean_ctor_get(x_5, 1);
lean_inc(x_709);
lean_inc(x_709);
x_710 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_709, x_6, x_7, x_8, x_9, x_10, x_11, x_517);
if (lean_obj_tag(x_710) == 0)
{
uint8_t x_711; 
x_711 = !lean_is_exclusive(x_710);
if (x_711 == 0)
{
lean_object* x_712; size_t x_713; size_t x_714; uint8_t x_715; 
x_712 = lean_ctor_get(x_710, 0);
x_713 = lean_ptr_addr(x_709);
lean_dec(x_709);
x_714 = lean_ptr_addr(x_712);
x_715 = lean_usize_dec_eq(x_713, x_714);
if (x_715 == 0)
{
lean_object* x_716; 
lean_dec(x_5);
x_716 = l_Lean_Expr_mdata___override(x_708, x_712);
lean_ctor_set(x_710, 0, x_716);
return x_710;
}
else
{
lean_dec(x_712);
lean_dec(x_708);
lean_ctor_set(x_710, 0, x_5);
return x_710;
}
}
else
{
lean_object* x_717; lean_object* x_718; size_t x_719; size_t x_720; uint8_t x_721; 
x_717 = lean_ctor_get(x_710, 0);
x_718 = lean_ctor_get(x_710, 1);
lean_inc(x_718);
lean_inc(x_717);
lean_dec(x_710);
x_719 = lean_ptr_addr(x_709);
lean_dec(x_709);
x_720 = lean_ptr_addr(x_717);
x_721 = lean_usize_dec_eq(x_719, x_720);
if (x_721 == 0)
{
lean_object* x_722; lean_object* x_723; 
lean_dec(x_5);
x_722 = l_Lean_Expr_mdata___override(x_708, x_717);
x_723 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_723, 0, x_722);
lean_ctor_set(x_723, 1, x_718);
return x_723;
}
else
{
lean_object* x_724; 
lean_dec(x_717);
lean_dec(x_708);
x_724 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_724, 0, x_5);
lean_ctor_set(x_724, 1, x_718);
return x_724;
}
}
}
else
{
uint8_t x_725; 
lean_dec(x_709);
lean_dec(x_708);
lean_dec(x_5);
x_725 = !lean_is_exclusive(x_710);
if (x_725 == 0)
{
return x_710;
}
else
{
lean_object* x_726; lean_object* x_727; lean_object* x_728; 
x_726 = lean_ctor_get(x_710, 0);
x_727 = lean_ctor_get(x_710, 1);
lean_inc(x_727);
lean_inc(x_726);
lean_dec(x_710);
x_728 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_728, 0, x_726);
lean_ctor_set(x_728, 1, x_727);
return x_728;
}
}
}
case 11:
{
lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; 
lean_free_object(x_515);
x_729 = lean_ctor_get(x_5, 0);
lean_inc(x_729);
x_730 = lean_ctor_get(x_5, 1);
lean_inc(x_730);
x_731 = lean_ctor_get(x_5, 2);
lean_inc(x_731);
lean_inc(x_731);
x_732 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_731, x_6, x_7, x_8, x_9, x_10, x_11, x_517);
if (lean_obj_tag(x_732) == 0)
{
uint8_t x_733; 
x_733 = !lean_is_exclusive(x_732);
if (x_733 == 0)
{
lean_object* x_734; size_t x_735; size_t x_736; uint8_t x_737; 
x_734 = lean_ctor_get(x_732, 0);
x_735 = lean_ptr_addr(x_731);
lean_dec(x_731);
x_736 = lean_ptr_addr(x_734);
x_737 = lean_usize_dec_eq(x_735, x_736);
if (x_737 == 0)
{
lean_object* x_738; 
lean_dec(x_5);
x_738 = l_Lean_Expr_proj___override(x_729, x_730, x_734);
lean_ctor_set(x_732, 0, x_738);
return x_732;
}
else
{
lean_dec(x_734);
lean_dec(x_730);
lean_dec(x_729);
lean_ctor_set(x_732, 0, x_5);
return x_732;
}
}
else
{
lean_object* x_739; lean_object* x_740; size_t x_741; size_t x_742; uint8_t x_743; 
x_739 = lean_ctor_get(x_732, 0);
x_740 = lean_ctor_get(x_732, 1);
lean_inc(x_740);
lean_inc(x_739);
lean_dec(x_732);
x_741 = lean_ptr_addr(x_731);
lean_dec(x_731);
x_742 = lean_ptr_addr(x_739);
x_743 = lean_usize_dec_eq(x_741, x_742);
if (x_743 == 0)
{
lean_object* x_744; lean_object* x_745; 
lean_dec(x_5);
x_744 = l_Lean_Expr_proj___override(x_729, x_730, x_739);
x_745 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_745, 0, x_744);
lean_ctor_set(x_745, 1, x_740);
return x_745;
}
else
{
lean_object* x_746; 
lean_dec(x_739);
lean_dec(x_730);
lean_dec(x_729);
x_746 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_746, 0, x_5);
lean_ctor_set(x_746, 1, x_740);
return x_746;
}
}
}
else
{
uint8_t x_747; 
lean_dec(x_731);
lean_dec(x_730);
lean_dec(x_729);
lean_dec(x_5);
x_747 = !lean_is_exclusive(x_732);
if (x_747 == 0)
{
return x_732;
}
else
{
lean_object* x_748; lean_object* x_749; lean_object* x_750; 
x_748 = lean_ctor_get(x_732, 0);
x_749 = lean_ctor_get(x_732, 1);
lean_inc(x_749);
lean_inc(x_748);
lean_dec(x_732);
x_750 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_750, 0, x_748);
lean_ctor_set(x_750, 1, x_749);
return x_750;
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
lean_ctor_set(x_515, 0, x_5);
return x_515;
}
}
}
else
{
lean_object* x_751; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_751 = l_Lean_Expr_bvar___override(x_6);
lean_ctor_set(x_515, 0, x_751);
return x_515;
}
}
else
{
lean_object* x_752; uint8_t x_753; 
x_752 = lean_ctor_get(x_515, 1);
lean_inc(x_752);
lean_dec(x_515);
x_753 = l_Lean_Occurrences_contains(x_2, x_509);
lean_dec(x_509);
if (x_753 == 0)
{
switch (lean_obj_tag(x_5)) {
case 5:
{
lean_object* x_754; lean_object* x_755; lean_object* x_756; 
x_754 = lean_ctor_get(x_5, 0);
lean_inc(x_754);
x_755 = lean_ctor_get(x_5, 1);
lean_inc(x_755);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_754);
lean_inc(x_1);
x_756 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_754, x_6, x_7, x_8, x_9, x_10, x_11, x_752);
if (lean_obj_tag(x_756) == 0)
{
lean_object* x_757; lean_object* x_758; lean_object* x_759; 
x_757 = lean_ctor_get(x_756, 0);
lean_inc(x_757);
x_758 = lean_ctor_get(x_756, 1);
lean_inc(x_758);
lean_dec(x_756);
lean_inc(x_755);
x_759 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_755, x_6, x_7, x_8, x_9, x_10, x_11, x_758);
if (lean_obj_tag(x_759) == 0)
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; size_t x_763; size_t x_764; uint8_t x_765; 
x_760 = lean_ctor_get(x_759, 0);
lean_inc(x_760);
x_761 = lean_ctor_get(x_759, 1);
lean_inc(x_761);
if (lean_is_exclusive(x_759)) {
 lean_ctor_release(x_759, 0);
 lean_ctor_release(x_759, 1);
 x_762 = x_759;
} else {
 lean_dec_ref(x_759);
 x_762 = lean_box(0);
}
x_763 = lean_ptr_addr(x_754);
lean_dec(x_754);
x_764 = lean_ptr_addr(x_757);
x_765 = lean_usize_dec_eq(x_763, x_764);
if (x_765 == 0)
{
lean_object* x_766; lean_object* x_767; 
lean_dec(x_755);
lean_dec(x_5);
x_766 = l_Lean_Expr_app___override(x_757, x_760);
if (lean_is_scalar(x_762)) {
 x_767 = lean_alloc_ctor(0, 2, 0);
} else {
 x_767 = x_762;
}
lean_ctor_set(x_767, 0, x_766);
lean_ctor_set(x_767, 1, x_761);
return x_767;
}
else
{
size_t x_768; size_t x_769; uint8_t x_770; 
x_768 = lean_ptr_addr(x_755);
lean_dec(x_755);
x_769 = lean_ptr_addr(x_760);
x_770 = lean_usize_dec_eq(x_768, x_769);
if (x_770 == 0)
{
lean_object* x_771; lean_object* x_772; 
lean_dec(x_5);
x_771 = l_Lean_Expr_app___override(x_757, x_760);
if (lean_is_scalar(x_762)) {
 x_772 = lean_alloc_ctor(0, 2, 0);
} else {
 x_772 = x_762;
}
lean_ctor_set(x_772, 0, x_771);
lean_ctor_set(x_772, 1, x_761);
return x_772;
}
else
{
lean_object* x_773; 
lean_dec(x_760);
lean_dec(x_757);
if (lean_is_scalar(x_762)) {
 x_773 = lean_alloc_ctor(0, 2, 0);
} else {
 x_773 = x_762;
}
lean_ctor_set(x_773, 0, x_5);
lean_ctor_set(x_773, 1, x_761);
return x_773;
}
}
}
else
{
lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; 
lean_dec(x_757);
lean_dec(x_755);
lean_dec(x_754);
lean_dec(x_5);
x_774 = lean_ctor_get(x_759, 0);
lean_inc(x_774);
x_775 = lean_ctor_get(x_759, 1);
lean_inc(x_775);
if (lean_is_exclusive(x_759)) {
 lean_ctor_release(x_759, 0);
 lean_ctor_release(x_759, 1);
 x_776 = x_759;
} else {
 lean_dec_ref(x_759);
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
else
{
lean_object* x_778; lean_object* x_779; lean_object* x_780; lean_object* x_781; 
lean_dec(x_755);
lean_dec(x_754);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_778 = lean_ctor_get(x_756, 0);
lean_inc(x_778);
x_779 = lean_ctor_get(x_756, 1);
lean_inc(x_779);
if (lean_is_exclusive(x_756)) {
 lean_ctor_release(x_756, 0);
 lean_ctor_release(x_756, 1);
 x_780 = x_756;
} else {
 lean_dec_ref(x_756);
 x_780 = lean_box(0);
}
if (lean_is_scalar(x_780)) {
 x_781 = lean_alloc_ctor(1, 2, 0);
} else {
 x_781 = x_780;
}
lean_ctor_set(x_781, 0, x_778);
lean_ctor_set(x_781, 1, x_779);
return x_781;
}
}
case 6:
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; uint8_t x_785; lean_object* x_786; 
x_782 = lean_ctor_get(x_5, 0);
lean_inc(x_782);
x_783 = lean_ctor_get(x_5, 1);
lean_inc(x_783);
x_784 = lean_ctor_get(x_5, 2);
lean_inc(x_784);
x_785 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_783);
lean_inc(x_1);
x_786 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_783, x_6, x_7, x_8, x_9, x_10, x_11, x_752);
if (lean_obj_tag(x_786) == 0)
{
lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; 
x_787 = lean_ctor_get(x_786, 0);
lean_inc(x_787);
x_788 = lean_ctor_get(x_786, 1);
lean_inc(x_788);
lean_dec(x_786);
x_789 = lean_nat_add(x_6, x_511);
lean_dec(x_6);
lean_inc(x_784);
x_790 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_784, x_789, x_7, x_8, x_9, x_10, x_11, x_788);
if (lean_obj_tag(x_790) == 0)
{
lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; size_t x_795; size_t x_796; uint8_t x_797; 
x_791 = lean_ctor_get(x_790, 0);
lean_inc(x_791);
x_792 = lean_ctor_get(x_790, 1);
lean_inc(x_792);
if (lean_is_exclusive(x_790)) {
 lean_ctor_release(x_790, 0);
 lean_ctor_release(x_790, 1);
 x_793 = x_790;
} else {
 lean_dec_ref(x_790);
 x_793 = lean_box(0);
}
lean_inc(x_784);
lean_inc(x_783);
lean_inc(x_782);
x_794 = l_Lean_Expr_lam___override(x_782, x_783, x_784, x_785);
x_795 = lean_ptr_addr(x_783);
lean_dec(x_783);
x_796 = lean_ptr_addr(x_787);
x_797 = lean_usize_dec_eq(x_795, x_796);
if (x_797 == 0)
{
lean_object* x_798; lean_object* x_799; 
lean_dec(x_794);
lean_dec(x_784);
x_798 = l_Lean_Expr_lam___override(x_782, x_787, x_791, x_785);
if (lean_is_scalar(x_793)) {
 x_799 = lean_alloc_ctor(0, 2, 0);
} else {
 x_799 = x_793;
}
lean_ctor_set(x_799, 0, x_798);
lean_ctor_set(x_799, 1, x_792);
return x_799;
}
else
{
size_t x_800; size_t x_801; uint8_t x_802; 
x_800 = lean_ptr_addr(x_784);
lean_dec(x_784);
x_801 = lean_ptr_addr(x_791);
x_802 = lean_usize_dec_eq(x_800, x_801);
if (x_802 == 0)
{
lean_object* x_803; lean_object* x_804; 
lean_dec(x_794);
x_803 = l_Lean_Expr_lam___override(x_782, x_787, x_791, x_785);
if (lean_is_scalar(x_793)) {
 x_804 = lean_alloc_ctor(0, 2, 0);
} else {
 x_804 = x_793;
}
lean_ctor_set(x_804, 0, x_803);
lean_ctor_set(x_804, 1, x_792);
return x_804;
}
else
{
uint8_t x_805; 
x_805 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_785, x_785);
if (x_805 == 0)
{
lean_object* x_806; lean_object* x_807; 
lean_dec(x_794);
x_806 = l_Lean_Expr_lam___override(x_782, x_787, x_791, x_785);
if (lean_is_scalar(x_793)) {
 x_807 = lean_alloc_ctor(0, 2, 0);
} else {
 x_807 = x_793;
}
lean_ctor_set(x_807, 0, x_806);
lean_ctor_set(x_807, 1, x_792);
return x_807;
}
else
{
lean_object* x_808; 
lean_dec(x_791);
lean_dec(x_787);
lean_dec(x_782);
if (lean_is_scalar(x_793)) {
 x_808 = lean_alloc_ctor(0, 2, 0);
} else {
 x_808 = x_793;
}
lean_ctor_set(x_808, 0, x_794);
lean_ctor_set(x_808, 1, x_792);
return x_808;
}
}
}
}
else
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; lean_object* x_812; 
lean_dec(x_787);
lean_dec(x_784);
lean_dec(x_783);
lean_dec(x_782);
x_809 = lean_ctor_get(x_790, 0);
lean_inc(x_809);
x_810 = lean_ctor_get(x_790, 1);
lean_inc(x_810);
if (lean_is_exclusive(x_790)) {
 lean_ctor_release(x_790, 0);
 lean_ctor_release(x_790, 1);
 x_811 = x_790;
} else {
 lean_dec_ref(x_790);
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
else
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
lean_dec(x_784);
lean_dec(x_783);
lean_dec(x_782);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_813 = lean_ctor_get(x_786, 0);
lean_inc(x_813);
x_814 = lean_ctor_get(x_786, 1);
lean_inc(x_814);
if (lean_is_exclusive(x_786)) {
 lean_ctor_release(x_786, 0);
 lean_ctor_release(x_786, 1);
 x_815 = x_786;
} else {
 lean_dec_ref(x_786);
 x_815 = lean_box(0);
}
if (lean_is_scalar(x_815)) {
 x_816 = lean_alloc_ctor(1, 2, 0);
} else {
 x_816 = x_815;
}
lean_ctor_set(x_816, 0, x_813);
lean_ctor_set(x_816, 1, x_814);
return x_816;
}
}
case 7:
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; uint8_t x_820; lean_object* x_821; 
x_817 = lean_ctor_get(x_5, 0);
lean_inc(x_817);
x_818 = lean_ctor_get(x_5, 1);
lean_inc(x_818);
x_819 = lean_ctor_get(x_5, 2);
lean_inc(x_819);
x_820 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_818);
lean_inc(x_1);
x_821 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_818, x_6, x_7, x_8, x_9, x_10, x_11, x_752);
if (lean_obj_tag(x_821) == 0)
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
x_822 = lean_ctor_get(x_821, 0);
lean_inc(x_822);
x_823 = lean_ctor_get(x_821, 1);
lean_inc(x_823);
lean_dec(x_821);
x_824 = lean_nat_add(x_6, x_511);
lean_dec(x_6);
lean_inc(x_819);
x_825 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_819, x_824, x_7, x_8, x_9, x_10, x_11, x_823);
if (lean_obj_tag(x_825) == 0)
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; size_t x_830; size_t x_831; uint8_t x_832; 
x_826 = lean_ctor_get(x_825, 0);
lean_inc(x_826);
x_827 = lean_ctor_get(x_825, 1);
lean_inc(x_827);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 lean_ctor_release(x_825, 1);
 x_828 = x_825;
} else {
 lean_dec_ref(x_825);
 x_828 = lean_box(0);
}
lean_inc(x_819);
lean_inc(x_818);
lean_inc(x_817);
x_829 = l_Lean_Expr_forallE___override(x_817, x_818, x_819, x_820);
x_830 = lean_ptr_addr(x_818);
lean_dec(x_818);
x_831 = lean_ptr_addr(x_822);
x_832 = lean_usize_dec_eq(x_830, x_831);
if (x_832 == 0)
{
lean_object* x_833; lean_object* x_834; 
lean_dec(x_829);
lean_dec(x_819);
x_833 = l_Lean_Expr_forallE___override(x_817, x_822, x_826, x_820);
if (lean_is_scalar(x_828)) {
 x_834 = lean_alloc_ctor(0, 2, 0);
} else {
 x_834 = x_828;
}
lean_ctor_set(x_834, 0, x_833);
lean_ctor_set(x_834, 1, x_827);
return x_834;
}
else
{
size_t x_835; size_t x_836; uint8_t x_837; 
x_835 = lean_ptr_addr(x_819);
lean_dec(x_819);
x_836 = lean_ptr_addr(x_826);
x_837 = lean_usize_dec_eq(x_835, x_836);
if (x_837 == 0)
{
lean_object* x_838; lean_object* x_839; 
lean_dec(x_829);
x_838 = l_Lean_Expr_forallE___override(x_817, x_822, x_826, x_820);
if (lean_is_scalar(x_828)) {
 x_839 = lean_alloc_ctor(0, 2, 0);
} else {
 x_839 = x_828;
}
lean_ctor_set(x_839, 0, x_838);
lean_ctor_set(x_839, 1, x_827);
return x_839;
}
else
{
uint8_t x_840; 
x_840 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_820, x_820);
if (x_840 == 0)
{
lean_object* x_841; lean_object* x_842; 
lean_dec(x_829);
x_841 = l_Lean_Expr_forallE___override(x_817, x_822, x_826, x_820);
if (lean_is_scalar(x_828)) {
 x_842 = lean_alloc_ctor(0, 2, 0);
} else {
 x_842 = x_828;
}
lean_ctor_set(x_842, 0, x_841);
lean_ctor_set(x_842, 1, x_827);
return x_842;
}
else
{
lean_object* x_843; 
lean_dec(x_826);
lean_dec(x_822);
lean_dec(x_817);
if (lean_is_scalar(x_828)) {
 x_843 = lean_alloc_ctor(0, 2, 0);
} else {
 x_843 = x_828;
}
lean_ctor_set(x_843, 0, x_829);
lean_ctor_set(x_843, 1, x_827);
return x_843;
}
}
}
}
else
{
lean_object* x_844; lean_object* x_845; lean_object* x_846; lean_object* x_847; 
lean_dec(x_822);
lean_dec(x_819);
lean_dec(x_818);
lean_dec(x_817);
x_844 = lean_ctor_get(x_825, 0);
lean_inc(x_844);
x_845 = lean_ctor_get(x_825, 1);
lean_inc(x_845);
if (lean_is_exclusive(x_825)) {
 lean_ctor_release(x_825, 0);
 lean_ctor_release(x_825, 1);
 x_846 = x_825;
} else {
 lean_dec_ref(x_825);
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
else
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; 
lean_dec(x_819);
lean_dec(x_818);
lean_dec(x_817);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_848 = lean_ctor_get(x_821, 0);
lean_inc(x_848);
x_849 = lean_ctor_get(x_821, 1);
lean_inc(x_849);
if (lean_is_exclusive(x_821)) {
 lean_ctor_release(x_821, 0);
 lean_ctor_release(x_821, 1);
 x_850 = x_821;
} else {
 lean_dec_ref(x_821);
 x_850 = lean_box(0);
}
if (lean_is_scalar(x_850)) {
 x_851 = lean_alloc_ctor(1, 2, 0);
} else {
 x_851 = x_850;
}
lean_ctor_set(x_851, 0, x_848);
lean_ctor_set(x_851, 1, x_849);
return x_851;
}
}
case 8:
{
lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; uint8_t x_856; lean_object* x_857; 
x_852 = lean_ctor_get(x_5, 0);
lean_inc(x_852);
x_853 = lean_ctor_get(x_5, 1);
lean_inc(x_853);
x_854 = lean_ctor_get(x_5, 2);
lean_inc(x_854);
x_855 = lean_ctor_get(x_5, 3);
lean_inc(x_855);
x_856 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_853);
lean_inc(x_1);
x_857 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_853, x_6, x_7, x_8, x_9, x_10, x_11, x_752);
if (lean_obj_tag(x_857) == 0)
{
lean_object* x_858; lean_object* x_859; lean_object* x_860; 
x_858 = lean_ctor_get(x_857, 0);
lean_inc(x_858);
x_859 = lean_ctor_get(x_857, 1);
lean_inc(x_859);
lean_dec(x_857);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_854);
lean_inc(x_1);
x_860 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_854, x_6, x_7, x_8, x_9, x_10, x_11, x_859);
if (lean_obj_tag(x_860) == 0)
{
lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; 
x_861 = lean_ctor_get(x_860, 0);
lean_inc(x_861);
x_862 = lean_ctor_get(x_860, 1);
lean_inc(x_862);
lean_dec(x_860);
x_863 = lean_nat_add(x_6, x_511);
lean_dec(x_6);
lean_inc(x_855);
x_864 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_855, x_863, x_7, x_8, x_9, x_10, x_11, x_862);
if (lean_obj_tag(x_864) == 0)
{
lean_object* x_865; lean_object* x_866; lean_object* x_867; size_t x_868; size_t x_869; uint8_t x_870; 
x_865 = lean_ctor_get(x_864, 0);
lean_inc(x_865);
x_866 = lean_ctor_get(x_864, 1);
lean_inc(x_866);
if (lean_is_exclusive(x_864)) {
 lean_ctor_release(x_864, 0);
 lean_ctor_release(x_864, 1);
 x_867 = x_864;
} else {
 lean_dec_ref(x_864);
 x_867 = lean_box(0);
}
x_868 = lean_ptr_addr(x_853);
lean_dec(x_853);
x_869 = lean_ptr_addr(x_858);
x_870 = lean_usize_dec_eq(x_868, x_869);
if (x_870 == 0)
{
lean_object* x_871; lean_object* x_872; 
lean_dec(x_855);
lean_dec(x_854);
lean_dec(x_5);
x_871 = l_Lean_Expr_letE___override(x_852, x_858, x_861, x_865, x_856);
if (lean_is_scalar(x_867)) {
 x_872 = lean_alloc_ctor(0, 2, 0);
} else {
 x_872 = x_867;
}
lean_ctor_set(x_872, 0, x_871);
lean_ctor_set(x_872, 1, x_866);
return x_872;
}
else
{
size_t x_873; size_t x_874; uint8_t x_875; 
x_873 = lean_ptr_addr(x_854);
lean_dec(x_854);
x_874 = lean_ptr_addr(x_861);
x_875 = lean_usize_dec_eq(x_873, x_874);
if (x_875 == 0)
{
lean_object* x_876; lean_object* x_877; 
lean_dec(x_855);
lean_dec(x_5);
x_876 = l_Lean_Expr_letE___override(x_852, x_858, x_861, x_865, x_856);
if (lean_is_scalar(x_867)) {
 x_877 = lean_alloc_ctor(0, 2, 0);
} else {
 x_877 = x_867;
}
lean_ctor_set(x_877, 0, x_876);
lean_ctor_set(x_877, 1, x_866);
return x_877;
}
else
{
size_t x_878; size_t x_879; uint8_t x_880; 
x_878 = lean_ptr_addr(x_855);
lean_dec(x_855);
x_879 = lean_ptr_addr(x_865);
x_880 = lean_usize_dec_eq(x_878, x_879);
if (x_880 == 0)
{
lean_object* x_881; lean_object* x_882; 
lean_dec(x_5);
x_881 = l_Lean_Expr_letE___override(x_852, x_858, x_861, x_865, x_856);
if (lean_is_scalar(x_867)) {
 x_882 = lean_alloc_ctor(0, 2, 0);
} else {
 x_882 = x_867;
}
lean_ctor_set(x_882, 0, x_881);
lean_ctor_set(x_882, 1, x_866);
return x_882;
}
else
{
lean_object* x_883; 
lean_dec(x_865);
lean_dec(x_861);
lean_dec(x_858);
lean_dec(x_852);
if (lean_is_scalar(x_867)) {
 x_883 = lean_alloc_ctor(0, 2, 0);
} else {
 x_883 = x_867;
}
lean_ctor_set(x_883, 0, x_5);
lean_ctor_set(x_883, 1, x_866);
return x_883;
}
}
}
}
else
{
lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; 
lean_dec(x_861);
lean_dec(x_858);
lean_dec(x_855);
lean_dec(x_854);
lean_dec(x_853);
lean_dec(x_852);
lean_dec(x_5);
x_884 = lean_ctor_get(x_864, 0);
lean_inc(x_884);
x_885 = lean_ctor_get(x_864, 1);
lean_inc(x_885);
if (lean_is_exclusive(x_864)) {
 lean_ctor_release(x_864, 0);
 lean_ctor_release(x_864, 1);
 x_886 = x_864;
} else {
 lean_dec_ref(x_864);
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
lean_dec(x_858);
lean_dec(x_855);
lean_dec(x_854);
lean_dec(x_853);
lean_dec(x_852);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_888 = lean_ctor_get(x_860, 0);
lean_inc(x_888);
x_889 = lean_ctor_get(x_860, 1);
lean_inc(x_889);
if (lean_is_exclusive(x_860)) {
 lean_ctor_release(x_860, 0);
 lean_ctor_release(x_860, 1);
 x_890 = x_860;
} else {
 lean_dec_ref(x_860);
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
else
{
lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; 
lean_dec(x_855);
lean_dec(x_854);
lean_dec(x_853);
lean_dec(x_852);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_892 = lean_ctor_get(x_857, 0);
lean_inc(x_892);
x_893 = lean_ctor_get(x_857, 1);
lean_inc(x_893);
if (lean_is_exclusive(x_857)) {
 lean_ctor_release(x_857, 0);
 lean_ctor_release(x_857, 1);
 x_894 = x_857;
} else {
 lean_dec_ref(x_857);
 x_894 = lean_box(0);
}
if (lean_is_scalar(x_894)) {
 x_895 = lean_alloc_ctor(1, 2, 0);
} else {
 x_895 = x_894;
}
lean_ctor_set(x_895, 0, x_892);
lean_ctor_set(x_895, 1, x_893);
return x_895;
}
}
case 10:
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; 
x_896 = lean_ctor_get(x_5, 0);
lean_inc(x_896);
x_897 = lean_ctor_get(x_5, 1);
lean_inc(x_897);
lean_inc(x_897);
x_898 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_897, x_6, x_7, x_8, x_9, x_10, x_11, x_752);
if (lean_obj_tag(x_898) == 0)
{
lean_object* x_899; lean_object* x_900; lean_object* x_901; size_t x_902; size_t x_903; uint8_t x_904; 
x_899 = lean_ctor_get(x_898, 0);
lean_inc(x_899);
x_900 = lean_ctor_get(x_898, 1);
lean_inc(x_900);
if (lean_is_exclusive(x_898)) {
 lean_ctor_release(x_898, 0);
 lean_ctor_release(x_898, 1);
 x_901 = x_898;
} else {
 lean_dec_ref(x_898);
 x_901 = lean_box(0);
}
x_902 = lean_ptr_addr(x_897);
lean_dec(x_897);
x_903 = lean_ptr_addr(x_899);
x_904 = lean_usize_dec_eq(x_902, x_903);
if (x_904 == 0)
{
lean_object* x_905; lean_object* x_906; 
lean_dec(x_5);
x_905 = l_Lean_Expr_mdata___override(x_896, x_899);
if (lean_is_scalar(x_901)) {
 x_906 = lean_alloc_ctor(0, 2, 0);
} else {
 x_906 = x_901;
}
lean_ctor_set(x_906, 0, x_905);
lean_ctor_set(x_906, 1, x_900);
return x_906;
}
else
{
lean_object* x_907; 
lean_dec(x_899);
lean_dec(x_896);
if (lean_is_scalar(x_901)) {
 x_907 = lean_alloc_ctor(0, 2, 0);
} else {
 x_907 = x_901;
}
lean_ctor_set(x_907, 0, x_5);
lean_ctor_set(x_907, 1, x_900);
return x_907;
}
}
else
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; 
lean_dec(x_897);
lean_dec(x_896);
lean_dec(x_5);
x_908 = lean_ctor_get(x_898, 0);
lean_inc(x_908);
x_909 = lean_ctor_get(x_898, 1);
lean_inc(x_909);
if (lean_is_exclusive(x_898)) {
 lean_ctor_release(x_898, 0);
 lean_ctor_release(x_898, 1);
 x_910 = x_898;
} else {
 lean_dec_ref(x_898);
 x_910 = lean_box(0);
}
if (lean_is_scalar(x_910)) {
 x_911 = lean_alloc_ctor(1, 2, 0);
} else {
 x_911 = x_910;
}
lean_ctor_set(x_911, 0, x_908);
lean_ctor_set(x_911, 1, x_909);
return x_911;
}
}
case 11:
{
lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; 
x_912 = lean_ctor_get(x_5, 0);
lean_inc(x_912);
x_913 = lean_ctor_get(x_5, 1);
lean_inc(x_913);
x_914 = lean_ctor_get(x_5, 2);
lean_inc(x_914);
lean_inc(x_914);
x_915 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_914, x_6, x_7, x_8, x_9, x_10, x_11, x_752);
if (lean_obj_tag(x_915) == 0)
{
lean_object* x_916; lean_object* x_917; lean_object* x_918; size_t x_919; size_t x_920; uint8_t x_921; 
x_916 = lean_ctor_get(x_915, 0);
lean_inc(x_916);
x_917 = lean_ctor_get(x_915, 1);
lean_inc(x_917);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 lean_ctor_release(x_915, 1);
 x_918 = x_915;
} else {
 lean_dec_ref(x_915);
 x_918 = lean_box(0);
}
x_919 = lean_ptr_addr(x_914);
lean_dec(x_914);
x_920 = lean_ptr_addr(x_916);
x_921 = lean_usize_dec_eq(x_919, x_920);
if (x_921 == 0)
{
lean_object* x_922; lean_object* x_923; 
lean_dec(x_5);
x_922 = l_Lean_Expr_proj___override(x_912, x_913, x_916);
if (lean_is_scalar(x_918)) {
 x_923 = lean_alloc_ctor(0, 2, 0);
} else {
 x_923 = x_918;
}
lean_ctor_set(x_923, 0, x_922);
lean_ctor_set(x_923, 1, x_917);
return x_923;
}
else
{
lean_object* x_924; 
lean_dec(x_916);
lean_dec(x_913);
lean_dec(x_912);
if (lean_is_scalar(x_918)) {
 x_924 = lean_alloc_ctor(0, 2, 0);
} else {
 x_924 = x_918;
}
lean_ctor_set(x_924, 0, x_5);
lean_ctor_set(x_924, 1, x_917);
return x_924;
}
}
else
{
lean_object* x_925; lean_object* x_926; lean_object* x_927; lean_object* x_928; 
lean_dec(x_914);
lean_dec(x_913);
lean_dec(x_912);
lean_dec(x_5);
x_925 = lean_ctor_get(x_915, 0);
lean_inc(x_925);
x_926 = lean_ctor_get(x_915, 1);
lean_inc(x_926);
if (lean_is_exclusive(x_915)) {
 lean_ctor_release(x_915, 0);
 lean_ctor_release(x_915, 1);
 x_927 = x_915;
} else {
 lean_dec_ref(x_915);
 x_927 = lean_box(0);
}
if (lean_is_scalar(x_927)) {
 x_928 = lean_alloc_ctor(1, 2, 0);
} else {
 x_928 = x_927;
}
lean_ctor_set(x_928, 0, x_925);
lean_ctor_set(x_928, 1, x_926);
return x_928;
}
}
default: 
{
lean_object* x_929; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_929 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_929, 0, x_5);
lean_ctor_set(x_929, 1, x_752);
return x_929;
}
}
}
else
{
lean_object* x_930; lean_object* x_931; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_1);
x_930 = l_Lean_Expr_bvar___override(x_6);
x_931 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_931, 0, x_930);
lean_ctor_set(x_931, 1, x_752);
return x_931;
}
}
}
}
else
{
uint8_t x_932; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_932 = !lean_is_exclusive(x_258);
if (x_932 == 0)
{
return x_258;
}
else
{
lean_object* x_933; lean_object* x_934; lean_object* x_935; 
x_933 = lean_ctor_get(x_258, 0);
x_934 = lean_ctor_get(x_258, 1);
lean_inc(x_934);
lean_inc(x_933);
lean_dec(x_258);
x_935 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_935, 0, x_933);
lean_ctor_set(x_935, 1, x_934);
return x_935;
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
lean_object* x_936; lean_object* x_937; lean_object* x_938; 
x_936 = lean_ctor_get(x_5, 0);
lean_inc(x_936);
x_937 = lean_ctor_get(x_5, 1);
lean_inc(x_937);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_936);
lean_inc(x_1);
x_938 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_936, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_938) == 0)
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; 
x_939 = lean_ctor_get(x_938, 0);
lean_inc(x_939);
x_940 = lean_ctor_get(x_938, 1);
lean_inc(x_940);
lean_dec(x_938);
lean_inc(x_937);
x_941 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_937, x_6, x_7, x_8, x_9, x_10, x_11, x_940);
if (lean_obj_tag(x_941) == 0)
{
uint8_t x_942; 
x_942 = !lean_is_exclusive(x_941);
if (x_942 == 0)
{
lean_object* x_943; size_t x_944; size_t x_945; uint8_t x_946; 
x_943 = lean_ctor_get(x_941, 0);
x_944 = lean_ptr_addr(x_936);
lean_dec(x_936);
x_945 = lean_ptr_addr(x_939);
x_946 = lean_usize_dec_eq(x_944, x_945);
if (x_946 == 0)
{
lean_object* x_947; 
lean_dec(x_937);
lean_dec(x_5);
x_947 = l_Lean_Expr_app___override(x_939, x_943);
lean_ctor_set(x_941, 0, x_947);
return x_941;
}
else
{
size_t x_948; size_t x_949; uint8_t x_950; 
x_948 = lean_ptr_addr(x_937);
lean_dec(x_937);
x_949 = lean_ptr_addr(x_943);
x_950 = lean_usize_dec_eq(x_948, x_949);
if (x_950 == 0)
{
lean_object* x_951; 
lean_dec(x_5);
x_951 = l_Lean_Expr_app___override(x_939, x_943);
lean_ctor_set(x_941, 0, x_951);
return x_941;
}
else
{
lean_dec(x_943);
lean_dec(x_939);
lean_ctor_set(x_941, 0, x_5);
return x_941;
}
}
}
else
{
lean_object* x_952; lean_object* x_953; size_t x_954; size_t x_955; uint8_t x_956; 
x_952 = lean_ctor_get(x_941, 0);
x_953 = lean_ctor_get(x_941, 1);
lean_inc(x_953);
lean_inc(x_952);
lean_dec(x_941);
x_954 = lean_ptr_addr(x_936);
lean_dec(x_936);
x_955 = lean_ptr_addr(x_939);
x_956 = lean_usize_dec_eq(x_954, x_955);
if (x_956 == 0)
{
lean_object* x_957; lean_object* x_958; 
lean_dec(x_937);
lean_dec(x_5);
x_957 = l_Lean_Expr_app___override(x_939, x_952);
x_958 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_958, 0, x_957);
lean_ctor_set(x_958, 1, x_953);
return x_958;
}
else
{
size_t x_959; size_t x_960; uint8_t x_961; 
x_959 = lean_ptr_addr(x_937);
lean_dec(x_937);
x_960 = lean_ptr_addr(x_952);
x_961 = lean_usize_dec_eq(x_959, x_960);
if (x_961 == 0)
{
lean_object* x_962; lean_object* x_963; 
lean_dec(x_5);
x_962 = l_Lean_Expr_app___override(x_939, x_952);
x_963 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_963, 0, x_962);
lean_ctor_set(x_963, 1, x_953);
return x_963;
}
else
{
lean_object* x_964; 
lean_dec(x_952);
lean_dec(x_939);
x_964 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_964, 0, x_5);
lean_ctor_set(x_964, 1, x_953);
return x_964;
}
}
}
}
else
{
uint8_t x_965; 
lean_dec(x_939);
lean_dec(x_937);
lean_dec(x_936);
lean_dec(x_5);
x_965 = !lean_is_exclusive(x_941);
if (x_965 == 0)
{
return x_941;
}
else
{
lean_object* x_966; lean_object* x_967; lean_object* x_968; 
x_966 = lean_ctor_get(x_941, 0);
x_967 = lean_ctor_get(x_941, 1);
lean_inc(x_967);
lean_inc(x_966);
lean_dec(x_941);
x_968 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_968, 0, x_966);
lean_ctor_set(x_968, 1, x_967);
return x_968;
}
}
}
else
{
uint8_t x_969; 
lean_dec(x_937);
lean_dec(x_936);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_969 = !lean_is_exclusive(x_938);
if (x_969 == 0)
{
return x_938;
}
else
{
lean_object* x_970; lean_object* x_971; lean_object* x_972; 
x_970 = lean_ctor_get(x_938, 0);
x_971 = lean_ctor_get(x_938, 1);
lean_inc(x_971);
lean_inc(x_970);
lean_dec(x_938);
x_972 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_972, 0, x_970);
lean_ctor_set(x_972, 1, x_971);
return x_972;
}
}
}
case 6:
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; uint8_t x_976; lean_object* x_977; 
x_973 = lean_ctor_get(x_5, 0);
lean_inc(x_973);
x_974 = lean_ctor_get(x_5, 1);
lean_inc(x_974);
x_975 = lean_ctor_get(x_5, 2);
lean_inc(x_975);
x_976 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_974);
lean_inc(x_1);
x_977 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_974, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_977) == 0)
{
lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; 
x_978 = lean_ctor_get(x_977, 0);
lean_inc(x_978);
x_979 = lean_ctor_get(x_977, 1);
lean_inc(x_979);
lean_dec(x_977);
x_980 = lean_unsigned_to_nat(1u);
x_981 = lean_nat_add(x_6, x_980);
lean_dec(x_6);
lean_inc(x_975);
x_982 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_975, x_981, x_7, x_8, x_9, x_10, x_11, x_979);
if (lean_obj_tag(x_982) == 0)
{
uint8_t x_983; 
x_983 = !lean_is_exclusive(x_982);
if (x_983 == 0)
{
lean_object* x_984; lean_object* x_985; size_t x_986; size_t x_987; uint8_t x_988; 
x_984 = lean_ctor_get(x_982, 0);
lean_inc(x_975);
lean_inc(x_974);
lean_inc(x_973);
x_985 = l_Lean_Expr_lam___override(x_973, x_974, x_975, x_976);
x_986 = lean_ptr_addr(x_974);
lean_dec(x_974);
x_987 = lean_ptr_addr(x_978);
x_988 = lean_usize_dec_eq(x_986, x_987);
if (x_988 == 0)
{
lean_object* x_989; 
lean_dec(x_985);
lean_dec(x_975);
x_989 = l_Lean_Expr_lam___override(x_973, x_978, x_984, x_976);
lean_ctor_set(x_982, 0, x_989);
return x_982;
}
else
{
size_t x_990; size_t x_991; uint8_t x_992; 
x_990 = lean_ptr_addr(x_975);
lean_dec(x_975);
x_991 = lean_ptr_addr(x_984);
x_992 = lean_usize_dec_eq(x_990, x_991);
if (x_992 == 0)
{
lean_object* x_993; 
lean_dec(x_985);
x_993 = l_Lean_Expr_lam___override(x_973, x_978, x_984, x_976);
lean_ctor_set(x_982, 0, x_993);
return x_982;
}
else
{
uint8_t x_994; 
x_994 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_976, x_976);
if (x_994 == 0)
{
lean_object* x_995; 
lean_dec(x_985);
x_995 = l_Lean_Expr_lam___override(x_973, x_978, x_984, x_976);
lean_ctor_set(x_982, 0, x_995);
return x_982;
}
else
{
lean_dec(x_984);
lean_dec(x_978);
lean_dec(x_973);
lean_ctor_set(x_982, 0, x_985);
return x_982;
}
}
}
}
else
{
lean_object* x_996; lean_object* x_997; lean_object* x_998; size_t x_999; size_t x_1000; uint8_t x_1001; 
x_996 = lean_ctor_get(x_982, 0);
x_997 = lean_ctor_get(x_982, 1);
lean_inc(x_997);
lean_inc(x_996);
lean_dec(x_982);
lean_inc(x_975);
lean_inc(x_974);
lean_inc(x_973);
x_998 = l_Lean_Expr_lam___override(x_973, x_974, x_975, x_976);
x_999 = lean_ptr_addr(x_974);
lean_dec(x_974);
x_1000 = lean_ptr_addr(x_978);
x_1001 = lean_usize_dec_eq(x_999, x_1000);
if (x_1001 == 0)
{
lean_object* x_1002; lean_object* x_1003; 
lean_dec(x_998);
lean_dec(x_975);
x_1002 = l_Lean_Expr_lam___override(x_973, x_978, x_996, x_976);
x_1003 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1003, 0, x_1002);
lean_ctor_set(x_1003, 1, x_997);
return x_1003;
}
else
{
size_t x_1004; size_t x_1005; uint8_t x_1006; 
x_1004 = lean_ptr_addr(x_975);
lean_dec(x_975);
x_1005 = lean_ptr_addr(x_996);
x_1006 = lean_usize_dec_eq(x_1004, x_1005);
if (x_1006 == 0)
{
lean_object* x_1007; lean_object* x_1008; 
lean_dec(x_998);
x_1007 = l_Lean_Expr_lam___override(x_973, x_978, x_996, x_976);
x_1008 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1008, 0, x_1007);
lean_ctor_set(x_1008, 1, x_997);
return x_1008;
}
else
{
uint8_t x_1009; 
x_1009 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_976, x_976);
if (x_1009 == 0)
{
lean_object* x_1010; lean_object* x_1011; 
lean_dec(x_998);
x_1010 = l_Lean_Expr_lam___override(x_973, x_978, x_996, x_976);
x_1011 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1011, 0, x_1010);
lean_ctor_set(x_1011, 1, x_997);
return x_1011;
}
else
{
lean_object* x_1012; 
lean_dec(x_996);
lean_dec(x_978);
lean_dec(x_973);
x_1012 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1012, 0, x_998);
lean_ctor_set(x_1012, 1, x_997);
return x_1012;
}
}
}
}
}
else
{
uint8_t x_1013; 
lean_dec(x_978);
lean_dec(x_975);
lean_dec(x_974);
lean_dec(x_973);
x_1013 = !lean_is_exclusive(x_982);
if (x_1013 == 0)
{
return x_982;
}
else
{
lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; 
x_1014 = lean_ctor_get(x_982, 0);
x_1015 = lean_ctor_get(x_982, 1);
lean_inc(x_1015);
lean_inc(x_1014);
lean_dec(x_982);
x_1016 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1016, 0, x_1014);
lean_ctor_set(x_1016, 1, x_1015);
return x_1016;
}
}
}
else
{
uint8_t x_1017; 
lean_dec(x_975);
lean_dec(x_974);
lean_dec(x_973);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1017 = !lean_is_exclusive(x_977);
if (x_1017 == 0)
{
return x_977;
}
else
{
lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; 
x_1018 = lean_ctor_get(x_977, 0);
x_1019 = lean_ctor_get(x_977, 1);
lean_inc(x_1019);
lean_inc(x_1018);
lean_dec(x_977);
x_1020 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1020, 0, x_1018);
lean_ctor_set(x_1020, 1, x_1019);
return x_1020;
}
}
}
case 7:
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; uint8_t x_1024; lean_object* x_1025; 
x_1021 = lean_ctor_get(x_5, 0);
lean_inc(x_1021);
x_1022 = lean_ctor_get(x_5, 1);
lean_inc(x_1022);
x_1023 = lean_ctor_get(x_5, 2);
lean_inc(x_1023);
x_1024 = lean_ctor_get_uint8(x_5, sizeof(void*)*3 + 8);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1022);
lean_inc(x_1);
x_1025 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1022, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1025) == 0)
{
lean_object* x_1026; lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; 
x_1026 = lean_ctor_get(x_1025, 0);
lean_inc(x_1026);
x_1027 = lean_ctor_get(x_1025, 1);
lean_inc(x_1027);
lean_dec(x_1025);
x_1028 = lean_unsigned_to_nat(1u);
x_1029 = lean_nat_add(x_6, x_1028);
lean_dec(x_6);
lean_inc(x_1023);
x_1030 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1023, x_1029, x_7, x_8, x_9, x_10, x_11, x_1027);
if (lean_obj_tag(x_1030) == 0)
{
uint8_t x_1031; 
x_1031 = !lean_is_exclusive(x_1030);
if (x_1031 == 0)
{
lean_object* x_1032; lean_object* x_1033; size_t x_1034; size_t x_1035; uint8_t x_1036; 
x_1032 = lean_ctor_get(x_1030, 0);
lean_inc(x_1023);
lean_inc(x_1022);
lean_inc(x_1021);
x_1033 = l_Lean_Expr_forallE___override(x_1021, x_1022, x_1023, x_1024);
x_1034 = lean_ptr_addr(x_1022);
lean_dec(x_1022);
x_1035 = lean_ptr_addr(x_1026);
x_1036 = lean_usize_dec_eq(x_1034, x_1035);
if (x_1036 == 0)
{
lean_object* x_1037; 
lean_dec(x_1033);
lean_dec(x_1023);
x_1037 = l_Lean_Expr_forallE___override(x_1021, x_1026, x_1032, x_1024);
lean_ctor_set(x_1030, 0, x_1037);
return x_1030;
}
else
{
size_t x_1038; size_t x_1039; uint8_t x_1040; 
x_1038 = lean_ptr_addr(x_1023);
lean_dec(x_1023);
x_1039 = lean_ptr_addr(x_1032);
x_1040 = lean_usize_dec_eq(x_1038, x_1039);
if (x_1040 == 0)
{
lean_object* x_1041; 
lean_dec(x_1033);
x_1041 = l_Lean_Expr_forallE___override(x_1021, x_1026, x_1032, x_1024);
lean_ctor_set(x_1030, 0, x_1041);
return x_1030;
}
else
{
uint8_t x_1042; 
x_1042 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_1024, x_1024);
if (x_1042 == 0)
{
lean_object* x_1043; 
lean_dec(x_1033);
x_1043 = l_Lean_Expr_forallE___override(x_1021, x_1026, x_1032, x_1024);
lean_ctor_set(x_1030, 0, x_1043);
return x_1030;
}
else
{
lean_dec(x_1032);
lean_dec(x_1026);
lean_dec(x_1021);
lean_ctor_set(x_1030, 0, x_1033);
return x_1030;
}
}
}
}
else
{
lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; size_t x_1047; size_t x_1048; uint8_t x_1049; 
x_1044 = lean_ctor_get(x_1030, 0);
x_1045 = lean_ctor_get(x_1030, 1);
lean_inc(x_1045);
lean_inc(x_1044);
lean_dec(x_1030);
lean_inc(x_1023);
lean_inc(x_1022);
lean_inc(x_1021);
x_1046 = l_Lean_Expr_forallE___override(x_1021, x_1022, x_1023, x_1024);
x_1047 = lean_ptr_addr(x_1022);
lean_dec(x_1022);
x_1048 = lean_ptr_addr(x_1026);
x_1049 = lean_usize_dec_eq(x_1047, x_1048);
if (x_1049 == 0)
{
lean_object* x_1050; lean_object* x_1051; 
lean_dec(x_1046);
lean_dec(x_1023);
x_1050 = l_Lean_Expr_forallE___override(x_1021, x_1026, x_1044, x_1024);
x_1051 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1051, 0, x_1050);
lean_ctor_set(x_1051, 1, x_1045);
return x_1051;
}
else
{
size_t x_1052; size_t x_1053; uint8_t x_1054; 
x_1052 = lean_ptr_addr(x_1023);
lean_dec(x_1023);
x_1053 = lean_ptr_addr(x_1044);
x_1054 = lean_usize_dec_eq(x_1052, x_1053);
if (x_1054 == 0)
{
lean_object* x_1055; lean_object* x_1056; 
lean_dec(x_1046);
x_1055 = l_Lean_Expr_forallE___override(x_1021, x_1026, x_1044, x_1024);
x_1056 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1056, 0, x_1055);
lean_ctor_set(x_1056, 1, x_1045);
return x_1056;
}
else
{
uint8_t x_1057; 
x_1057 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_1024, x_1024);
if (x_1057 == 0)
{
lean_object* x_1058; lean_object* x_1059; 
lean_dec(x_1046);
x_1058 = l_Lean_Expr_forallE___override(x_1021, x_1026, x_1044, x_1024);
x_1059 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1059, 0, x_1058);
lean_ctor_set(x_1059, 1, x_1045);
return x_1059;
}
else
{
lean_object* x_1060; 
lean_dec(x_1044);
lean_dec(x_1026);
lean_dec(x_1021);
x_1060 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1060, 0, x_1046);
lean_ctor_set(x_1060, 1, x_1045);
return x_1060;
}
}
}
}
}
else
{
uint8_t x_1061; 
lean_dec(x_1026);
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
x_1061 = !lean_is_exclusive(x_1030);
if (x_1061 == 0)
{
return x_1030;
}
else
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; 
x_1062 = lean_ctor_get(x_1030, 0);
x_1063 = lean_ctor_get(x_1030, 1);
lean_inc(x_1063);
lean_inc(x_1062);
lean_dec(x_1030);
x_1064 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1064, 0, x_1062);
lean_ctor_set(x_1064, 1, x_1063);
return x_1064;
}
}
}
else
{
uint8_t x_1065; 
lean_dec(x_1023);
lean_dec(x_1022);
lean_dec(x_1021);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1065 = !lean_is_exclusive(x_1025);
if (x_1065 == 0)
{
return x_1025;
}
else
{
lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; 
x_1066 = lean_ctor_get(x_1025, 0);
x_1067 = lean_ctor_get(x_1025, 1);
lean_inc(x_1067);
lean_inc(x_1066);
lean_dec(x_1025);
x_1068 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1068, 0, x_1066);
lean_ctor_set(x_1068, 1, x_1067);
return x_1068;
}
}
}
case 8:
{
lean_object* x_1069; lean_object* x_1070; lean_object* x_1071; lean_object* x_1072; uint8_t x_1073; lean_object* x_1074; 
x_1069 = lean_ctor_get(x_5, 0);
lean_inc(x_1069);
x_1070 = lean_ctor_get(x_5, 1);
lean_inc(x_1070);
x_1071 = lean_ctor_get(x_5, 2);
lean_inc(x_1071);
x_1072 = lean_ctor_get(x_5, 3);
lean_inc(x_1072);
x_1073 = lean_ctor_get_uint8(x_5, sizeof(void*)*4 + 8);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1070);
lean_inc(x_1);
x_1074 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1070, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1074) == 0)
{
lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; 
x_1075 = lean_ctor_get(x_1074, 0);
lean_inc(x_1075);
x_1076 = lean_ctor_get(x_1074, 1);
lean_inc(x_1076);
lean_dec(x_1074);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_1071);
lean_inc(x_1);
x_1077 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1071, x_6, x_7, x_8, x_9, x_10, x_11, x_1076);
if (lean_obj_tag(x_1077) == 0)
{
lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; 
x_1078 = lean_ctor_get(x_1077, 0);
lean_inc(x_1078);
x_1079 = lean_ctor_get(x_1077, 1);
lean_inc(x_1079);
lean_dec(x_1077);
x_1080 = lean_unsigned_to_nat(1u);
x_1081 = lean_nat_add(x_6, x_1080);
lean_dec(x_6);
lean_inc(x_1072);
x_1082 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1072, x_1081, x_7, x_8, x_9, x_10, x_11, x_1079);
if (lean_obj_tag(x_1082) == 0)
{
uint8_t x_1083; 
x_1083 = !lean_is_exclusive(x_1082);
if (x_1083 == 0)
{
lean_object* x_1084; size_t x_1085; size_t x_1086; uint8_t x_1087; 
x_1084 = lean_ctor_get(x_1082, 0);
x_1085 = lean_ptr_addr(x_1070);
lean_dec(x_1070);
x_1086 = lean_ptr_addr(x_1075);
x_1087 = lean_usize_dec_eq(x_1085, x_1086);
if (x_1087 == 0)
{
lean_object* x_1088; 
lean_dec(x_1072);
lean_dec(x_1071);
lean_dec(x_5);
x_1088 = l_Lean_Expr_letE___override(x_1069, x_1075, x_1078, x_1084, x_1073);
lean_ctor_set(x_1082, 0, x_1088);
return x_1082;
}
else
{
size_t x_1089; size_t x_1090; uint8_t x_1091; 
x_1089 = lean_ptr_addr(x_1071);
lean_dec(x_1071);
x_1090 = lean_ptr_addr(x_1078);
x_1091 = lean_usize_dec_eq(x_1089, x_1090);
if (x_1091 == 0)
{
lean_object* x_1092; 
lean_dec(x_1072);
lean_dec(x_5);
x_1092 = l_Lean_Expr_letE___override(x_1069, x_1075, x_1078, x_1084, x_1073);
lean_ctor_set(x_1082, 0, x_1092);
return x_1082;
}
else
{
size_t x_1093; size_t x_1094; uint8_t x_1095; 
x_1093 = lean_ptr_addr(x_1072);
lean_dec(x_1072);
x_1094 = lean_ptr_addr(x_1084);
x_1095 = lean_usize_dec_eq(x_1093, x_1094);
if (x_1095 == 0)
{
lean_object* x_1096; 
lean_dec(x_5);
x_1096 = l_Lean_Expr_letE___override(x_1069, x_1075, x_1078, x_1084, x_1073);
lean_ctor_set(x_1082, 0, x_1096);
return x_1082;
}
else
{
lean_dec(x_1084);
lean_dec(x_1078);
lean_dec(x_1075);
lean_dec(x_1069);
lean_ctor_set(x_1082, 0, x_5);
return x_1082;
}
}
}
}
else
{
lean_object* x_1097; lean_object* x_1098; size_t x_1099; size_t x_1100; uint8_t x_1101; 
x_1097 = lean_ctor_get(x_1082, 0);
x_1098 = lean_ctor_get(x_1082, 1);
lean_inc(x_1098);
lean_inc(x_1097);
lean_dec(x_1082);
x_1099 = lean_ptr_addr(x_1070);
lean_dec(x_1070);
x_1100 = lean_ptr_addr(x_1075);
x_1101 = lean_usize_dec_eq(x_1099, x_1100);
if (x_1101 == 0)
{
lean_object* x_1102; lean_object* x_1103; 
lean_dec(x_1072);
lean_dec(x_1071);
lean_dec(x_5);
x_1102 = l_Lean_Expr_letE___override(x_1069, x_1075, x_1078, x_1097, x_1073);
x_1103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1103, 0, x_1102);
lean_ctor_set(x_1103, 1, x_1098);
return x_1103;
}
else
{
size_t x_1104; size_t x_1105; uint8_t x_1106; 
x_1104 = lean_ptr_addr(x_1071);
lean_dec(x_1071);
x_1105 = lean_ptr_addr(x_1078);
x_1106 = lean_usize_dec_eq(x_1104, x_1105);
if (x_1106 == 0)
{
lean_object* x_1107; lean_object* x_1108; 
lean_dec(x_1072);
lean_dec(x_5);
x_1107 = l_Lean_Expr_letE___override(x_1069, x_1075, x_1078, x_1097, x_1073);
x_1108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1108, 0, x_1107);
lean_ctor_set(x_1108, 1, x_1098);
return x_1108;
}
else
{
size_t x_1109; size_t x_1110; uint8_t x_1111; 
x_1109 = lean_ptr_addr(x_1072);
lean_dec(x_1072);
x_1110 = lean_ptr_addr(x_1097);
x_1111 = lean_usize_dec_eq(x_1109, x_1110);
if (x_1111 == 0)
{
lean_object* x_1112; lean_object* x_1113; 
lean_dec(x_5);
x_1112 = l_Lean_Expr_letE___override(x_1069, x_1075, x_1078, x_1097, x_1073);
x_1113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1113, 0, x_1112);
lean_ctor_set(x_1113, 1, x_1098);
return x_1113;
}
else
{
lean_object* x_1114; 
lean_dec(x_1097);
lean_dec(x_1078);
lean_dec(x_1075);
lean_dec(x_1069);
x_1114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1114, 0, x_5);
lean_ctor_set(x_1114, 1, x_1098);
return x_1114;
}
}
}
}
}
else
{
uint8_t x_1115; 
lean_dec(x_1078);
lean_dec(x_1075);
lean_dec(x_1072);
lean_dec(x_1071);
lean_dec(x_1070);
lean_dec(x_1069);
lean_dec(x_5);
x_1115 = !lean_is_exclusive(x_1082);
if (x_1115 == 0)
{
return x_1082;
}
else
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; 
x_1116 = lean_ctor_get(x_1082, 0);
x_1117 = lean_ctor_get(x_1082, 1);
lean_inc(x_1117);
lean_inc(x_1116);
lean_dec(x_1082);
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
lean_dec(x_1075);
lean_dec(x_1072);
lean_dec(x_1071);
lean_dec(x_1070);
lean_dec(x_1069);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1119 = !lean_is_exclusive(x_1077);
if (x_1119 == 0)
{
return x_1077;
}
else
{
lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; 
x_1120 = lean_ctor_get(x_1077, 0);
x_1121 = lean_ctor_get(x_1077, 1);
lean_inc(x_1121);
lean_inc(x_1120);
lean_dec(x_1077);
x_1122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1122, 0, x_1120);
lean_ctor_set(x_1122, 1, x_1121);
return x_1122;
}
}
}
else
{
uint8_t x_1123; 
lean_dec(x_1072);
lean_dec(x_1071);
lean_dec(x_1070);
lean_dec(x_1069);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_1123 = !lean_is_exclusive(x_1074);
if (x_1123 == 0)
{
return x_1074;
}
else
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; 
x_1124 = lean_ctor_get(x_1074, 0);
x_1125 = lean_ctor_get(x_1074, 1);
lean_inc(x_1125);
lean_inc(x_1124);
lean_dec(x_1074);
x_1126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1126, 0, x_1124);
lean_ctor_set(x_1126, 1, x_1125);
return x_1126;
}
}
}
case 10:
{
lean_object* x_1127; lean_object* x_1128; lean_object* x_1129; 
x_1127 = lean_ctor_get(x_5, 0);
lean_inc(x_1127);
x_1128 = lean_ctor_get(x_5, 1);
lean_inc(x_1128);
lean_inc(x_1128);
x_1129 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1128, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1129) == 0)
{
uint8_t x_1130; 
x_1130 = !lean_is_exclusive(x_1129);
if (x_1130 == 0)
{
lean_object* x_1131; size_t x_1132; size_t x_1133; uint8_t x_1134; 
x_1131 = lean_ctor_get(x_1129, 0);
x_1132 = lean_ptr_addr(x_1128);
lean_dec(x_1128);
x_1133 = lean_ptr_addr(x_1131);
x_1134 = lean_usize_dec_eq(x_1132, x_1133);
if (x_1134 == 0)
{
lean_object* x_1135; 
lean_dec(x_5);
x_1135 = l_Lean_Expr_mdata___override(x_1127, x_1131);
lean_ctor_set(x_1129, 0, x_1135);
return x_1129;
}
else
{
lean_dec(x_1131);
lean_dec(x_1127);
lean_ctor_set(x_1129, 0, x_5);
return x_1129;
}
}
else
{
lean_object* x_1136; lean_object* x_1137; size_t x_1138; size_t x_1139; uint8_t x_1140; 
x_1136 = lean_ctor_get(x_1129, 0);
x_1137 = lean_ctor_get(x_1129, 1);
lean_inc(x_1137);
lean_inc(x_1136);
lean_dec(x_1129);
x_1138 = lean_ptr_addr(x_1128);
lean_dec(x_1128);
x_1139 = lean_ptr_addr(x_1136);
x_1140 = lean_usize_dec_eq(x_1138, x_1139);
if (x_1140 == 0)
{
lean_object* x_1141; lean_object* x_1142; 
lean_dec(x_5);
x_1141 = l_Lean_Expr_mdata___override(x_1127, x_1136);
x_1142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1142, 0, x_1141);
lean_ctor_set(x_1142, 1, x_1137);
return x_1142;
}
else
{
lean_object* x_1143; 
lean_dec(x_1136);
lean_dec(x_1127);
x_1143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1143, 0, x_5);
lean_ctor_set(x_1143, 1, x_1137);
return x_1143;
}
}
}
else
{
uint8_t x_1144; 
lean_dec(x_1128);
lean_dec(x_1127);
lean_dec(x_5);
x_1144 = !lean_is_exclusive(x_1129);
if (x_1144 == 0)
{
return x_1129;
}
else
{
lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; 
x_1145 = lean_ctor_get(x_1129, 0);
x_1146 = lean_ctor_get(x_1129, 1);
lean_inc(x_1146);
lean_inc(x_1145);
lean_dec(x_1129);
x_1147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1147, 0, x_1145);
lean_ctor_set(x_1147, 1, x_1146);
return x_1147;
}
}
}
case 11:
{
lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; 
x_1148 = lean_ctor_get(x_5, 0);
lean_inc(x_1148);
x_1149 = lean_ctor_get(x_5, 1);
lean_inc(x_1149);
x_1150 = lean_ctor_get(x_5, 2);
lean_inc(x_1150);
lean_inc(x_1150);
x_1151 = l_Lean_Meta_kabstract_visit(x_1, x_2, x_3, x_4, x_1150, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_1151) == 0)
{
uint8_t x_1152; 
x_1152 = !lean_is_exclusive(x_1151);
if (x_1152 == 0)
{
lean_object* x_1153; size_t x_1154; size_t x_1155; uint8_t x_1156; 
x_1153 = lean_ctor_get(x_1151, 0);
x_1154 = lean_ptr_addr(x_1150);
lean_dec(x_1150);
x_1155 = lean_ptr_addr(x_1153);
x_1156 = lean_usize_dec_eq(x_1154, x_1155);
if (x_1156 == 0)
{
lean_object* x_1157; 
lean_dec(x_5);
x_1157 = l_Lean_Expr_proj___override(x_1148, x_1149, x_1153);
lean_ctor_set(x_1151, 0, x_1157);
return x_1151;
}
else
{
lean_dec(x_1153);
lean_dec(x_1149);
lean_dec(x_1148);
lean_ctor_set(x_1151, 0, x_5);
return x_1151;
}
}
else
{
lean_object* x_1158; lean_object* x_1159; size_t x_1160; size_t x_1161; uint8_t x_1162; 
x_1158 = lean_ctor_get(x_1151, 0);
x_1159 = lean_ctor_get(x_1151, 1);
lean_inc(x_1159);
lean_inc(x_1158);
lean_dec(x_1151);
x_1160 = lean_ptr_addr(x_1150);
lean_dec(x_1150);
x_1161 = lean_ptr_addr(x_1158);
x_1162 = lean_usize_dec_eq(x_1160, x_1161);
if (x_1162 == 0)
{
lean_object* x_1163; lean_object* x_1164; 
lean_dec(x_5);
x_1163 = l_Lean_Expr_proj___override(x_1148, x_1149, x_1158);
x_1164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1164, 0, x_1163);
lean_ctor_set(x_1164, 1, x_1159);
return x_1164;
}
else
{
lean_object* x_1165; 
lean_dec(x_1158);
lean_dec(x_1149);
lean_dec(x_1148);
x_1165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1165, 0, x_5);
lean_ctor_set(x_1165, 1, x_1159);
return x_1165;
}
}
}
else
{
uint8_t x_1166; 
lean_dec(x_1150);
lean_dec(x_1149);
lean_dec(x_1148);
lean_dec(x_5);
x_1166 = !lean_is_exclusive(x_1151);
if (x_1166 == 0)
{
return x_1151;
}
else
{
lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; 
x_1167 = lean_ctor_get(x_1151, 0);
x_1168 = lean_ctor_get(x_1151, 1);
lean_inc(x_1168);
lean_inc(x_1167);
lean_dec(x_1151);
x_1169 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1169, 0, x_1167);
lean_ctor_set(x_1169, 1, x_1168);
return x_1169;
}
}
}
default: 
{
lean_object* x_1170; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_1170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1170, 0, x_5);
lean_ctor_set(x_1170, 1, x_12);
return x_1170;
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
x_72 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_54, x_54);
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
x_87 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_54, x_54);
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
x_120 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_102, x_102);
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
x_135 = l___private_Lean_Expr_0__Lean_beqBinderInfo____x40_Lean_Expr___hyg_477_(x_102, x_102);
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
x_9 = l_Lean_instantiateMVars___at___private_Lean_Meta_Basic_0__Lean_Meta_mkLeveErrorMessageCore___spec__2(x_1, x_4, x_5, x_6, x_7, x_8);
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
x_16 = l_Lean_Expr_headNumArgs_go(x_2, x_15);
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
x_41 = l_Lean_Expr_headNumArgs_go(x_2, x_40);
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
x_70 = l_Lean_Expr_headNumArgs_go(x_2, x_69);
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
x_94 = l_Lean_Expr_headNumArgs_go(x_2, x_93);
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
