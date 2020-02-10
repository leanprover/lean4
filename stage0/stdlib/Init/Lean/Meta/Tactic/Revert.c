// Lean compiler output
// Module: Init.Lean.Meta.Tactic.Revert
// Imports: Init.Lean.Meta.Tactic.Util
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
lean_object* l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_mkMVar(lean_object*);
extern lean_object* l_Array_empty___closed__1;
lean_object* l_Lean_Meta_elimMVarDeps(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarTag(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
extern lean_object* l_Lean_Expr_getAppArgs___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgsAux___main(lean_object*, lean_object*);
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_revert___spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert___closed__2;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_revert___spec__2(lean_object*, lean_object*);
lean_object* lean_name_mk_string(lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMVarKind(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_revert___closed__1;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_LocalInstance_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_revert___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_setMVarTag(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean_box(0);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
lean_inc(x_7);
x_11 = l_Lean_mkFVar(x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
lean_dec(x_7);
x_15 = lean_array_fset(x_10, x_1, x_14);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
lean_object* l_Array_umapMAux___main___at_Lean_Meta_revert___spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_array_get_size(x_2);
x_4 = lean_nat_dec_lt(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_5 = l_Array_empty___closed__1;
x_6 = x_2;
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_array_fget(x_2, x_1);
x_8 = lean_box(0);
x_9 = x_8;
x_10 = lean_array_fset(x_2, x_1, x_9);
x_11 = l_Lean_Expr_fvarId_x21(x_7);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_1, x_12);
x_14 = x_11;
lean_dec(x_7);
x_15 = lean_array_fset(x_10, x_1, x_14);
lean_dec(x_1);
x_1 = x_13;
x_2 = x_15;
goto _start;
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_array_set(x_3, x_4, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_2 = x_7;
x_3 = x_9;
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_4);
x_13 = l_Lean_Expr_mvarId_x21(x_2);
lean_dec(x_2);
lean_inc(x_13);
x_14 = l_Lean_Meta_setMVarTag(x_13, x_1, x_5, x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__2(x_17, x_3);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__2(x_21, x_3);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
}
}
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_revert___spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_4);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
lean_dec(x_6);
x_9 = 1;
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_array_fget(x_4, x_6);
x_11 = lean_array_fget(x_5, x_6);
x_12 = l_Lean_LocalInstance_beq(x_10, x_11);
lean_dec(x_11);
lean_dec(x_10);
if (x_12 == 0)
{
uint8_t x_13; 
lean_dec(x_6);
x_13 = 0;
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_3 = lean_box(0);
x_6 = x_15;
goto _start;
}
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_array_set(x_3, x_4, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
lean_dec(x_4);
x_2 = x_7;
x_3 = x_9;
x_4 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_dec(x_4);
x_13 = l_Lean_Expr_mvarId_x21(x_2);
lean_dec(x_2);
lean_inc(x_13);
x_14 = l_Lean_Meta_setMVarTag(x_13, x_1, x_5, x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__2(x_17, x_3);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_unsigned_to_nat(0u);
x_22 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__2(x_21, x_3);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_13);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
}
}
lean_object* _init_l_Lean_Meta_revert___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string("revert");
return x_1;
}
}
lean_object* _init_l_Lean_Meta_revert___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Meta_revert___closed__1;
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
lean_object* l_Lean_Meta_revert(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEmpty___rarg(x_2);
if (x_6 == 0)
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_Meta_getMVarDecl(x_1, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_11 = lean_ctor_get(x_4, 0);
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_ctor_get(x_4, 3);
x_14 = lean_ctor_get(x_4, 4);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_8, 4);
lean_inc(x_16);
x_17 = lean_array_get_size(x_12);
x_18 = lean_array_get_size(x_16);
x_19 = lean_nat_dec_eq(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_16);
lean_inc(x_11);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_15);
lean_ctor_set(x_20, 2, x_16);
lean_ctor_set(x_20, 3, x_13);
lean_ctor_set(x_20, 4, x_14);
if (x_19 == 0)
{
lean_object* x_267; 
lean_dec(x_16);
lean_dec(x_8);
x_267 = lean_box(0);
x_21 = x_267;
goto block_266;
}
else
{
lean_object* x_268; uint8_t x_269; 
x_268 = lean_unsigned_to_nat(0u);
x_269 = l_Array_isEqvAux___main___at_Lean_Meta_revert___spec__4(x_4, x_8, lean_box(0), x_12, x_16, x_268);
lean_dec(x_16);
lean_dec(x_8);
if (x_269 == 0)
{
lean_object* x_270; 
x_270 = lean_box(0);
x_21 = x_270;
goto block_266;
}
else
{
lean_object* x_271; 
lean_dec(x_10);
lean_inc(x_1);
x_271 = l_Lean_Meta_getMVarTag(x_1, x_20, x_9);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
lean_dec(x_271);
x_274 = l_Lean_Meta_revert___closed__2;
lean_inc(x_1);
x_275 = l_Lean_Meta_checkNotAssigned(x_1, x_274, x_20, x_273);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_276 = lean_ctor_get(x_275, 1);
lean_inc(x_276);
lean_dec(x_275);
x_277 = 0;
lean_inc(x_1);
x_278 = l_Lean_Meta_setMVarKind(x_1, x_277, x_20, x_276);
x_279 = lean_ctor_get(x_278, 1);
lean_inc(x_279);
lean_dec(x_278);
x_280 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_268, x_2);
lean_inc(x_1);
x_281 = l_Lean_mkMVar(x_1);
x_282 = l_Lean_Meta_elimMVarDeps(x_280, x_281, x_3, x_20, x_279);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; uint8_t x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = 2;
x_286 = l_Lean_Meta_setMVarKind(x_1, x_285, x_20, x_284);
x_287 = lean_ctor_get(x_286, 1);
lean_inc(x_287);
lean_dec(x_286);
x_288 = l_Lean_Expr_getAppNumArgsAux___main(x_283, x_268);
x_289 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_288);
x_290 = lean_mk_array(x_288, x_289);
x_291 = lean_unsigned_to_nat(1u);
x_292 = lean_nat_sub(x_288, x_291);
lean_dec(x_288);
x_293 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__5(x_272, x_283, x_290, x_292, x_20, x_287);
lean_dec(x_20);
return x_293;
}
else
{
lean_object* x_294; lean_object* x_295; uint8_t x_296; lean_object* x_297; uint8_t x_298; 
lean_dec(x_272);
x_294 = lean_ctor_get(x_282, 0);
lean_inc(x_294);
x_295 = lean_ctor_get(x_282, 1);
lean_inc(x_295);
lean_dec(x_282);
x_296 = 2;
x_297 = l_Lean_Meta_setMVarKind(x_1, x_296, x_20, x_295);
lean_dec(x_20);
x_298 = !lean_is_exclusive(x_297);
if (x_298 == 0)
{
lean_object* x_299; 
x_299 = lean_ctor_get(x_297, 0);
lean_dec(x_299);
lean_ctor_set_tag(x_297, 1);
lean_ctor_set(x_297, 0, x_294);
return x_297;
}
else
{
lean_object* x_300; lean_object* x_301; 
x_300 = lean_ctor_get(x_297, 1);
lean_inc(x_300);
lean_dec(x_297);
x_301 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_301, 0, x_294);
lean_ctor_set(x_301, 1, x_300);
return x_301;
}
}
}
else
{
uint8_t x_302; 
lean_dec(x_272);
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_302 = !lean_is_exclusive(x_275);
if (x_302 == 0)
{
return x_275;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_303 = lean_ctor_get(x_275, 0);
x_304 = lean_ctor_get(x_275, 1);
lean_inc(x_304);
lean_inc(x_303);
lean_dec(x_275);
x_305 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_305, 0, x_303);
lean_ctor_set(x_305, 1, x_304);
return x_305;
}
}
}
else
{
uint8_t x_306; 
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_306 = !lean_is_exclusive(x_271);
if (x_306 == 0)
{
return x_271;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_271, 0);
x_308 = lean_ctor_get(x_271, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_271);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
}
block_266:
{
uint8_t x_22; 
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_9);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_9, 2);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_50; lean_object* x_51; 
x_25 = lean_ctor_get(x_23, 2);
x_50 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_23, 2, x_50);
lean_inc(x_1);
x_51 = l_Lean_Meta_getMVarTag(x_1, x_20, x_9);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Meta_revert___closed__2;
lean_inc(x_1);
x_55 = l_Lean_Meta_checkNotAssigned(x_1, x_54, x_20, x_53);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = 0;
lean_inc(x_1);
x_58 = l_Lean_Meta_setMVarKind(x_1, x_57, x_20, x_56);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_60, x_2);
lean_inc(x_1);
x_62 = l_Lean_mkMVar(x_1);
x_63 = l_Lean_Meta_elimMVarDeps(x_61, x_62, x_3, x_20, x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_10);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = 2;
x_67 = l_Lean_Meta_setMVarKind(x_1, x_66, x_20, x_65);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
x_69 = l_Lean_Expr_getAppNumArgsAux___main(x_64, x_60);
x_70 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_69);
x_71 = lean_mk_array(x_69, x_70);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_sub(x_69, x_72);
lean_dec(x_69);
x_74 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(x_52, x_64, x_71, x_73, x_20, x_68);
lean_dec(x_20);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_75, 2);
lean_inc(x_76);
x_77 = !lean_is_exclusive(x_74);
if (x_77 == 0)
{
lean_object* x_78; uint8_t x_79; 
x_78 = lean_ctor_get(x_74, 1);
lean_dec(x_78);
x_79 = !lean_is_exclusive(x_75);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_75, 2);
lean_dec(x_80);
x_81 = !lean_is_exclusive(x_76);
if (x_81 == 0)
{
lean_object* x_82; 
x_82 = lean_ctor_get(x_76, 2);
lean_dec(x_82);
lean_ctor_set(x_76, 2, x_25);
return x_74;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_76, 0);
x_84 = lean_ctor_get(x_76, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_76);
x_85 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
lean_ctor_set(x_85, 2, x_25);
lean_ctor_set(x_75, 2, x_85);
return x_74;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_86 = lean_ctor_get(x_75, 0);
x_87 = lean_ctor_get(x_75, 1);
x_88 = lean_ctor_get(x_75, 3);
x_89 = lean_ctor_get(x_75, 4);
x_90 = lean_ctor_get(x_75, 5);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_75);
x_91 = lean_ctor_get(x_76, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_76, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 lean_ctor_release(x_76, 2);
 x_93 = x_76;
} else {
 lean_dec_ref(x_76);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(0, 3, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
lean_ctor_set(x_94, 2, x_25);
x_95 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_95, 0, x_86);
lean_ctor_set(x_95, 1, x_87);
lean_ctor_set(x_95, 2, x_94);
lean_ctor_set(x_95, 3, x_88);
lean_ctor_set(x_95, 4, x_89);
lean_ctor_set(x_95, 5, x_90);
lean_ctor_set(x_74, 1, x_95);
return x_74;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_96 = lean_ctor_get(x_74, 0);
lean_inc(x_96);
lean_dec(x_74);
x_97 = lean_ctor_get(x_75, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_75, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_75, 3);
lean_inc(x_99);
x_100 = lean_ctor_get(x_75, 4);
lean_inc(x_100);
x_101 = lean_ctor_get(x_75, 5);
lean_inc(x_101);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 lean_ctor_release(x_75, 2);
 lean_ctor_release(x_75, 3);
 lean_ctor_release(x_75, 4);
 lean_ctor_release(x_75, 5);
 x_102 = x_75;
} else {
 lean_dec_ref(x_75);
 x_102 = lean_box(0);
}
x_103 = lean_ctor_get(x_76, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_76, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 lean_ctor_release(x_76, 2);
 x_105 = x_76;
} else {
 lean_dec_ref(x_76);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 3, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
lean_ctor_set(x_106, 2, x_25);
if (lean_is_scalar(x_102)) {
 x_107 = lean_alloc_ctor(0, 6, 0);
} else {
 x_107 = x_102;
}
lean_ctor_set(x_107, 0, x_97);
lean_ctor_set(x_107, 1, x_98);
lean_ctor_set(x_107, 2, x_106);
lean_ctor_set(x_107, 3, x_99);
lean_ctor_set(x_107, 4, x_100);
lean_ctor_set(x_107, 5, x_101);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_96);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
else
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_52);
x_109 = lean_ctor_get(x_63, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_63, 1);
lean_inc(x_110);
lean_dec(x_63);
x_111 = 2;
x_112 = l_Lean_Meta_setMVarKind(x_1, x_111, x_20, x_110);
lean_dec(x_20);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_26 = x_109;
x_27 = x_113;
goto block_49;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_52);
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_114 = lean_ctor_get(x_55, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_55, 1);
lean_inc(x_115);
lean_dec(x_55);
x_26 = x_114;
x_27 = x_115;
goto block_49;
}
}
else
{
lean_object* x_116; lean_object* x_117; 
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_116 = lean_ctor_get(x_51, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_51, 1);
lean_inc(x_117);
lean_dec(x_51);
x_26 = x_116;
x_27 = x_117;
goto block_49;
}
block_49:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 2);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_29, 2);
lean_dec(x_31);
lean_ctor_set(x_29, 2, x_25);
if (lean_is_scalar(x_10)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_10;
 lean_ctor_set_tag(x_32, 1);
}
lean_ctor_set(x_32, 0, x_26);
lean_ctor_set(x_32, 1, x_27);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_29, 0);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_29);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_25);
lean_ctor_set(x_27, 2, x_35);
if (lean_is_scalar(x_10)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_10;
 lean_ctor_set_tag(x_36, 1);
}
lean_ctor_set(x_36, 0, x_26);
lean_ctor_set(x_36, 1, x_27);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_37 = lean_ctor_get(x_27, 2);
x_38 = lean_ctor_get(x_27, 0);
x_39 = lean_ctor_get(x_27, 1);
x_40 = lean_ctor_get(x_27, 3);
x_41 = lean_ctor_get(x_27, 4);
x_42 = lean_ctor_get(x_27, 5);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_37);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_27);
x_43 = lean_ctor_get(x_37, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 lean_ctor_release(x_37, 2);
 x_45 = x_37;
} else {
 lean_dec_ref(x_37);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 3, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
lean_ctor_set(x_46, 2, x_25);
x_47 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_39);
lean_ctor_set(x_47, 2, x_46);
lean_ctor_set(x_47, 3, x_40);
lean_ctor_set(x_47, 4, x_41);
lean_ctor_set(x_47, 5, x_42);
if (lean_is_scalar(x_10)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_10;
 lean_ctor_set_tag(x_48, 1);
}
lean_ctor_set(x_48, 0, x_26);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_118 = lean_ctor_get(x_23, 0);
x_119 = lean_ctor_get(x_23, 1);
x_120 = lean_ctor_get(x_23, 2);
lean_inc(x_120);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_23);
x_137 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_138 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_138, 0, x_118);
lean_ctor_set(x_138, 1, x_119);
lean_ctor_set(x_138, 2, x_137);
lean_ctor_set(x_9, 2, x_138);
lean_inc(x_1);
x_139 = l_Lean_Meta_getMVarTag(x_1, x_20, x_9);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = l_Lean_Meta_revert___closed__2;
lean_inc(x_1);
x_143 = l_Lean_Meta_checkNotAssigned(x_1, x_142, x_20, x_141);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
lean_dec(x_143);
x_145 = 0;
lean_inc(x_1);
x_146 = l_Lean_Meta_setMVarKind(x_1, x_145, x_20, x_144);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_148 = lean_unsigned_to_nat(0u);
x_149 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_148, x_2);
lean_inc(x_1);
x_150 = l_Lean_mkMVar(x_1);
x_151 = l_Lean_Meta_elimMVarDeps(x_149, x_150, x_3, x_20, x_147);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_10);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = 2;
x_155 = l_Lean_Meta_setMVarKind(x_1, x_154, x_20, x_153);
x_156 = lean_ctor_get(x_155, 1);
lean_inc(x_156);
lean_dec(x_155);
x_157 = l_Lean_Expr_getAppNumArgsAux___main(x_152, x_148);
x_158 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_157);
x_159 = lean_mk_array(x_157, x_158);
x_160 = lean_unsigned_to_nat(1u);
x_161 = lean_nat_sub(x_157, x_160);
lean_dec(x_157);
x_162 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(x_140, x_152, x_159, x_161, x_20, x_156);
lean_dec(x_20);
x_163 = lean_ctor_get(x_162, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_163, 2);
lean_inc(x_164);
x_165 = lean_ctor_get(x_162, 0);
lean_inc(x_165);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_166 = x_162;
} else {
 lean_dec_ref(x_162);
 x_166 = lean_box(0);
}
x_167 = lean_ctor_get(x_163, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_163, 1);
lean_inc(x_168);
x_169 = lean_ctor_get(x_163, 3);
lean_inc(x_169);
x_170 = lean_ctor_get(x_163, 4);
lean_inc(x_170);
x_171 = lean_ctor_get(x_163, 5);
lean_inc(x_171);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 lean_ctor_release(x_163, 2);
 lean_ctor_release(x_163, 3);
 lean_ctor_release(x_163, 4);
 lean_ctor_release(x_163, 5);
 x_172 = x_163;
} else {
 lean_dec_ref(x_163);
 x_172 = lean_box(0);
}
x_173 = lean_ctor_get(x_164, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_164, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 lean_ctor_release(x_164, 2);
 x_175 = x_164;
} else {
 lean_dec_ref(x_164);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(0, 3, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
lean_ctor_set(x_176, 2, x_120);
if (lean_is_scalar(x_172)) {
 x_177 = lean_alloc_ctor(0, 6, 0);
} else {
 x_177 = x_172;
}
lean_ctor_set(x_177, 0, x_167);
lean_ctor_set(x_177, 1, x_168);
lean_ctor_set(x_177, 2, x_176);
lean_ctor_set(x_177, 3, x_169);
lean_ctor_set(x_177, 4, x_170);
lean_ctor_set(x_177, 5, x_171);
if (lean_is_scalar(x_166)) {
 x_178 = lean_alloc_ctor(0, 2, 0);
} else {
 x_178 = x_166;
}
lean_ctor_set(x_178, 0, x_165);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_140);
x_179 = lean_ctor_get(x_151, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_151, 1);
lean_inc(x_180);
lean_dec(x_151);
x_181 = 2;
x_182 = l_Lean_Meta_setMVarKind(x_1, x_181, x_20, x_180);
lean_dec(x_20);
x_183 = lean_ctor_get(x_182, 1);
lean_inc(x_183);
lean_dec(x_182);
x_121 = x_179;
x_122 = x_183;
goto block_136;
}
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_140);
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_184 = lean_ctor_get(x_143, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_143, 1);
lean_inc(x_185);
lean_dec(x_143);
x_121 = x_184;
x_122 = x_185;
goto block_136;
}
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_186 = lean_ctor_get(x_139, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_139, 1);
lean_inc(x_187);
lean_dec(x_139);
x_121 = x_186;
x_122 = x_187;
goto block_136;
}
block_136:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_123 = lean_ctor_get(x_122, 2);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_122, 3);
lean_inc(x_126);
x_127 = lean_ctor_get(x_122, 4);
lean_inc(x_127);
x_128 = lean_ctor_get(x_122, 5);
lean_inc(x_128);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 lean_ctor_release(x_122, 2);
 lean_ctor_release(x_122, 3);
 lean_ctor_release(x_122, 4);
 lean_ctor_release(x_122, 5);
 x_129 = x_122;
} else {
 lean_dec_ref(x_122);
 x_129 = lean_box(0);
}
x_130 = lean_ctor_get(x_123, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_123, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 x_132 = x_123;
} else {
 lean_dec_ref(x_123);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(0, 3, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
lean_ctor_set(x_133, 2, x_120);
if (lean_is_scalar(x_129)) {
 x_134 = lean_alloc_ctor(0, 6, 0);
} else {
 x_134 = x_129;
}
lean_ctor_set(x_134, 0, x_124);
lean_ctor_set(x_134, 1, x_125);
lean_ctor_set(x_134, 2, x_133);
lean_ctor_set(x_134, 3, x_126);
lean_ctor_set(x_134, 4, x_127);
lean_ctor_set(x_134, 5, x_128);
if (lean_is_scalar(x_10)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_10;
 lean_ctor_set_tag(x_135, 1);
}
lean_ctor_set(x_135, 0, x_121);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_188 = lean_ctor_get(x_9, 2);
x_189 = lean_ctor_get(x_9, 0);
x_190 = lean_ctor_get(x_9, 1);
x_191 = lean_ctor_get(x_9, 3);
x_192 = lean_ctor_get(x_9, 4);
x_193 = lean_ctor_get(x_9, 5);
lean_inc(x_193);
lean_inc(x_192);
lean_inc(x_191);
lean_inc(x_188);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_9);
x_194 = lean_ctor_get(x_188, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_188, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_188, 2);
lean_inc(x_196);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 lean_ctor_release(x_188, 2);
 x_197 = x_188;
} else {
 lean_dec_ref(x_188);
 x_197 = lean_box(0);
}
x_214 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_197)) {
 x_215 = lean_alloc_ctor(0, 3, 0);
} else {
 x_215 = x_197;
}
lean_ctor_set(x_215, 0, x_194);
lean_ctor_set(x_215, 1, x_195);
lean_ctor_set(x_215, 2, x_214);
x_216 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_216, 0, x_189);
lean_ctor_set(x_216, 1, x_190);
lean_ctor_set(x_216, 2, x_215);
lean_ctor_set(x_216, 3, x_191);
lean_ctor_set(x_216, 4, x_192);
lean_ctor_set(x_216, 5, x_193);
lean_inc(x_1);
x_217 = l_Lean_Meta_getMVarTag(x_1, x_20, x_216);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = l_Lean_Meta_revert___closed__2;
lean_inc(x_1);
x_221 = l_Lean_Meta_checkNotAssigned(x_1, x_220, x_20, x_219);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
lean_dec(x_221);
x_223 = 0;
lean_inc(x_1);
x_224 = l_Lean_Meta_setMVarKind(x_1, x_223, x_20, x_222);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
x_226 = lean_unsigned_to_nat(0u);
x_227 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_226, x_2);
lean_inc(x_1);
x_228 = l_Lean_mkMVar(x_1);
x_229 = l_Lean_Meta_elimMVarDeps(x_227, x_228, x_3, x_20, x_225);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_10);
x_230 = lean_ctor_get(x_229, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_229, 1);
lean_inc(x_231);
lean_dec(x_229);
x_232 = 2;
x_233 = l_Lean_Meta_setMVarKind(x_1, x_232, x_20, x_231);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_235 = l_Lean_Expr_getAppNumArgsAux___main(x_230, x_226);
x_236 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_235);
x_237 = lean_mk_array(x_235, x_236);
x_238 = lean_unsigned_to_nat(1u);
x_239 = lean_nat_sub(x_235, x_238);
lean_dec(x_235);
x_240 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(x_218, x_230, x_237, x_239, x_20, x_234);
lean_dec(x_20);
x_241 = lean_ctor_get(x_240, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_241, 2);
lean_inc(x_242);
x_243 = lean_ctor_get(x_240, 0);
lean_inc(x_243);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_244 = x_240;
} else {
 lean_dec_ref(x_240);
 x_244 = lean_box(0);
}
x_245 = lean_ctor_get(x_241, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_241, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_241, 3);
lean_inc(x_247);
x_248 = lean_ctor_get(x_241, 4);
lean_inc(x_248);
x_249 = lean_ctor_get(x_241, 5);
lean_inc(x_249);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 lean_ctor_release(x_241, 2);
 lean_ctor_release(x_241, 3);
 lean_ctor_release(x_241, 4);
 lean_ctor_release(x_241, 5);
 x_250 = x_241;
} else {
 lean_dec_ref(x_241);
 x_250 = lean_box(0);
}
x_251 = lean_ctor_get(x_242, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_242, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 lean_ctor_release(x_242, 2);
 x_253 = x_242;
} else {
 lean_dec_ref(x_242);
 x_253 = lean_box(0);
}
if (lean_is_scalar(x_253)) {
 x_254 = lean_alloc_ctor(0, 3, 0);
} else {
 x_254 = x_253;
}
lean_ctor_set(x_254, 0, x_251);
lean_ctor_set(x_254, 1, x_252);
lean_ctor_set(x_254, 2, x_196);
if (lean_is_scalar(x_250)) {
 x_255 = lean_alloc_ctor(0, 6, 0);
} else {
 x_255 = x_250;
}
lean_ctor_set(x_255, 0, x_245);
lean_ctor_set(x_255, 1, x_246);
lean_ctor_set(x_255, 2, x_254);
lean_ctor_set(x_255, 3, x_247);
lean_ctor_set(x_255, 4, x_248);
lean_ctor_set(x_255, 5, x_249);
if (lean_is_scalar(x_244)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_244;
}
lean_ctor_set(x_256, 0, x_243);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
else
{
lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; 
lean_dec(x_218);
x_257 = lean_ctor_get(x_229, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_229, 1);
lean_inc(x_258);
lean_dec(x_229);
x_259 = 2;
x_260 = l_Lean_Meta_setMVarKind(x_1, x_259, x_20, x_258);
lean_dec(x_20);
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
lean_dec(x_260);
x_198 = x_257;
x_199 = x_261;
goto block_213;
}
}
else
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_218);
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_262 = lean_ctor_get(x_221, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_221, 1);
lean_inc(x_263);
lean_dec(x_221);
x_198 = x_262;
x_199 = x_263;
goto block_213;
}
}
else
{
lean_object* x_264; lean_object* x_265; 
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_264 = lean_ctor_get(x_217, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_217, 1);
lean_inc(x_265);
lean_dec(x_217);
x_198 = x_264;
x_199 = x_265;
goto block_213;
}
block_213:
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_200 = lean_ctor_get(x_199, 2);
lean_inc(x_200);
x_201 = lean_ctor_get(x_199, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_199, 1);
lean_inc(x_202);
x_203 = lean_ctor_get(x_199, 3);
lean_inc(x_203);
x_204 = lean_ctor_get(x_199, 4);
lean_inc(x_204);
x_205 = lean_ctor_get(x_199, 5);
lean_inc(x_205);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 lean_ctor_release(x_199, 2);
 lean_ctor_release(x_199, 3);
 lean_ctor_release(x_199, 4);
 lean_ctor_release(x_199, 5);
 x_206 = x_199;
} else {
 lean_dec_ref(x_199);
 x_206 = lean_box(0);
}
x_207 = lean_ctor_get(x_200, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_200, 1);
lean_inc(x_208);
if (lean_is_exclusive(x_200)) {
 lean_ctor_release(x_200, 0);
 lean_ctor_release(x_200, 1);
 lean_ctor_release(x_200, 2);
 x_209 = x_200;
} else {
 lean_dec_ref(x_200);
 x_209 = lean_box(0);
}
if (lean_is_scalar(x_209)) {
 x_210 = lean_alloc_ctor(0, 3, 0);
} else {
 x_210 = x_209;
}
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_208);
lean_ctor_set(x_210, 2, x_196);
if (lean_is_scalar(x_206)) {
 x_211 = lean_alloc_ctor(0, 6, 0);
} else {
 x_211 = x_206;
}
lean_ctor_set(x_211, 0, x_201);
lean_ctor_set(x_211, 1, x_202);
lean_ctor_set(x_211, 2, x_210);
lean_ctor_set(x_211, 3, x_203);
lean_ctor_set(x_211, 4, x_204);
lean_ctor_set(x_211, 5, x_205);
if (lean_is_scalar(x_10)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_10;
 lean_ctor_set_tag(x_212, 1);
}
lean_ctor_set(x_212, 0, x_198);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
}
else
{
uint8_t x_310; 
lean_dec(x_2);
lean_dec(x_1);
x_310 = !lean_is_exclusive(x_7);
if (x_310 == 0)
{
return x_7;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_7, 0);
x_312 = lean_ctor_get(x_7, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_7);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; 
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_2);
lean_ctor_set(x_314, 1, x_1);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_5);
return x_315;
}
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Array_isEqvAux___main___at_Lean_Meta_revert___spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Array_isEqvAux___main___at_Lean_Meta_revert___spec__4(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
lean_object* l_Lean_Meta_revert___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Meta_revert(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_4);
return x_7;
}
}
lean_object* initialize_Init_Lean_Meta_Tactic_Util(lean_object*);
static bool _G_initialized = false;
lean_object* initialize_Init_Lean_Meta_Tactic_Revert(lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_mk_io_result(lean_box(0));
_G_initialized = true;
res = initialize_Init_Lean_Meta_Tactic_Util(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_revert___closed__1 = _init_l_Lean_Meta_revert___closed__1();
lean_mark_persistent(l_Lean_Meta_revert___closed__1);
l_Lean_Meta_revert___closed__2 = _init_l_Lean_Meta_revert___closed__2();
lean_mark_persistent(l_Lean_Meta_revert___closed__2);
return lean_mk_io_result(lean_box(0));
}
#ifdef __cplusplus
}
#endif
