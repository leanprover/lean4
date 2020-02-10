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
lean_object* l_Lean_Meta_revert___closed__1;
uint8_t l_Array_isEmpty___rarg(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVarDecl(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_LocalInstance_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_object* l_unsafeCast(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEqvAux___main___at_Lean_Meta_revert___spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_array_set(x_2, x_3, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_3, x_7);
lean_dec(x_3);
x_1 = x_4;
x_2 = x_6;
x_3 = x_8;
goto _start;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__2(x_10, x_2);
x_12 = l_Lean_Expr_mvarId_x21(x_1);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
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
lean_object* x_254; 
lean_dec(x_16);
lean_dec(x_8);
x_254 = lean_box(0);
x_21 = x_254;
goto block_253;
}
else
{
lean_object* x_255; uint8_t x_256; 
x_255 = lean_unsigned_to_nat(0u);
x_256 = l_Array_isEqvAux___main___at_Lean_Meta_revert___spec__4(x_4, x_8, lean_box(0), x_12, x_16, x_255);
lean_dec(x_16);
lean_dec(x_8);
if (x_256 == 0)
{
lean_object* x_257; 
x_257 = lean_box(0);
x_21 = x_257;
goto block_253;
}
else
{
lean_object* x_258; lean_object* x_259; 
lean_dec(x_10);
x_258 = l_Lean_Meta_revert___closed__2;
lean_inc(x_1);
x_259 = l_Lean_Meta_checkNotAssigned(x_1, x_258, x_20, x_9);
if (lean_obj_tag(x_259) == 0)
{
lean_object* x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
lean_dec(x_259);
x_261 = 0;
lean_inc(x_1);
x_262 = l_Lean_Meta_setMVarKind(x_1, x_261, x_20, x_260);
x_263 = lean_ctor_get(x_262, 1);
lean_inc(x_263);
lean_dec(x_262);
x_264 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_255, x_2);
lean_inc(x_1);
x_265 = l_Lean_mkMVar(x_1);
x_266 = l_Lean_Meta_elimMVarDeps(x_264, x_265, x_3, x_20, x_263);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; uint8_t x_269; lean_object* x_270; uint8_t x_271; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = 2;
x_270 = l_Lean_Meta_setMVarKind(x_1, x_269, x_20, x_268);
lean_dec(x_20);
x_271 = !lean_is_exclusive(x_270);
if (x_271 == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_272 = lean_ctor_get(x_270, 0);
lean_dec(x_272);
x_273 = l_Lean_Expr_getAppNumArgsAux___main(x_267, x_255);
x_274 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_273);
x_275 = lean_mk_array(x_273, x_274);
x_276 = lean_unsigned_to_nat(1u);
x_277 = lean_nat_sub(x_273, x_276);
lean_dec(x_273);
x_278 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(x_267, x_275, x_277);
lean_ctor_set(x_270, 0, x_278);
return x_270;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_279 = lean_ctor_get(x_270, 1);
lean_inc(x_279);
lean_dec(x_270);
x_280 = l_Lean_Expr_getAppNumArgsAux___main(x_267, x_255);
x_281 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_280);
x_282 = lean_mk_array(x_280, x_281);
x_283 = lean_unsigned_to_nat(1u);
x_284 = lean_nat_sub(x_280, x_283);
lean_dec(x_280);
x_285 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(x_267, x_282, x_284);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_279);
return x_286;
}
}
else
{
lean_object* x_287; lean_object* x_288; uint8_t x_289; lean_object* x_290; uint8_t x_291; 
x_287 = lean_ctor_get(x_266, 0);
lean_inc(x_287);
x_288 = lean_ctor_get(x_266, 1);
lean_inc(x_288);
lean_dec(x_266);
x_289 = 2;
x_290 = l_Lean_Meta_setMVarKind(x_1, x_289, x_20, x_288);
lean_dec(x_20);
x_291 = !lean_is_exclusive(x_290);
if (x_291 == 0)
{
lean_object* x_292; 
x_292 = lean_ctor_get(x_290, 0);
lean_dec(x_292);
lean_ctor_set_tag(x_290, 1);
lean_ctor_set(x_290, 0, x_287);
return x_290;
}
else
{
lean_object* x_293; lean_object* x_294; 
x_293 = lean_ctor_get(x_290, 1);
lean_inc(x_293);
lean_dec(x_290);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_287);
lean_ctor_set(x_294, 1, x_293);
return x_294;
}
}
}
else
{
uint8_t x_295; 
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_295 = !lean_is_exclusive(x_259);
if (x_295 == 0)
{
return x_259;
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_259, 0);
x_297 = lean_ctor_get(x_259, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_259);
x_298 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_297);
return x_298;
}
}
}
}
block_253:
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
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_25 = lean_ctor_get(x_23, 2);
x_50 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
lean_ctor_set(x_23, 2, x_50);
x_51 = l_Lean_Meta_revert___closed__2;
lean_inc(x_1);
x_52 = l_Lean_Meta_checkNotAssigned(x_1, x_51, x_20, x_9);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = 0;
lean_inc(x_1);
x_55 = l_Lean_Meta_setMVarKind(x_1, x_54, x_20, x_53);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_unsigned_to_nat(0u);
x_58 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_57, x_2);
lean_inc(x_1);
x_59 = l_Lean_mkMVar(x_1);
x_60 = l_Lean_Meta_elimMVarDeps(x_58, x_59, x_3, x_20, x_56);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_10);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = 2;
x_64 = l_Lean_Meta_setMVarKind(x_1, x_63, x_20, x_62);
lean_dec(x_20);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_66 = lean_ctor_get(x_64, 1);
x_67 = lean_ctor_get(x_64, 0);
lean_dec(x_67);
x_68 = l_Lean_Expr_getAppNumArgsAux___main(x_61, x_57);
x_69 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_68);
x_70 = lean_mk_array(x_68, x_69);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_sub(x_68, x_71);
lean_dec(x_68);
x_73 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(x_61, x_70, x_72);
x_74 = !lean_is_exclusive(x_66);
if (x_74 == 0)
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_66, 2);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 2);
lean_dec(x_77);
lean_ctor_set(x_75, 2, x_25);
lean_ctor_set(x_64, 0, x_73);
return x_64;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_75, 0);
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_75);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
lean_ctor_set(x_80, 2, x_25);
lean_ctor_set(x_66, 2, x_80);
lean_ctor_set(x_64, 0, x_73);
return x_64;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_81 = lean_ctor_get(x_66, 2);
x_82 = lean_ctor_get(x_66, 0);
x_83 = lean_ctor_get(x_66, 1);
x_84 = lean_ctor_get(x_66, 3);
x_85 = lean_ctor_get(x_66, 4);
x_86 = lean_ctor_get(x_66, 5);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_81);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_66);
x_87 = lean_ctor_get(x_81, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 lean_ctor_release(x_81, 2);
 x_89 = x_81;
} else {
 lean_dec_ref(x_81);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(0, 3, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
lean_ctor_set(x_90, 2, x_25);
x_91 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_91, 0, x_82);
lean_ctor_set(x_91, 1, x_83);
lean_ctor_set(x_91, 2, x_90);
lean_ctor_set(x_91, 3, x_84);
lean_ctor_set(x_91, 4, x_85);
lean_ctor_set(x_91, 5, x_86);
lean_ctor_set(x_64, 1, x_91);
lean_ctor_set(x_64, 0, x_73);
return x_64;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_92 = lean_ctor_get(x_64, 1);
lean_inc(x_92);
lean_dec(x_64);
x_93 = l_Lean_Expr_getAppNumArgsAux___main(x_61, x_57);
x_94 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_93);
x_95 = lean_mk_array(x_93, x_94);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_sub(x_93, x_96);
lean_dec(x_93);
x_98 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(x_61, x_95, x_97);
x_99 = lean_ctor_get(x_92, 2);
lean_inc(x_99);
x_100 = lean_ctor_get(x_92, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_92, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_92, 3);
lean_inc(x_102);
x_103 = lean_ctor_get(x_92, 4);
lean_inc(x_103);
x_104 = lean_ctor_get(x_92, 5);
lean_inc(x_104);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 lean_ctor_release(x_92, 2);
 lean_ctor_release(x_92, 3);
 lean_ctor_release(x_92, 4);
 lean_ctor_release(x_92, 5);
 x_105 = x_92;
} else {
 lean_dec_ref(x_92);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_99, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_99, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 lean_ctor_release(x_99, 2);
 x_108 = x_99;
} else {
 lean_dec_ref(x_99);
 x_108 = lean_box(0);
}
if (lean_is_scalar(x_108)) {
 x_109 = lean_alloc_ctor(0, 3, 0);
} else {
 x_109 = x_108;
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_107);
lean_ctor_set(x_109, 2, x_25);
if (lean_is_scalar(x_105)) {
 x_110 = lean_alloc_ctor(0, 6, 0);
} else {
 x_110 = x_105;
}
lean_ctor_set(x_110, 0, x_100);
lean_ctor_set(x_110, 1, x_101);
lean_ctor_set(x_110, 2, x_109);
lean_ctor_set(x_110, 3, x_102);
lean_ctor_set(x_110, 4, x_103);
lean_ctor_set(x_110, 5, x_104);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_98);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
else
{
lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; lean_object* x_116; 
x_112 = lean_ctor_get(x_60, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_60, 1);
lean_inc(x_113);
lean_dec(x_60);
x_114 = 2;
x_115 = l_Lean_Meta_setMVarKind(x_1, x_114, x_20, x_113);
lean_dec(x_20);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
lean_dec(x_115);
x_26 = x_112;
x_27 = x_116;
goto block_49;
}
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_117 = lean_ctor_get(x_52, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_52, 1);
lean_inc(x_118);
lean_dec(x_52);
x_26 = x_117;
x_27 = x_118;
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
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_119 = lean_ctor_get(x_23, 0);
x_120 = lean_ctor_get(x_23, 1);
x_121 = lean_ctor_get(x_23, 2);
lean_inc(x_121);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_23);
x_138 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
x_139 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_139, 0, x_119);
lean_ctor_set(x_139, 1, x_120);
lean_ctor_set(x_139, 2, x_138);
lean_ctor_set(x_9, 2, x_139);
x_140 = l_Lean_Meta_revert___closed__2;
lean_inc(x_1);
x_141 = l_Lean_Meta_checkNotAssigned(x_1, x_140, x_20, x_9);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
x_143 = 0;
lean_inc(x_1);
x_144 = l_Lean_Meta_setMVarKind(x_1, x_143, x_20, x_142);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
lean_dec(x_144);
x_146 = lean_unsigned_to_nat(0u);
x_147 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_146, x_2);
lean_inc(x_1);
x_148 = l_Lean_mkMVar(x_1);
x_149 = l_Lean_Meta_elimMVarDeps(x_147, x_148, x_3, x_20, x_145);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_10);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = 2;
x_153 = l_Lean_Meta_setMVarKind(x_1, x_152, x_20, x_151);
lean_dec(x_20);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
x_156 = l_Lean_Expr_getAppNumArgsAux___main(x_150, x_146);
x_157 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_156);
x_158 = lean_mk_array(x_156, x_157);
x_159 = lean_unsigned_to_nat(1u);
x_160 = lean_nat_sub(x_156, x_159);
lean_dec(x_156);
x_161 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(x_150, x_158, x_160);
x_162 = lean_ctor_get(x_154, 2);
lean_inc(x_162);
x_163 = lean_ctor_get(x_154, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_154, 1);
lean_inc(x_164);
x_165 = lean_ctor_get(x_154, 3);
lean_inc(x_165);
x_166 = lean_ctor_get(x_154, 4);
lean_inc(x_166);
x_167 = lean_ctor_get(x_154, 5);
lean_inc(x_167);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 lean_ctor_release(x_154, 2);
 lean_ctor_release(x_154, 3);
 lean_ctor_release(x_154, 4);
 lean_ctor_release(x_154, 5);
 x_168 = x_154;
} else {
 lean_dec_ref(x_154);
 x_168 = lean_box(0);
}
x_169 = lean_ctor_get(x_162, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_162, 1);
lean_inc(x_170);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 lean_ctor_release(x_162, 2);
 x_171 = x_162;
} else {
 lean_dec_ref(x_162);
 x_171 = lean_box(0);
}
if (lean_is_scalar(x_171)) {
 x_172 = lean_alloc_ctor(0, 3, 0);
} else {
 x_172 = x_171;
}
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
lean_ctor_set(x_172, 2, x_121);
if (lean_is_scalar(x_168)) {
 x_173 = lean_alloc_ctor(0, 6, 0);
} else {
 x_173 = x_168;
}
lean_ctor_set(x_173, 0, x_163);
lean_ctor_set(x_173, 1, x_164);
lean_ctor_set(x_173, 2, x_172);
lean_ctor_set(x_173, 3, x_165);
lean_ctor_set(x_173, 4, x_166);
lean_ctor_set(x_173, 5, x_167);
if (lean_is_scalar(x_155)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_155;
}
lean_ctor_set(x_174, 0, x_161);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; 
x_175 = lean_ctor_get(x_149, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_149, 1);
lean_inc(x_176);
lean_dec(x_149);
x_177 = 2;
x_178 = l_Lean_Meta_setMVarKind(x_1, x_177, x_20, x_176);
lean_dec(x_20);
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
lean_dec(x_178);
x_122 = x_175;
x_123 = x_179;
goto block_137;
}
}
else
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_180 = lean_ctor_get(x_141, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_141, 1);
lean_inc(x_181);
lean_dec(x_141);
x_122 = x_180;
x_123 = x_181;
goto block_137;
}
block_137:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_124 = lean_ctor_get(x_123, 2);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_123, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 3);
lean_inc(x_127);
x_128 = lean_ctor_get(x_123, 4);
lean_inc(x_128);
x_129 = lean_ctor_get(x_123, 5);
lean_inc(x_129);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 lean_ctor_release(x_123, 2);
 lean_ctor_release(x_123, 3);
 lean_ctor_release(x_123, 4);
 lean_ctor_release(x_123, 5);
 x_130 = x_123;
} else {
 lean_dec_ref(x_123);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_124, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_124, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 lean_ctor_release(x_124, 2);
 x_133 = x_124;
} else {
 lean_dec_ref(x_124);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(0, 3, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
lean_ctor_set(x_134, 2, x_121);
if (lean_is_scalar(x_130)) {
 x_135 = lean_alloc_ctor(0, 6, 0);
} else {
 x_135 = x_130;
}
lean_ctor_set(x_135, 0, x_125);
lean_ctor_set(x_135, 1, x_126);
lean_ctor_set(x_135, 2, x_134);
lean_ctor_set(x_135, 3, x_127);
lean_ctor_set(x_135, 4, x_128);
lean_ctor_set(x_135, 5, x_129);
if (lean_is_scalar(x_10)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_10;
 lean_ctor_set_tag(x_136, 1);
}
lean_ctor_set(x_136, 0, x_122);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_182 = lean_ctor_get(x_9, 2);
x_183 = lean_ctor_get(x_9, 0);
x_184 = lean_ctor_get(x_9, 1);
x_185 = lean_ctor_get(x_9, 3);
x_186 = lean_ctor_get(x_9, 4);
x_187 = lean_ctor_get(x_9, 5);
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_182);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_9);
x_188 = lean_ctor_get(x_182, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_182, 1);
lean_inc(x_189);
x_190 = lean_ctor_get(x_182, 2);
lean_inc(x_190);
if (lean_is_exclusive(x_182)) {
 lean_ctor_release(x_182, 0);
 lean_ctor_release(x_182, 1);
 lean_ctor_release(x_182, 2);
 x_191 = x_182;
} else {
 lean_dec_ref(x_182);
 x_191 = lean_box(0);
}
x_208 = l_Lean_Meta_resettingSynthInstanceCache___rarg___closed__1;
if (lean_is_scalar(x_191)) {
 x_209 = lean_alloc_ctor(0, 3, 0);
} else {
 x_209 = x_191;
}
lean_ctor_set(x_209, 0, x_188);
lean_ctor_set(x_209, 1, x_189);
lean_ctor_set(x_209, 2, x_208);
x_210 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_210, 0, x_183);
lean_ctor_set(x_210, 1, x_184);
lean_ctor_set(x_210, 2, x_209);
lean_ctor_set(x_210, 3, x_185);
lean_ctor_set(x_210, 4, x_186);
lean_ctor_set(x_210, 5, x_187);
x_211 = l_Lean_Meta_revert___closed__2;
lean_inc(x_1);
x_212 = l_Lean_Meta_checkNotAssigned(x_1, x_211, x_20, x_210);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
x_214 = 0;
lean_inc(x_1);
x_215 = l_Lean_Meta_setMVarKind(x_1, x_214, x_20, x_213);
x_216 = lean_ctor_get(x_215, 1);
lean_inc(x_216);
lean_dec(x_215);
x_217 = lean_unsigned_to_nat(0u);
x_218 = l_Array_umapMAux___main___at_Lean_Meta_revert___spec__1(x_217, x_2);
lean_inc(x_1);
x_219 = l_Lean_mkMVar(x_1);
x_220 = l_Lean_Meta_elimMVarDeps(x_218, x_219, x_3, x_20, x_216);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_10);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = 2;
x_224 = l_Lean_Meta_setMVarKind(x_1, x_223, x_20, x_222);
lean_dec(x_20);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_226 = x_224;
} else {
 lean_dec_ref(x_224);
 x_226 = lean_box(0);
}
x_227 = l_Lean_Expr_getAppNumArgsAux___main(x_221, x_217);
x_228 = l_Lean_Expr_getAppArgs___closed__1;
lean_inc(x_227);
x_229 = lean_mk_array(x_227, x_228);
x_230 = lean_unsigned_to_nat(1u);
x_231 = lean_nat_sub(x_227, x_230);
lean_dec(x_227);
x_232 = l_Lean_Expr_withAppAux___main___at_Lean_Meta_revert___spec__3(x_221, x_229, x_231);
x_233 = lean_ctor_get(x_225, 2);
lean_inc(x_233);
x_234 = lean_ctor_get(x_225, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_225, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_225, 3);
lean_inc(x_236);
x_237 = lean_ctor_get(x_225, 4);
lean_inc(x_237);
x_238 = lean_ctor_get(x_225, 5);
lean_inc(x_238);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 lean_ctor_release(x_225, 2);
 lean_ctor_release(x_225, 3);
 lean_ctor_release(x_225, 4);
 lean_ctor_release(x_225, 5);
 x_239 = x_225;
} else {
 lean_dec_ref(x_225);
 x_239 = lean_box(0);
}
x_240 = lean_ctor_get(x_233, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_233, 1);
lean_inc(x_241);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 lean_ctor_release(x_233, 2);
 x_242 = x_233;
} else {
 lean_dec_ref(x_233);
 x_242 = lean_box(0);
}
if (lean_is_scalar(x_242)) {
 x_243 = lean_alloc_ctor(0, 3, 0);
} else {
 x_243 = x_242;
}
lean_ctor_set(x_243, 0, x_240);
lean_ctor_set(x_243, 1, x_241);
lean_ctor_set(x_243, 2, x_190);
if (lean_is_scalar(x_239)) {
 x_244 = lean_alloc_ctor(0, 6, 0);
} else {
 x_244 = x_239;
}
lean_ctor_set(x_244, 0, x_234);
lean_ctor_set(x_244, 1, x_235);
lean_ctor_set(x_244, 2, x_243);
lean_ctor_set(x_244, 3, x_236);
lean_ctor_set(x_244, 4, x_237);
lean_ctor_set(x_244, 5, x_238);
if (lean_is_scalar(x_226)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_226;
}
lean_ctor_set(x_245, 0, x_232);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
else
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; 
x_246 = lean_ctor_get(x_220, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_220, 1);
lean_inc(x_247);
lean_dec(x_220);
x_248 = 2;
x_249 = l_Lean_Meta_setMVarKind(x_1, x_248, x_20, x_247);
lean_dec(x_20);
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
lean_dec(x_249);
x_192 = x_246;
x_193 = x_250;
goto block_207;
}
}
else
{
lean_object* x_251; lean_object* x_252; 
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
x_251 = lean_ctor_get(x_212, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_212, 1);
lean_inc(x_252);
lean_dec(x_212);
x_192 = x_251;
x_193 = x_252;
goto block_207;
}
block_207:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_194 = lean_ctor_get(x_193, 2);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
x_197 = lean_ctor_get(x_193, 3);
lean_inc(x_197);
x_198 = lean_ctor_get(x_193, 4);
lean_inc(x_198);
x_199 = lean_ctor_get(x_193, 5);
lean_inc(x_199);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 lean_ctor_release(x_193, 2);
 lean_ctor_release(x_193, 3);
 lean_ctor_release(x_193, 4);
 lean_ctor_release(x_193, 5);
 x_200 = x_193;
} else {
 lean_dec_ref(x_193);
 x_200 = lean_box(0);
}
x_201 = lean_ctor_get(x_194, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_194, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_194)) {
 lean_ctor_release(x_194, 0);
 lean_ctor_release(x_194, 1);
 lean_ctor_release(x_194, 2);
 x_203 = x_194;
} else {
 lean_dec_ref(x_194);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(0, 3, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
lean_ctor_set(x_204, 2, x_190);
if (lean_is_scalar(x_200)) {
 x_205 = lean_alloc_ctor(0, 6, 0);
} else {
 x_205 = x_200;
}
lean_ctor_set(x_205, 0, x_195);
lean_ctor_set(x_205, 1, x_196);
lean_ctor_set(x_205, 2, x_204);
lean_ctor_set(x_205, 3, x_197);
lean_ctor_set(x_205, 4, x_198);
lean_ctor_set(x_205, 5, x_199);
if (lean_is_scalar(x_10)) {
 x_206 = lean_alloc_ctor(1, 2, 0);
} else {
 x_206 = x_10;
 lean_ctor_set_tag(x_206, 1);
}
lean_ctor_set(x_206, 0, x_192);
lean_ctor_set(x_206, 1, x_205);
return x_206;
}
}
}
}
else
{
uint8_t x_299; 
lean_dec(x_2);
lean_dec(x_1);
x_299 = !lean_is_exclusive(x_7);
if (x_299 == 0)
{
return x_7;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_300 = lean_ctor_get(x_7, 0);
x_301 = lean_ctor_get(x_7, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_7);
x_302 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_302, 0, x_300);
lean_ctor_set(x_302, 1, x_301);
return x_302;
}
}
}
else
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_2);
lean_ctor_set(x_303, 1, x_1);
x_304 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_304, 0, x_303);
lean_ctor_set(x_304, 1, x_5);
return x_304;
}
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
