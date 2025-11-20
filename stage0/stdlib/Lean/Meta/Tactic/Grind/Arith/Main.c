// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Main
// Imports: public import Lean.Meta.Tactic.Grind.Types import Init.Grind.Propagator import Lean.Meta.Tactic.Grind.PropagatorAttr import Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr import Lean.Meta.Tactic.Grind.Arith.Cutsat.Search import Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr import Lean.Meta.Tactic.Grind.Arith.Linear.Search
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_();
static lean_object* l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_;
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_();
lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_;
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8____boxed(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_;
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_;
static lean_object* l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc_ref(x_1);
x_11 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc_ref(x_1);
x_14 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_18 = lean_box(0);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
uint8_t x_19; lean_object* x_20; 
lean_free_object(x_14);
x_19 = lean_unbox(x_12);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_20 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(x_1, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; lean_object* x_22; 
lean_dec_ref(x_20);
x_21 = lean_unbox(x_12);
lean_dec(x_12);
x_22 = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(x_1, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_22;
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_20;
}
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
uint8_t x_27; lean_object* x_28; 
x_27 = lean_unbox(x_12);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_28 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(x_1, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; lean_object* x_30; 
lean_dec_ref(x_28);
x_29 = lean_unbox(x_12);
lean_dec(x_12);
x_30 = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(x_1, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_30;
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_28;
}
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
return x_14;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_14, 0);
lean_inc(x_32);
lean_dec(x_14);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; lean_object* x_35; 
x_34 = lean_unbox(x_12);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_35 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(x_1, x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; lean_object* x_37; 
lean_dec_ref(x_35);
x_36 = lean_unbox(x_12);
lean_dec(x_12);
x_37 = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(x_1, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_37;
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_35;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_38 = !lean_is_exclusive(x_11);
if (x_38 == 0)
{
return x_11;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_11, 0);
lean_inc(x_39);
lean_dec(x_11);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_propagateLE(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LE", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("le", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_;
x_2 = l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateLE___boxed), 10, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc_ref(x_1);
x_11 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_unbox(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc_ref(x_1);
x_14 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_4, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_18 = lean_box(0);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
uint8_t x_19; lean_object* x_20; 
lean_free_object(x_14);
x_19 = lean_unbox(x_12);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_20 = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(x_1, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; lean_object* x_22; 
lean_dec_ref(x_20);
x_21 = lean_unbox(x_12);
lean_dec(x_12);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(x_1, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_22;
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_20;
}
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_14, 0);
lean_inc(x_23);
lean_dec(x_14);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
uint8_t x_27; lean_object* x_28; 
x_27 = lean_unbox(x_12);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_28 = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(x_1, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_28) == 0)
{
uint8_t x_29; lean_object* x_30; 
lean_dec_ref(x_28);
x_29 = lean_unbox(x_12);
lean_dec(x_12);
x_30 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(x_1, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_30;
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_28;
}
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_31 = !lean_is_exclusive(x_14);
if (x_31 == 0)
{
return x_14;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_14, 0);
lean_inc(x_32);
lean_dec(x_14);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; lean_object* x_35; 
x_34 = lean_unbox(x_12);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_35 = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(x_1, x_34, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_35) == 0)
{
uint8_t x_36; lean_object* x_37; 
lean_dec_ref(x_35);
x_36 = lean_unbox(x_12);
lean_dec(x_12);
x_37 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(x_1, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_37;
}
else
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_35;
}
}
}
else
{
uint8_t x_38; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_38 = !lean_is_exclusive(x_11);
if (x_38 == 0)
{
return x_11;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_11, 0);
lean_inc(x_39);
lean_dec(x_11);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_propagateLT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("LT", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("lt", 2, 2);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_;
x_2 = l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_;
x_3 = l_Lean_Name_mkStr2(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_;
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateLT___boxed), 10, 0);
x_4 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_();
return x_2;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Search(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Search(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_ = _init_l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_);
l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_ = _init_l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_);
l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_ = _init_l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_);
if (builtin) {res = l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_ = _init_l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_);
l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_ = _init_l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_);
l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_ = _init_l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_);
if (builtin) {res = l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
