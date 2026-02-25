// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Main
// Imports: import Init.Grind.Propagator import Lean.Meta.Tactic.Grind.Arith.Cutsat.LeCnstr import Lean.Meta.Tactic.Grind.Arith.Linear.IneqCnstr public import Lean.Meta.Tactic.Grind.PropagatorAttr
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
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_propagateIneq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLE(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLE___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8__value;
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8____boxed(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLT___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value;
static const lean_string_object l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_ = (const lean_object*)&l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8__value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_();
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLE(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc_ref(x_1);
x_13 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_inc_ref(x_1);
x_16 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_20 = lean_box(0);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
uint8_t x_21; lean_object* x_22; 
lean_free_object(x_16);
x_21 = lean_unbox(x_14);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_22 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(x_1, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; lean_object* x_24; 
lean_dec_ref(x_22);
x_23 = lean_unbox(x_14);
lean_dec(x_14);
x_24 = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(x_1, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_24;
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_22;
}
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; 
x_29 = lean_unbox(x_14);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_30 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(x_1, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; lean_object* x_32; 
lean_dec_ref(x_30);
x_31 = lean_unbox(x_14);
lean_dec(x_14);
x_32 = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(x_1, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_32;
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_30;
}
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_16, 0);
lean_inc(x_34);
lean_dec(x_16);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; lean_object* x_37; 
x_36 = lean_unbox(x_14);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_37 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLe(x_1, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; lean_object* x_39; 
lean_dec_ref(x_37);
x_38 = lean_unbox(x_14);
lean_dec(x_14);
x_39 = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(x_1, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_39;
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_37;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
return x_13;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_13, 0);
lean_inc(x_41);
lean_dec(x_13);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLE___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_propagateLE(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateLE___boxed), 12, 0);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLT(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
lean_inc_ref(x_1);
x_13 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
x_15 = lean_unbox(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_inc_ref(x_1);
x_16 = l_Lean_Meta_Grind_isEqFalse___redArg(x_1, x_2, x_6, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_20 = lean_box(0);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
uint8_t x_21; lean_object* x_22; 
lean_free_object(x_16);
x_21 = lean_unbox(x_14);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_22 = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(x_1, x_21, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; lean_object* x_24; 
lean_dec_ref(x_22);
x_23 = lean_unbox(x_14);
lean_dec(x_14);
x_24 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(x_1, x_23, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_24;
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_22;
}
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
else
{
uint8_t x_29; lean_object* x_30; 
x_29 = lean_unbox(x_14);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_30 = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(x_1, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_30) == 0)
{
uint8_t x_31; lean_object* x_32; 
lean_dec_ref(x_30);
x_31 = lean_unbox(x_14);
lean_dec(x_14);
x_32 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(x_1, x_31, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_32;
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_30;
}
}
}
}
else
{
uint8_t x_33; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_16, 0);
lean_inc(x_34);
lean_dec(x_16);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; lean_object* x_37; 
x_36 = lean_unbox(x_14);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc_ref(x_1);
x_37 = l_Lean_Meta_Grind_Arith_Linear_propagateIneq(x_1, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; lean_object* x_39; 
lean_dec_ref(x_37);
x_38 = lean_unbox(x_14);
lean_dec(x_14);
x_39 = l_Lean_Meta_Grind_Arith_Cutsat_propagateLt(x_1, x_38, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_39;
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_37;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
return x_13;
}
else
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_13, 0);
lean_inc(x_41);
lean_dec(x_13);
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLT___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_propagateLT(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1___closed__2_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_));
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_propagateLT___boxed), 12, 0);
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
lean_object* initialize_Init_Grind_Propagator(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Main(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Propagator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_LeCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_IneqCnstr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Meta_Grind_Arith_propagateLE___regBuiltin_Lean_Meta_Grind_Arith_propagateLE_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_2242026828____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_Grind_Arith_propagateLT___regBuiltin_Lean_Meta_Grind_Arith_propagateLT_declare__1_00___x40_Lean_Meta_Tactic_Grind_Arith_Main_831638839____hygCtx___hyg_8_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
