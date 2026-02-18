// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.IsRelevant
// Imports: public import Lean.Meta.Tactic.Grind.Types import Lean.Meta.Tactic.Grind.Arith.Cutsat.ToInt import Lean.Meta.Tactic.Grind.Arith.Linear.StructId
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
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isNatType(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_isIntType(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isSupportedType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isSupportedType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Not"};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 11, 203, 55, 27, 192, 137, 230)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__2_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dvd"};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 71, 229, 107, 63, 192, 93, 62)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__5_value),LEAN_SCALAR_PTR_LITERAL(233, 16, 181, 127, 123, 63, 3, 18)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LT"};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "lt"};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__7_value),LEAN_SCALAR_PTR_LITERAL(71, 235, 154, 184, 62, 135, 30, 248)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__8_value),LEAN_SCALAR_PTR_LITERAL(54, 235, 251, 9, 4, 74, 57, 164)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "LE"};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "le"};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__11_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__10_value),LEAN_SCALAR_PTR_LITERAL(216, 149, 183, 186, 191, 145, 216, 115)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__11_value),LEAN_SCALAR_PTR_LITERAL(109, 14, 90, 172, 72, 170, 136, 101)}};
static const lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12_value;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isSupportedType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; uint8_t x_51; 
x_51 = l_Lean_Meta_Grind_Arith_isNatType(x_1);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = l_Lean_Meta_Grind_Arith_isIntType(x_1);
x_13 = x_52;
goto block_50;
}
else
{
x_13 = x_51;
goto block_50;
}
block_50:
{
uint8_t x_14; 
x_14 = 1;
if (x_13 == 0)
{
lean_object* x_15; 
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
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_getToIntId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
lean_free_object(x_15);
x_18 = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_box(x_13);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; 
lean_dec_ref(x_20);
x_22 = lean_box(x_14);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(x_13);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec_ref(x_23);
x_26 = lean_box(x_14);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_18, 0);
lean_inc(x_29);
lean_dec(x_18);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; 
lean_dec_ref(x_17);
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
x_31 = lean_box(x_14);
lean_ctor_set(x_15, 0, x_31);
return x_15;
}
}
else
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_15, 0);
lean_inc(x_32);
lean_dec(x_15);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
x_33 = l_Lean_Meta_Grind_Arith_Linear_getStructId_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_35 = x_33;
} else {
 lean_dec_ref(x_33);
 x_35 = lean_box(0);
}
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_box(x_13);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 1, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_34);
x_38 = lean_box(x_14);
if (lean_is_scalar(x_35)) {
 x_39 = lean_alloc_ctor(0, 1, 0);
} else {
 x_39 = x_35;
}
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_33, 0);
lean_inc(x_40);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 x_41 = x_33;
} else {
 lean_dec_ref(x_33);
 x_41 = lean_box(0);
}
if (lean_is_scalar(x_41)) {
 x_42 = lean_alloc_ctor(1, 1, 0);
} else {
 x_42 = x_41;
}
lean_ctor_set(x_42, 0, x_40);
return x_42;
}
}
else
{
lean_object* x_43; lean_object* x_44; 
lean_dec_ref(x_32);
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
x_43 = lean_box(x_14);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
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
x_45 = !lean_is_exclusive(x_15);
if (x_45 == 0)
{
return x_15;
}
else
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_15, 0);
lean_inc(x_46);
lean_dec(x_15);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
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
x_48 = lean_box(x_14);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isSupportedType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_isSupportedType(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Expr_cleanupAnnotations(x_1);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec_ref(x_18);
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
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_20);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_22 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__1));
x_23 = l_Lean_Expr_isConstOf(x_21, x_22);
if (x_23 == 0)
{
uint8_t x_24; 
lean_dec_ref(x_20);
x_24 = l_Lean_Expr_isApp(x_21);
if (x_24 == 0)
{
lean_dec_ref(x_21);
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
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_26 = l_Lean_Expr_isApp(x_25);
if (x_26 == 0)
{
lean_dec_ref(x_25);
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
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_25);
x_29 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__3));
x_30 = l_Lean_Expr_isConstOf(x_28, x_29);
if (x_30 == 0)
{
uint8_t x_31; 
lean_dec_ref(x_27);
x_31 = l_Lean_Expr_isApp(x_28);
if (x_31 == 0)
{
lean_dec_ref(x_28);
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
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_32);
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_34 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__6));
x_35 = l_Lean_Expr_isConstOf(x_33, x_34);
if (x_35 == 0)
{
lean_object* x_36; uint8_t x_37; 
x_36 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__9));
x_37 = l_Lean_Expr_isConstOf(x_33, x_36);
if (x_37 == 0)
{
lean_object* x_38; uint8_t x_39; 
x_38 = ((lean_object*)(l_Lean_Meta_Grind_Arith_isRelevantPred___closed__12));
x_39 = l_Lean_Expr_isConstOf(x_33, x_38);
lean_dec_ref(x_33);
if (x_39 == 0)
{
lean_dec_ref(x_32);
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
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_object* x_40; 
x_40 = l_Lean_Meta_Grind_Arith_isSupportedType(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_40;
}
}
else
{
lean_object* x_41; 
lean_dec_ref(x_33);
x_41 = l_Lean_Meta_Grind_Arith_isSupportedType(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_41;
}
}
else
{
lean_object* x_42; 
lean_dec_ref(x_33);
x_42 = l_Lean_Meta_Grind_Arith_isSupportedType(x_32, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_42;
}
}
}
else
{
lean_object* x_43; 
lean_dec_ref(x_28);
x_43 = l_Lean_Meta_Grind_Arith_isSupportedType(x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_43;
}
}
}
}
else
{
lean_dec_ref(x_21);
x_1 = x_20;
goto _start;
}
}
block_17:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = 0;
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_Arith_isRelevantPred(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_IsRelevant(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToInt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_StructId(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
