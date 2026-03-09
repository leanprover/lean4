// Lean compiler output
// Module: Lean.Meta.Sym.LitValues
// Imports: public import Lean.Expr public import Init.Data.Rat
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
static const lean_string_object l_Lean_Meta_Sym_getNatValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_Meta_Sym_getNatValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Sym_getNatValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_Meta_Sym_getNatValue_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__2_value;
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Sym_getIntValue_x3f_spec__0(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getIntValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Sym_getIntValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getIntValue_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_getIntValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Sym_getIntValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getIntValue_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getIntValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getIntValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Sym_getIntValue_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_getIntValue_x3f___closed__2_value;
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntValue_x3f(lean_object*);
lean_object* l_Rat_ofInt(lean_object*);
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__1(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getRatValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l_Lean_Meta_Sym_getRatValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getRatValue_x3f___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_getRatValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l_Lean_Meta_Sym_getRatValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getRatValue_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getRatValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getRatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l_Lean_Meta_Sym_getRatValue_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_getRatValue_x3f___closed__2_value;
lean_object* l_Rat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getRatValue_x3f(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "ofNatLT"};
static const lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 44, 243, 4, 118, 78, 150, 28)}};
static const lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4_value;
lean_object* l_BitVec_ofNat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt8Value_x3f(lean_object*);
uint16_t lean_uint16_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt32Value_x3f(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f(lean_object*);
uint8_t lean_int8_of_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt8Value_x3f(lean_object*);
uint16_t lean_int16_of_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt16Value_x3f(lean_object*);
uint32_t lean_int32_of_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt32Value_x3f(lean_object*);
uint64_t lean_int64_of_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt64Value_x3f(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getFinValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l_Lean_Meta_Sym_getFinValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getFinValue_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_getFinValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getFinValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_object* l_Lean_Meta_Sym_getFinValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getFinValue_x3f___closed__1_value;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFinValue_x3f(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_getCharValue_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l_Lean_Meta_Sym_getCharValue_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_getCharValue_x3f___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_getCharValue_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_getNatValue_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l_Lean_Meta_Sym_getCharValue_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_getCharValue_x3f___closed__1_value;
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCharValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getStringValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_5);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_8);
x_9 = l_Lean_Expr_appFnCleanup___redArg(x_5);
x_10 = l_Lean_Expr_isApp(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = l_Lean_Expr_appFnCleanup___redArg(x_9);
x_13 = ((lean_object*)(l_Lean_Meta_Sym_getNatValue_x3f___closed__2));
x_14 = l_Lean_Expr_isConstOf(x_12, x_13);
lean_dec_ref(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec_ref(x_8);
x_15 = lean_box(0);
return x_15;
}
else
{
if (lean_obj_tag(x_8) == 9)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_24; 
x_17 = lean_ctor_get(x_16, 0);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
x_18 = x_16;
x_19 = x_24;
goto block_23;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; 
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 1);
x_20 = x_18;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_17);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
else
{
lean_object* x_25; 
lean_dec_ref(x_16);
x_25 = lean_box(0);
return x_25;
}
}
else
{
lean_object* x_26; 
lean_dec_ref(x_8);
x_26 = lean_box(0);
return x_26;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Sym_getIntValue_x3f_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getIntValue_x3f(lean_object* x_1) {
_start:
{
lean_object* x_14; uint8_t x_15; 
lean_inc_ref(x_1);
x_14 = l_Lean_Expr_cleanupAnnotations(x_1);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_dec_ref(x_14);
goto block_13;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec_ref(x_16);
goto block_13;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec_ref(x_19);
lean_dec_ref(x_16);
goto block_13;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = ((lean_object*)(l_Lean_Meta_Sym_getIntValue_x3f___closed__2));
x_23 = l_Lean_Expr_isConstOf(x_21, x_22);
lean_dec_ref(x_21);
if (x_23 == 0)
{
lean_dec_ref(x_16);
goto block_13;
}
else
{
lean_object* x_24; 
lean_dec_ref(x_1);
x_24 = l_Lean_Meta_Sym_getNatValue_x3f(x_16);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_box(0);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_35; 
x_26 = lean_ctor_get(x_24, 0);
x_35 = !lean_is_exclusive(x_24);
if (x_35 == 0)
{
x_27 = x_24;
x_28 = x_35;
goto block_34;
}
else
{
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_nat_to_int(x_26);
x_30 = lean_int_neg(x_29);
lean_dec(x_29);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_30);
x_31 = x_27;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
}
}
}
}
block_13:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getNatValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_12; 
x_4 = lean_ctor_get(x_2, 0);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
x_5 = x_2;
x_6 = x_12;
goto block_11;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_nat_to_int(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_7);
x_8 = x_5;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Rat_ofInt(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_nat_to_int(x_1);
x_3 = l_Rat_ofInt(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getRatValue_x3f(lean_object* x_1) {
_start:
{
lean_object* x_14; uint8_t x_15; 
lean_inc_ref(x_1);
x_14 = l_Lean_Expr_cleanupAnnotations(x_1);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_dec_ref(x_14);
goto block_13;
}
else
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc_ref(x_16);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec_ref(x_17);
lean_dec_ref(x_16);
goto block_13;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec_ref(x_20);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
goto block_13;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec_ref(x_22);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
goto block_13;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec_ref(x_24);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
goto block_13;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec_ref(x_26);
lean_dec_ref(x_19);
lean_dec_ref(x_16);
goto block_13;
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_29 = ((lean_object*)(l_Lean_Meta_Sym_getRatValue_x3f___closed__2));
x_30 = l_Lean_Expr_isConstOf(x_28, x_29);
lean_dec_ref(x_28);
if (x_30 == 0)
{
lean_dec_ref(x_19);
lean_dec_ref(x_16);
goto block_13;
}
else
{
lean_object* x_31; 
lean_dec_ref(x_1);
x_31 = l_Lean_Meta_Sym_getIntValue_x3f(x_19);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
lean_dec_ref(x_16);
x_32 = lean_box(0);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec_ref(x_31);
x_34 = l_Lean_Meta_Sym_getNatValue_x3f(x_16);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
lean_dec(x_33);
x_35 = lean_box(0);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_46; 
x_36 = lean_ctor_get(x_34, 0);
x_46 = !lean_is_exclusive(x_34);
if (x_46 == 0)
{
x_37 = x_34;
x_38 = x_46;
goto block_45;
}
else
{
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_box(0);
x_38 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = l_Rat_ofInt(x_33);
x_40 = l_Nat_cast___at___00Lean_Meta_Sym_getRatValue_x3f_spec__1(x_36);
x_41 = l_Rat_div(x_39, x_40);
lean_dec_ref(x_39);
if (x_38 == 0)
{
lean_ctor_set(x_37, 0, x_41);
x_42 = x_37;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_41);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
}
}
}
}
}
block_13:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getIntValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_12; 
x_4 = lean_ctor_get(x_2, 0);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
x_5 = x_2;
x_6 = x_12;
goto block_11;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_12;
goto block_11;
}
block_11:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Rat_ofInt(x_4);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_7);
x_8 = x_5;
goto block_9;
}
else
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
x_8 = x_10;
goto block_9;
}
block_9:
{
return x_8;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getBitVecValue_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Expr_cleanupAnnotations(x_1);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec_ref(x_20);
x_22 = lean_box(0);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_23);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec_ref(x_24);
lean_dec_ref(x_23);
x_26 = lean_box(0);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc_ref(x_27);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_29 = ((lean_object*)(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__1));
x_30 = l_Lean_Expr_isConstOf(x_28, x_29);
if (x_30 == 0)
{
uint8_t x_31; 
lean_dec_ref(x_23);
x_31 = l_Lean_Expr_isApp(x_28);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec_ref(x_28);
lean_dec_ref(x_27);
x_32 = lean_box(0);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_28, 1);
lean_inc_ref(x_33);
x_34 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_35 = ((lean_object*)(l_Lean_Meta_Sym_getNatValue_x3f___closed__2));
x_36 = l_Lean_Expr_isConstOf(x_34, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = ((lean_object*)(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__3));
x_38 = l_Lean_Expr_isConstOf(x_34, x_37);
lean_dec_ref(x_34);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec_ref(x_33);
lean_dec_ref(x_27);
x_39 = lean_box(0);
return x_39;
}
else
{
x_2 = x_33;
x_3 = x_27;
goto block_19;
}
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_dec_ref(x_34);
x_40 = l_Lean_Expr_cleanupAnnotations(x_33);
x_41 = l_Lean_Expr_isApp(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec_ref(x_40);
lean_dec_ref(x_27);
x_42 = lean_box(0);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc_ref(x_43);
x_44 = l_Lean_Expr_appFnCleanup___redArg(x_40);
x_45 = ((lean_object*)(l_Lean_Meta_Sym_getBitVecValue_x3f___closed__4));
x_46 = l_Lean_Expr_isConstOf(x_44, x_45);
lean_dec_ref(x_44);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec_ref(x_43);
lean_dec_ref(x_27);
x_47 = lean_box(0);
return x_47;
}
else
{
lean_object* x_48; 
x_48 = l_Lean_Meta_Sym_getNatValue_x3f(x_43);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; 
lean_dec_ref(x_27);
x_49 = lean_box(0);
return x_49;
}
else
{
if (lean_obj_tag(x_27) == 9)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_50);
lean_dec_ref(x_27);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_61; 
x_51 = lean_ctor_get(x_48, 0);
x_61 = !lean_is_exclusive(x_48);
if (x_61 == 0)
{
x_52 = x_48;
x_53 = x_61;
goto block_60;
}
else
{
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_box(0);
x_53 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_50, 0);
lean_inc(x_54);
lean_dec_ref(x_50);
x_55 = l_BitVec_ofNat(x_51, x_54);
lean_dec(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_55);
if (x_53 == 0)
{
lean_ctor_set(x_52, 0, x_56);
x_57 = x_52;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_56);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
else
{
lean_object* x_62; 
lean_dec_ref(x_50);
lean_dec_ref(x_48);
x_62 = lean_box(0);
return x_62;
}
}
else
{
lean_object* x_63; 
lean_dec_ref(x_48);
lean_dec_ref(x_27);
x_63 = lean_box(0);
return x_63;
}
}
}
}
}
}
}
else
{
lean_dec_ref(x_28);
x_2 = x_27;
x_3 = x_23;
goto block_19;
}
}
}
block_19:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Sym_getNatValue_x3f(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec_ref(x_3);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = l_Lean_Meta_Sym_getNatValue_x3f(x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; uint8_t x_18; 
x_9 = lean_ctor_get(x_7, 0);
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
x_10 = x_7;
x_11 = x_18;
goto block_17;
}
else
{
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_box(0);
x_11 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = l_BitVec_ofNat(x_6, x_9);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
if (x_11 == 0)
{
lean_ctor_set(x_10, 0, x_13);
x_14 = x_10;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt8Value_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getNatValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
x_5 = x_2;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_uint8_of_nat(x_4);
lean_dec(x_4);
x_8 = lean_box(x_7);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt16Value_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getNatValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
x_5 = x_2;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
uint16_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_uint16_of_nat(x_4);
lean_dec(x_4);
x_8 = lean_box(x_7);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt32Value_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getNatValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
x_5 = x_2;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
uint32_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_uint32_of_nat(x_4);
lean_dec(x_4);
x_8 = lean_box_uint32(x_7);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getUInt64Value_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getNatValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
x_5 = x_2;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
uint64_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_uint64_of_nat(x_4);
lean_dec(x_4);
x_8 = lean_box_uint64(x_7);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt8Value_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getIntValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
x_5 = x_2;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_int8_of_int(x_4);
lean_dec(x_4);
x_8 = lean_box(x_7);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt16Value_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getIntValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
x_5 = x_2;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
uint16_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_int16_of_int(x_4);
lean_dec(x_4);
x_8 = lean_box(x_7);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt32Value_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getIntValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
x_5 = x_2;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
uint32_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_int32_of_int(x_4);
lean_dec(x_4);
x_8 = lean_box_uint32(x_7);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getInt64Value_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Sym_getIntValue_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_13; 
x_4 = lean_ctor_get(x_2, 0);
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
x_5 = x_2;
x_6 = x_13;
goto block_12;
}
else
{
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_box(0);
x_6 = x_13;
goto block_12;
}
block_12:
{
uint64_t x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_int64_of_int(x_4);
lean_dec(x_4);
x_8 = lean_box_uint64(x_7);
if (x_6 == 0)
{
lean_ctor_set(x_5, 0, x_8);
x_9 = x_5;
goto block_10;
}
else
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_8);
x_9 = x_11;
goto block_10;
}
block_10:
{
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getFinValue_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec_ref(x_5);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc_ref(x_8);
x_9 = l_Lean_Expr_appFnCleanup___redArg(x_5);
x_10 = l_Lean_Expr_isApp(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec_ref(x_9);
lean_dec_ref(x_8);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_12);
x_13 = l_Lean_Expr_appFnCleanup___redArg(x_9);
x_14 = ((lean_object*)(l_Lean_Meta_Sym_getNatValue_x3f___closed__2));
x_15 = l_Lean_Expr_isConstOf(x_13, x_14);
lean_dec_ref(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec_ref(x_12);
lean_dec_ref(x_8);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Expr_cleanupAnnotations(x_12);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec_ref(x_17);
lean_dec_ref(x_8);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_20);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_22 = ((lean_object*)(l_Lean_Meta_Sym_getFinValue_x3f___closed__1));
x_23 = l_Lean_Expr_isConstOf(x_21, x_22);
lean_dec_ref(x_21);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec_ref(x_20);
lean_dec_ref(x_8);
x_24 = lean_box(0);
return x_24;
}
else
{
lean_object* x_25; 
x_25 = l_Lean_Meta_Sym_getNatValue_x3f(x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
lean_dec_ref(x_8);
x_26 = lean_box(0);
return x_26;
}
else
{
if (lean_obj_tag(x_8) == 9)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_8, 0);
lean_inc_ref(x_27);
lean_dec_ref(x_8);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; uint8_t x_41; 
x_28 = lean_ctor_get(x_25, 0);
x_41 = !lean_is_exclusive(x_25);
if (x_41 == 0)
{
x_29 = x_25;
x_30 = x_41;
goto block_40;
}
else
{
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_box(0);
x_30 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_27, 0);
lean_inc(x_31);
lean_dec_ref(x_27);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_nat_dec_eq(x_28, x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_nat_mod(x_31, x_28);
lean_dec(x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_34);
if (x_30 == 0)
{
lean_ctor_set(x_29, 0, x_35);
x_36 = x_29;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_35);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
else
{
lean_object* x_39; 
lean_dec(x_31);
lean_del_object(x_29);
lean_dec(x_28);
x_39 = lean_box(0);
return x_39;
}
}
}
else
{
lean_object* x_42; 
lean_dec_ref(x_27);
lean_dec_ref(x_25);
x_42 = lean_box(0);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec_ref(x_25);
lean_dec_ref(x_8);
x_43 = lean_box(0);
return x_43;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getCharValue_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec_ref(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_7 = ((lean_object*)(l_Lean_Meta_Sym_getCharValue_x3f___closed__1));
x_8 = l_Lean_Expr_isConstOf(x_6, x_7);
lean_dec_ref(x_6);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_5);
x_9 = lean_box(0);
return x_9;
}
else
{
if (lean_obj_tag(x_5) == 9)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_10);
lean_dec_ref(x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_20; 
x_11 = lean_ctor_get(x_10, 0);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
x_12 = x_10;
x_13 = x_20;
goto block_19;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_20;
goto block_19;
}
block_19:
{
uint32_t x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Char_ofNat(x_11);
lean_dec(x_11);
x_15 = lean_box_uint32(x_14);
if (x_13 == 0)
{
lean_ctor_set_tag(x_12, 1);
lean_ctor_set(x_12, 0, x_15);
x_16 = x_12;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
else
{
lean_object* x_21; 
lean_dec_ref(x_10);
x_21 = lean_box(0);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec_ref(x_5);
x_22 = lean_box(0);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_getStringValue_x3f(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_2);
lean_dec_ref(x_1);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_10; 
x_3 = lean_ctor_get(x_2, 0);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
x_4 = x_2;
x_5 = x_10;
goto block_9;
}
else
{
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = x_10;
goto block_9;
}
block_9:
{
lean_object* x_6; 
if (x_5 == 0)
{
x_6 = x_4;
goto block_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_3);
x_6 = x_8;
goto block_7;
}
block_7:
{
return x_6;
}
}
}
else
{
lean_object* x_11; 
lean_dec_ref(x_2);
x_11 = lean_box(0);
return x_11;
}
}
else
{
lean_object* x_12; 
lean_dec_ref(x_1);
x_12 = lean_box(0);
return x_12;
}
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Rat(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Expr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Rat(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Init_Data_Rat(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_LitValues(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Rat(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_LitValues(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_LitValues(builtin);
}
#ifdef __cplusplus
}
#endif
