// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.CastLike
// Imports: public import Lean.Expr import Init.Grind.Ring.Envelope import Init.Grind.Module.Envelope
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
static const lean_string_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ToInt"};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toInt"};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__3_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__2_value),LEAN_SCALAR_PTR_LITERAL(183, 224, 159, 121, 66, 246, 115, 233)}};
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__3_value),LEAN_SCALAR_PTR_LITERAL(251, 249, 151, 171, 150, 156, 160, 34)}};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__4_value;
static const lean_string_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "NatCast"};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__6_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__5_value),LEAN_SCALAR_PTR_LITERAL(65, 128, 63, 191, 243, 154, 52, 80)}};
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__6_value),LEAN_SCALAR_PTR_LITERAL(47, 224, 192, 179, 253, 143, 7, 98)}};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__7_value;
static const lean_string_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "IntCast"};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__8_value;
static const lean_string_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intCast"};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__8_value),LEAN_SCALAR_PTR_LITERAL(63, 186, 193, 83, 149, 255, 18, 69)}};
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__9_value),LEAN_SCALAR_PTR_LITERAL(190, 203, 124, 26, 63, 107, 241, 61)}};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__10_value;
static const lean_string_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Ring"};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__11_value;
static const lean_string_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "OfSemiring"};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__12_value;
static const lean_string_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "toQ"};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__13_value;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__11_value),LEAN_SCALAR_PTR_LITERAL(196, 225, 111, 69, 82, 38, 249, 149)}};
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__12_value),LEAN_SCALAR_PTR_LITERAL(214, 53, 64, 113, 205, 30, 141, 114)}};
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__13_value),LEAN_SCALAR_PTR_LITERAL(232, 146, 236, 221, 122, 127, 105, 70)}};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__14_value;
static const lean_string_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "IntModule"};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__15_value;
static const lean_string_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OfNatModule"};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__15_value),LEAN_SCALAR_PTR_LITERAL(155, 104, 69, 168, 85, 29, 139, 105)}};
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__16_value),LEAN_SCALAR_PTR_LITERAL(74, 53, 51, 211, 82, 161, 6, 157)}};
static const lean_ctor_object l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__13_value),LEAN_SCALAR_PTR_LITERAL(100, 80, 29, 215, 2, 174, 123, 91)}};
static const lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_isCastLikeDeclName___closed__17_value;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isCastLikeDeclName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isCastLikeFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCastLikeFn___boxed(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isCastLikeApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCastLikeApp___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isCastLikeDeclName(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_10; uint8_t x_11; 
x_10 = ((lean_object*)(l_Lean_Meta_Grind_isCastLikeDeclName___closed__14));
x_11 = lean_name_eq(x_1, x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = ((lean_object*)(l_Lean_Meta_Grind_isCastLikeDeclName___closed__17));
x_13 = lean_name_eq(x_1, x_12);
x_2 = x_13;
goto block_9;
}
else
{
x_2 = x_11;
goto block_9;
}
block_9:
{
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = ((lean_object*)(l_Lean_Meta_Grind_isCastLikeDeclName___closed__4));
x_4 = lean_name_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = ((lean_object*)(l_Lean_Meta_Grind_isCastLikeDeclName___closed__7));
x_6 = lean_name_eq(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = ((lean_object*)(l_Lean_Meta_Grind_isCastLikeDeclName___closed__10));
x_8 = lean_name_eq(x_1, x_7);
return x_8;
}
else
{
return x_6;
}
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCastLikeDeclName___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_isCastLikeDeclName(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isCastLikeFn(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Meta_Grind_isCastLikeDeclName(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCastLikeFn___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_isCastLikeFn(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isCastLikeApp(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_getAppFn(x_1);
x_3 = l_Lean_Meta_Grind_isCastLikeFn(x_2);
lean_dec_ref(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isCastLikeApp___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_isCastLikeApp(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Init_Grind_Ring_Envelope(uint8_t builtin);
lean_object* initialize_Init_Grind_Module_Envelope(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_CastLike(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Ring_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Module_Envelope(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
