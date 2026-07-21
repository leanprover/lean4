// Lean compiler output
// Module: Lean.Meta.Sym.Offset
// Imports: public import Lean.Meta.Sym.LitValues
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_num_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_num_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_add_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_add_elim(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedOffset_default = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_instInhabitedOffset = (const lean_object*)&l_Lean_Meta_Sym_instInhabitedOffset_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_inc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_inc___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f___closed__2_value;
static const lean_string_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__3 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__3_value;
static const lean_string_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__2 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__2_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__4_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__3_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__4 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__4_value;
static const lean_string_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMod"};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__6 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__6_value;
static const lean_string_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMod"};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__5 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__5_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__5_value),LEAN_SCALAR_PTR_LITERAL(93, 4, 3, 35, 188, 254, 191, 190)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__6_value),LEAN_SCALAR_PTR_LITERAL(120, 199, 142, 238, 9, 44, 94, 134)}};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__7 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__7_value;
static const lean_string_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__9 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__9_value;
static const lean_string_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__8 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__8_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__8_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__10_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__9_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__10 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__10_value;
static const lean_string_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hMul"};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__12 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__12_value;
static const lean_string_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HMul"};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__11 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__11_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__11_value),LEAN_SCALAR_PTR_LITERAL(254, 113, 255, 140, 142, 9, 169, 40)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__13_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__12_value),LEAN_SCALAR_PTR_LITERAL(248, 227, 200, 215, 229, 255, 92, 22)}};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__13 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__13_value;
static const lean_string_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hSub"};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__15 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__15_value;
static const lean_string_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HSub"};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__14 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__14_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__14_value),LEAN_SCALAR_PTR_LITERAL(121, 130, 45, 212, 110, 237, 236, 233)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__16_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__15_value),LEAN_SCALAR_PTR_LITERAL(231, 253, 204, 163, 168, 77, 27, 58)}};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__16 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__16_value;
static const lean_string_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hAdd"};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__18 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__18_value;
static const lean_string_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HAdd"};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__17 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__17_value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__17_value),LEAN_SCALAR_PTR_LITERAL(221, 239, 47, 196, 170, 166, 59, 144)}};
static const lean_ctor_object l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19_value_aux_0),((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__18_value),LEAN_SCALAR_PTR_LITERAL(134, 172, 115, 219, 189, 252, 56, 148)}};
static const lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19 = (const lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_isOffset_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_Sym_isOffset_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_isOffset_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isOffset_x3f_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isOffset(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isOffset_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_toOffset(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatExpr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isNatValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorIdx(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Meta_Sym_Offset_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
if (lean_obj_tag(v_t_6_) == 0)
{
lean_object* v_k_8_; lean_object* v___x_9_; 
v_k_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc(v_k_8_);
lean_dec_ref_known(v_t_6_, 1);
v___x_9_ = lean_apply_1(v_k_7_, v_k_8_);
return v___x_9_;
}
else
{
lean_object* v_e_10_; lean_object* v_k_11_; lean_object* v___x_12_; 
v_e_10_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_e_10_);
v_k_11_ = lean_ctor_get(v_t_6_, 1);
lean_inc(v_k_11_);
lean_dec_ref_known(v_t_6_, 2);
v___x_12_ = lean_apply_2(v_k_7_, v_e_10_, v_k_11_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim(lean_object* v_motive_13_, lean_object* v_ctorIdx_14_, lean_object* v_t_15_, lean_object* v_h_16_, lean_object* v_k_17_){
_start:
{
lean_object* v___x_18_; 
v___x_18_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_15_, v_k_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim___boxed(lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Meta_Sym_Offset_ctorElim(v_motive_19_, v_ctorIdx_20_, v_t_21_, v_h_22_, v_k_23_);
lean_dec(v_ctorIdx_20_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_num_elim___redArg(lean_object* v_t_25_, lean_object* v_num_26_){
_start:
{
lean_object* v___x_27_; 
v___x_27_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_25_, v_num_26_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_num_elim(lean_object* v_motive_28_, lean_object* v_t_29_, lean_object* v_h_30_, lean_object* v_num_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_29_, v_num_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_add_elim___redArg(lean_object* v_t_33_, lean_object* v_add_34_){
_start:
{
lean_object* v___x_35_; 
v___x_35_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_33_, v_add_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_add_elim(lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_add_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_37_, v_add_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_inc(lean_object* v_x_45_, lean_object* v_x_46_){
_start:
{
if (lean_obj_tag(v_x_45_) == 0)
{
lean_object* v_k_47_; lean_object* v___x_49_; uint8_t v_isShared_50_; uint8_t v_isSharedCheck_55_; 
v_k_47_ = lean_ctor_get(v_x_45_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v_x_45_);
if (v_isSharedCheck_55_ == 0)
{
v___x_49_ = v_x_45_;
v_isShared_50_ = v_isSharedCheck_55_;
goto v_resetjp_48_;
}
else
{
lean_inc(v_k_47_);
lean_dec(v_x_45_);
v___x_49_ = lean_box(0);
v_isShared_50_ = v_isSharedCheck_55_;
goto v_resetjp_48_;
}
v_resetjp_48_:
{
lean_object* v___x_51_; lean_object* v___x_53_; 
v___x_51_ = lean_nat_add(v_k_47_, v_x_46_);
lean_dec(v_k_47_);
if (v_isShared_50_ == 0)
{
lean_ctor_set(v___x_49_, 0, v___x_51_);
v___x_53_ = v___x_49_;
goto v_reusejp_52_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_51_);
v___x_53_ = v_reuseFailAlloc_54_;
goto v_reusejp_52_;
}
v_reusejp_52_:
{
return v___x_53_;
}
}
}
else
{
lean_object* v_e_56_; lean_object* v_k_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_65_; 
v_e_56_ = lean_ctor_get(v_x_45_, 0);
v_k_57_ = lean_ctor_get(v_x_45_, 1);
v_isSharedCheck_65_ = !lean_is_exclusive(v_x_45_);
if (v_isSharedCheck_65_ == 0)
{
v___x_59_ = v_x_45_;
v_isShared_60_ = v_isSharedCheck_65_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_k_57_);
lean_inc(v_e_56_);
lean_dec(v_x_45_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_65_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v___x_61_; lean_object* v___x_63_; 
v___x_61_ = lean_nat_add(v_k_57_, v_x_46_);
lean_dec(v_k_57_);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 1, v___x_61_);
v___x_63_ = v___x_59_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_e_56_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v___x_61_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_inc___boxed(lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Meta_Sym_Offset_inc(v_x_66_, v_x_67_);
lean_dec(v_x_67_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit(lean_object* v_e_107_){
_start:
{
lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_108_ = l_Lean_Expr_cleanupAnnotations(v_e_107_);
v___x_109_ = l_Lean_Expr_isApp(v___x_108_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; 
lean_dec_ref(v___x_108_);
v___x_110_ = lean_box(0);
return v___x_110_;
}
else
{
lean_object* v_arg_111_; lean_object* v___x_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v_arg_111_ = lean_ctor_get(v___x_108_, 1);
lean_inc_ref(v_arg_111_);
v___x_112_ = l_Lean_Expr_appFnCleanup___redArg(v___x_108_);
v___x_113_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__1));
v___x_114_ = l_Lean_Expr_isConstOf(v___x_112_, v___x_113_);
if (v___x_114_ == 0)
{
uint8_t v___x_115_; 
v___x_115_ = l_Lean_Expr_isApp(v___x_112_);
if (v___x_115_ == 0)
{
lean_object* v___x_116_; 
lean_dec_ref(v___x_112_);
lean_dec_ref(v_arg_111_);
v___x_116_ = lean_box(0);
return v___x_116_;
}
else
{
lean_object* v_arg_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v_arg_117_ = lean_ctor_get(v___x_112_, 1);
lean_inc_ref(v_arg_117_);
v___x_118_ = l_Lean_Expr_appFnCleanup___redArg(v___x_112_);
v___x_119_ = l_Lean_Expr_isApp(v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; 
lean_dec_ref(v___x_118_);
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_111_);
v___x_120_ = lean_box(0);
return v___x_120_;
}
else
{
lean_object* v___x_121_; lean_object* v___x_122_; uint8_t v___x_123_; 
v___x_121_ = l_Lean_Expr_appFnCleanup___redArg(v___x_118_);
v___x_122_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__4));
v___x_123_ = l_Lean_Expr_isConstOf(v___x_121_, v___x_122_);
if (v___x_123_ == 0)
{
uint8_t v___x_124_; 
v___x_124_ = l_Lean_Expr_isApp(v___x_121_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; 
lean_dec_ref(v___x_121_);
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_111_);
v___x_125_ = lean_box(0);
return v___x_125_;
}
else
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = l_Lean_Expr_appFnCleanup___redArg(v___x_121_);
v___x_127_ = l_Lean_Expr_isApp(v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; 
lean_dec_ref(v___x_126_);
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_111_);
v___x_128_ = lean_box(0);
return v___x_128_;
}
else
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = l_Lean_Expr_appFnCleanup___redArg(v___x_126_);
v___x_130_ = l_Lean_Expr_isApp(v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; 
lean_dec_ref(v___x_129_);
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_111_);
v___x_131_ = lean_box(0);
return v___x_131_;
}
else
{
lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_132_ = l_Lean_Expr_appFnCleanup___redArg(v___x_129_);
v___x_133_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__7));
v___x_134_ = l_Lean_Expr_isConstOf(v___x_132_, v___x_133_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_135_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__10));
v___x_136_ = l_Lean_Expr_isConstOf(v___x_132_, v___x_135_);
if (v___x_136_ == 0)
{
lean_object* v___x_137_; uint8_t v___x_138_; 
v___x_137_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__13));
v___x_138_ = l_Lean_Expr_isConstOf(v___x_132_, v___x_137_);
if (v___x_138_ == 0)
{
lean_object* v___x_139_; uint8_t v___x_140_; 
v___x_139_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__16));
v___x_140_ = l_Lean_Expr_isConstOf(v___x_132_, v___x_139_);
if (v___x_140_ == 0)
{
lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_141_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19));
v___x_142_ = l_Lean_Expr_isConstOf(v___x_132_, v___x_141_);
lean_dec_ref(v___x_132_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; 
lean_dec_ref(v_arg_117_);
lean_dec_ref(v_arg_111_);
v___x_143_ = lean_box(0);
return v___x_143_;
}
else
{
lean_object* v___x_144_; 
v___x_144_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_117_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_dec_ref(v_arg_111_);
return v___x_144_;
}
else
{
lean_object* v_val_145_; lean_object* v___x_146_; 
v_val_145_ = lean_ctor_get(v___x_144_, 0);
lean_inc(v_val_145_);
lean_dec_ref_known(v___x_144_, 1);
v___x_146_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_111_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_dec(v_val_145_);
return v___x_146_;
}
else
{
lean_object* v_val_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_155_; 
v_val_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_155_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_val_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_155_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v___x_153_; 
v___x_151_ = lean_nat_add(v_val_145_, v_val_147_);
lean_dec(v_val_147_);
lean_dec(v_val_145_);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_151_);
v___x_153_ = v___x_149_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v___x_151_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
}
}
else
{
lean_object* v___x_156_; 
lean_dec_ref(v___x_132_);
v___x_156_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_117_);
if (lean_obj_tag(v___x_156_) == 0)
{
lean_dec_ref(v_arg_111_);
return v___x_156_;
}
else
{
lean_object* v_val_157_; lean_object* v___x_158_; 
v_val_157_ = lean_ctor_get(v___x_156_, 0);
lean_inc(v_val_157_);
lean_dec_ref_known(v___x_156_, 1);
v___x_158_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_111_);
if (lean_obj_tag(v___x_158_) == 0)
{
lean_dec(v_val_157_);
return v___x_158_;
}
else
{
lean_object* v_val_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_167_; 
v_val_159_ = lean_ctor_get(v___x_158_, 0);
v_isSharedCheck_167_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_167_ == 0)
{
v___x_161_ = v___x_158_;
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_val_159_);
lean_dec(v___x_158_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_167_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_163_ = lean_nat_sub(v_val_157_, v_val_159_);
lean_dec(v_val_159_);
lean_dec(v_val_157_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_163_);
v___x_165_ = v___x_161_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
}
else
{
lean_object* v___x_168_; 
lean_dec_ref(v___x_132_);
v___x_168_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_117_);
if (lean_obj_tag(v___x_168_) == 0)
{
lean_dec_ref(v_arg_111_);
return v___x_168_;
}
else
{
lean_object* v_val_169_; lean_object* v___x_170_; 
v_val_169_ = lean_ctor_get(v___x_168_, 0);
lean_inc(v_val_169_);
lean_dec_ref_known(v___x_168_, 1);
v___x_170_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_111_);
if (lean_obj_tag(v___x_170_) == 0)
{
lean_dec(v_val_169_);
return v___x_170_;
}
else
{
lean_object* v_val_171_; lean_object* v___x_173_; uint8_t v_isShared_174_; uint8_t v_isSharedCheck_179_; 
v_val_171_ = lean_ctor_get(v___x_170_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_170_);
if (v_isSharedCheck_179_ == 0)
{
v___x_173_ = v___x_170_;
v_isShared_174_ = v_isSharedCheck_179_;
goto v_resetjp_172_;
}
else
{
lean_inc(v_val_171_);
lean_dec(v___x_170_);
v___x_173_ = lean_box(0);
v_isShared_174_ = v_isSharedCheck_179_;
goto v_resetjp_172_;
}
v_resetjp_172_:
{
lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_175_ = lean_nat_mul(v_val_169_, v_val_171_);
lean_dec(v_val_171_);
lean_dec(v_val_169_);
if (v_isShared_174_ == 0)
{
lean_ctor_set(v___x_173_, 0, v___x_175_);
v___x_177_ = v___x_173_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
}
else
{
lean_object* v___x_180_; 
lean_dec_ref(v___x_132_);
v___x_180_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_117_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_dec_ref(v_arg_111_);
return v___x_180_;
}
else
{
lean_object* v_val_181_; lean_object* v___x_182_; 
v_val_181_ = lean_ctor_get(v___x_180_, 0);
lean_inc(v_val_181_);
lean_dec_ref_known(v___x_180_, 1);
v___x_182_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_111_);
if (lean_obj_tag(v___x_182_) == 0)
{
lean_dec(v_val_181_);
return v___x_182_;
}
else
{
lean_object* v_val_183_; lean_object* v___x_185_; uint8_t v_isShared_186_; uint8_t v_isSharedCheck_191_; 
v_val_183_ = lean_ctor_get(v___x_182_, 0);
v_isSharedCheck_191_ = !lean_is_exclusive(v___x_182_);
if (v_isSharedCheck_191_ == 0)
{
v___x_185_ = v___x_182_;
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
else
{
lean_inc(v_val_183_);
lean_dec(v___x_182_);
v___x_185_ = lean_box(0);
v_isShared_186_ = v_isSharedCheck_191_;
goto v_resetjp_184_;
}
v_resetjp_184_:
{
lean_object* v___x_187_; lean_object* v___x_189_; 
v___x_187_ = lean_nat_div(v_val_181_, v_val_183_);
lean_dec(v_val_183_);
lean_dec(v_val_181_);
if (v_isShared_186_ == 0)
{
lean_ctor_set(v___x_185_, 0, v___x_187_);
v___x_189_ = v___x_185_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
}
}
else
{
lean_object* v___x_192_; 
lean_dec_ref(v___x_132_);
v___x_192_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_117_);
if (lean_obj_tag(v___x_192_) == 0)
{
lean_dec_ref(v_arg_111_);
return v___x_192_;
}
else
{
lean_object* v_val_193_; lean_object* v___x_194_; 
v_val_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_val_193_);
lean_dec_ref_known(v___x_192_, 1);
v___x_194_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_111_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_dec(v_val_193_);
return v___x_194_;
}
else
{
lean_object* v_val_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_203_; 
v_val_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_203_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_val_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_203_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_199_ = lean_nat_mod(v_val_193_, v_val_195_);
lean_dec(v_val_195_);
lean_dec(v_val_193_);
if (v_isShared_198_ == 0)
{
lean_ctor_set(v___x_197_, 0, v___x_199_);
v___x_201_ = v___x_197_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_204_; 
lean_dec_ref(v___x_121_);
lean_dec_ref(v_arg_111_);
v___x_204_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_117_);
return v___x_204_;
}
}
}
}
else
{
lean_object* v___x_205_; 
lean_dec_ref(v___x_112_);
v___x_205_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_111_);
if (lean_obj_tag(v___x_205_) == 0)
{
return v___x_205_;
}
else
{
lean_object* v_val_206_; lean_object* v___x_208_; uint8_t v_isShared_209_; uint8_t v_isSharedCheck_215_; 
v_val_206_ = lean_ctor_get(v___x_205_, 0);
v_isSharedCheck_215_ = !lean_is_exclusive(v___x_205_);
if (v_isSharedCheck_215_ == 0)
{
v___x_208_ = v___x_205_;
v_isShared_209_ = v_isSharedCheck_215_;
goto v_resetjp_207_;
}
else
{
lean_inc(v_val_206_);
lean_dec(v___x_205_);
v___x_208_ = lean_box(0);
v_isShared_209_ = v_isSharedCheck_215_;
goto v_resetjp_207_;
}
v_resetjp_207_:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_210_ = lean_unsigned_to_nat(1u);
v___x_211_ = lean_nat_add(v_val_206_, v___x_210_);
lean_dec(v_val_206_);
if (v_isShared_209_ == 0)
{
lean_ctor_set(v___x_208_, 0, v___x_211_);
v___x_213_ = v___x_208_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v___x_211_);
v___x_213_ = v_reuseFailAlloc_214_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
return v___x_213_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(lean_object* v_e_216_){
_start:
{
switch(lean_obj_tag(v_e_216_))
{
case 9:
{
lean_object* v_a_217_; 
v_a_217_ = lean_ctor_get(v_e_216_, 0);
lean_inc_ref(v_a_217_);
lean_dec_ref_known(v_e_216_, 1);
if (lean_obj_tag(v_a_217_) == 0)
{
lean_object* v_val_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
v_val_218_ = lean_ctor_get(v_a_217_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v_a_217_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v_a_217_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_val_218_);
lean_dec(v_a_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
lean_ctor_set_tag(v___x_220_, 1);
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_val_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
else
{
lean_object* v___x_226_; 
lean_dec_ref(v_a_217_);
v___x_226_ = lean_box(0);
return v___x_226_;
}
}
case 10:
{
lean_object* v_expr_227_; 
v_expr_227_ = lean_ctor_get(v_e_216_, 1);
lean_inc_ref(v_expr_227_);
lean_dec_ref_known(v_e_216_, 2);
v_e_216_ = v_expr_227_;
goto _start;
}
case 4:
{
lean_object* v_declName_229_; 
v_declName_229_ = lean_ctor_get(v_e_216_, 0);
lean_inc(v_declName_229_);
lean_dec_ref_known(v_e_216_, 2);
if (lean_obj_tag(v_declName_229_) == 1)
{
lean_object* v_pre_230_; 
v_pre_230_ = lean_ctor_get(v_declName_229_, 0);
lean_inc(v_pre_230_);
if (lean_obj_tag(v_pre_230_) == 1)
{
lean_object* v_pre_231_; 
v_pre_231_ = lean_ctor_get(v_pre_230_, 0);
if (lean_obj_tag(v_pre_231_) == 0)
{
lean_object* v_str_232_; lean_object* v_str_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v_str_232_ = lean_ctor_get(v_declName_229_, 1);
lean_inc_ref(v_str_232_);
lean_dec_ref_known(v_declName_229_, 2);
v_str_233_ = lean_ctor_get(v_pre_230_, 1);
lean_inc_ref(v_str_233_);
lean_dec_ref_known(v_pre_230_, 2);
v___x_234_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f___closed__0));
v___x_235_ = lean_string_dec_eq(v_str_233_, v___x_234_);
lean_dec_ref(v_str_233_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; 
lean_dec_ref(v_str_232_);
v___x_236_ = lean_box(0);
return v___x_236_;
}
else
{
lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_237_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f___closed__1));
v___x_238_ = lean_string_dec_eq(v_str_232_, v___x_237_);
lean_dec_ref(v_str_232_);
if (v___x_238_ == 0)
{
lean_object* v___x_239_; 
v___x_239_ = lean_box(0);
return v___x_239_;
}
else
{
lean_object* v___x_240_; 
v___x_240_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f___closed__2));
return v___x_240_;
}
}
}
else
{
lean_object* v___x_241_; 
lean_dec_ref_known(v_pre_230_, 2);
lean_dec_ref_known(v_declName_229_, 2);
v___x_241_ = lean_box(0);
return v___x_241_;
}
}
else
{
lean_object* v___x_242_; 
lean_dec_ref_known(v_declName_229_, 2);
lean_dec(v_pre_230_);
v___x_242_ = lean_box(0);
return v___x_242_;
}
}
else
{
lean_object* v___x_243_; 
lean_dec(v_declName_229_);
v___x_243_ = lean_box(0);
return v___x_243_;
}
}
case 5:
{
lean_object* v___x_244_; 
v___x_244_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit(v_e_216_);
return v___x_244_;
}
case 2:
{
lean_object* v___x_245_; 
v___x_245_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit(v_e_216_);
return v___x_245_;
}
default: 
{
lean_object* v___x_246_; 
lean_dec_ref(v_e_216_);
v___x_246_ = lean_box(0);
return v___x_246_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f(lean_object* v_e_249_){
_start:
{
lean_object* v___x_250_; uint8_t v___x_251_; 
v___x_250_ = l_Lean_Expr_cleanupAnnotations(v_e_249_);
v___x_251_ = l_Lean_Expr_isApp(v___x_250_);
if (v___x_251_ == 0)
{
lean_object* v___x_252_; 
lean_dec_ref(v___x_250_);
v___x_252_ = lean_box(0);
return v___x_252_;
}
else
{
lean_object* v_arg_253_; lean_object* v___x_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_arg_253_ = lean_ctor_get(v___x_250_, 1);
lean_inc_ref(v_arg_253_);
v___x_254_ = l_Lean_Expr_appFnCleanup___redArg(v___x_250_);
v___x_255_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__1));
v___x_256_ = l_Lean_Expr_isConstOf(v___x_254_, v___x_255_);
if (v___x_256_ == 0)
{
uint8_t v___x_257_; 
v___x_257_ = l_Lean_Expr_isApp(v___x_254_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; 
lean_dec_ref(v___x_254_);
lean_dec_ref(v_arg_253_);
v___x_258_ = lean_box(0);
return v___x_258_;
}
else
{
lean_object* v_arg_259_; lean_object* v___x_260_; uint8_t v___x_261_; 
v_arg_259_ = lean_ctor_get(v___x_254_, 1);
lean_inc_ref(v_arg_259_);
v___x_260_ = l_Lean_Expr_appFnCleanup___redArg(v___x_254_);
v___x_261_ = l_Lean_Expr_isApp(v___x_260_);
if (v___x_261_ == 0)
{
lean_object* v___x_262_; 
lean_dec_ref(v___x_260_);
lean_dec_ref(v_arg_259_);
lean_dec_ref(v_arg_253_);
v___x_262_ = lean_box(0);
return v___x_262_;
}
else
{
lean_object* v___x_263_; uint8_t v___x_264_; 
v___x_263_ = l_Lean_Expr_appFnCleanup___redArg(v___x_260_);
v___x_264_ = l_Lean_Expr_isApp(v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
lean_dec_ref(v___x_263_);
lean_dec_ref(v_arg_259_);
lean_dec_ref(v_arg_253_);
v___x_265_ = lean_box(0);
return v___x_265_;
}
else
{
lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_266_ = l_Lean_Expr_appFnCleanup___redArg(v___x_263_);
v___x_267_ = l_Lean_Expr_isApp(v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; 
lean_dec_ref(v___x_266_);
lean_dec_ref(v_arg_259_);
lean_dec_ref(v_arg_253_);
v___x_268_ = lean_box(0);
return v___x_268_;
}
else
{
lean_object* v___x_269_; uint8_t v___x_270_; 
v___x_269_ = l_Lean_Expr_appFnCleanup___redArg(v___x_266_);
v___x_270_ = l_Lean_Expr_isApp(v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; 
lean_dec_ref(v___x_269_);
lean_dec_ref(v_arg_259_);
lean_dec_ref(v_arg_253_);
v___x_271_ = lean_box(0);
return v___x_271_;
}
else
{
lean_object* v_arg_272_; lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
v_arg_272_ = lean_ctor_get(v___x_269_, 1);
lean_inc_ref(v_arg_272_);
v___x_273_ = l_Lean_Expr_appFnCleanup___redArg(v___x_269_);
v___x_274_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19));
v___x_275_ = l_Lean_Expr_isConstOf(v___x_273_, v___x_274_);
lean_dec_ref(v___x_273_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; 
lean_dec_ref(v_arg_272_);
lean_dec_ref(v_arg_259_);
lean_dec_ref(v_arg_253_);
v___x_276_ = lean_box(0);
return v___x_276_;
}
else
{
lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_277_ = ((lean_object*)(l_Lean_Meta_Sym_isOffset_x3f___closed__0));
v___x_278_ = l_Lean_Expr_isConstOf(v_arg_272_, v___x_277_);
lean_dec_ref(v_arg_272_);
if (v___x_278_ == 0)
{
lean_object* v___x_279_; 
lean_dec_ref(v_arg_259_);
lean_dec_ref(v_arg_253_);
v___x_279_ = lean_box(0);
return v___x_279_;
}
else
{
lean_object* v___x_280_; 
v___x_280_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_253_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v___x_281_; 
lean_dec_ref(v_arg_259_);
v___x_281_ = lean_box(0);
return v___x_281_;
}
else
{
lean_object* v_val_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_291_; 
v_val_282_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_291_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_291_ == 0)
{
v___x_284_ = v___x_280_;
v_isShared_285_ = v_isSharedCheck_291_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_val_282_);
lean_dec(v___x_280_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_291_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_286_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isOffset_x3f_get(v_arg_259_);
v___x_287_ = l_Lean_Meta_Sym_Offset_inc(v___x_286_, v_val_282_);
lean_dec(v_val_282_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v___x_287_);
v___x_289_ = v___x_284_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v___x_287_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
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
else
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
lean_dec_ref(v___x_254_);
v___x_292_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isOffset_x3f_get(v_arg_253_);
v___x_293_ = lean_unsigned_to_nat(1u);
v___x_294_ = l_Lean_Meta_Sym_Offset_inc(v___x_292_, v___x_293_);
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v___x_294_);
return v___x_295_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isOffset_x3f_get(lean_object* v_e_296_){
_start:
{
lean_object* v___x_297_; 
lean_inc_ref(v_e_296_);
v___x_297_ = l_Lean_Meta_Sym_isOffset_x3f(v_e_296_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_298_ = lean_unsigned_to_nat(0u);
v___x_299_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_299_, 0, v_e_296_);
lean_ctor_set(v___x_299_, 1, v___x_298_);
return v___x_299_;
}
else
{
lean_object* v_val_300_; 
lean_dec_ref(v_e_296_);
v_val_300_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_val_300_);
lean_dec_ref_known(v___x_297_, 1);
return v_val_300_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f_x27(lean_object* v_declName_301_, lean_object* v_p_302_){
_start:
{
uint8_t v___y_304_; lean_object* v___x_307_; uint8_t v___x_308_; 
v___x_307_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__1));
v___x_308_ = lean_name_eq(v_declName_301_, v___x_307_);
if (v___x_308_ == 0)
{
lean_object* v___x_309_; uint8_t v___x_310_; 
v___x_309_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19));
v___x_310_ = lean_name_eq(v_declName_301_, v___x_309_);
v___y_304_ = v___x_310_;
goto v___jp_303_;
}
else
{
v___y_304_ = v___x_308_;
goto v___jp_303_;
}
v___jp_303_:
{
if (v___y_304_ == 0)
{
lean_object* v___x_305_; 
lean_dec_ref(v_p_302_);
v___x_305_ = lean_box(0);
return v___x_305_;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_Meta_Sym_isOffset_x3f(v_p_302_);
return v___x_306_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f_x27___boxed(lean_object* v_declName_311_, lean_object* v_p_312_){
_start:
{
lean_object* v_res_313_; 
v_res_313_ = l_Lean_Meta_Sym_isOffset_x3f_x27(v_declName_311_, v_p_312_);
lean_dec(v_declName_311_);
return v_res_313_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(lean_object* v_e_314_){
_start:
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = ((lean_object*)(l_Lean_Meta_Sym_isOffset_x3f___closed__0));
v___x_316_ = l_Lean_Expr_isConstOf(v_e_314_, v___x_315_);
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType___boxed(lean_object* v_e_317_){
_start:
{
uint8_t v_res_318_; lean_object* v_r_319_; 
v_res_318_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(v_e_317_);
lean_dec_ref(v_e_317_);
v_r_319_ = lean_box(v_res_318_);
return v_r_319_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isOffset(lean_object* v_e_320_){
_start:
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = l_Lean_Expr_cleanupAnnotations(v_e_320_);
v___x_322_ = l_Lean_Expr_isApp(v___x_321_);
if (v___x_322_ == 0)
{
lean_dec_ref(v___x_321_);
return v___x_322_;
}
else
{
lean_object* v_arg_323_; lean_object* v___x_324_; lean_object* v___x_325_; uint8_t v___x_326_; 
v_arg_323_ = lean_ctor_get(v___x_321_, 1);
lean_inc_ref(v_arg_323_);
v___x_324_ = l_Lean_Expr_appFnCleanup___redArg(v___x_321_);
v___x_325_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__1));
v___x_326_ = l_Lean_Expr_isConstOf(v___x_324_, v___x_325_);
if (v___x_326_ == 0)
{
uint8_t v___x_327_; 
v___x_327_ = l_Lean_Expr_isApp(v___x_324_);
if (v___x_327_ == 0)
{
lean_dec_ref(v___x_324_);
lean_dec_ref(v_arg_323_);
return v___x_327_;
}
else
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = l_Lean_Expr_appFnCleanup___redArg(v___x_324_);
v___x_329_ = l_Lean_Expr_isApp(v___x_328_);
if (v___x_329_ == 0)
{
lean_dec_ref(v___x_328_);
lean_dec_ref(v_arg_323_);
return v___x_329_;
}
else
{
lean_object* v___x_330_; uint8_t v___x_331_; 
v___x_330_ = l_Lean_Expr_appFnCleanup___redArg(v___x_328_);
v___x_331_ = l_Lean_Expr_isApp(v___x_330_);
if (v___x_331_ == 0)
{
lean_dec_ref(v___x_330_);
lean_dec_ref(v_arg_323_);
return v___x_331_;
}
else
{
lean_object* v___x_332_; uint8_t v___x_333_; 
v___x_332_ = l_Lean_Expr_appFnCleanup___redArg(v___x_330_);
v___x_333_ = l_Lean_Expr_isApp(v___x_332_);
if (v___x_333_ == 0)
{
lean_dec_ref(v___x_332_);
lean_dec_ref(v_arg_323_);
return v___x_333_;
}
else
{
lean_object* v___x_334_; uint8_t v___x_335_; 
v___x_334_ = l_Lean_Expr_appFnCleanup___redArg(v___x_332_);
v___x_335_ = l_Lean_Expr_isApp(v___x_334_);
if (v___x_335_ == 0)
{
lean_dec_ref(v___x_334_);
lean_dec_ref(v_arg_323_);
return v___x_335_;
}
else
{
lean_object* v_arg_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; 
v_arg_336_ = lean_ctor_get(v___x_334_, 1);
lean_inc_ref(v_arg_336_);
v___x_337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_334_);
v___x_338_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19));
v___x_339_ = l_Lean_Expr_isConstOf(v___x_337_, v___x_338_);
lean_dec_ref(v___x_337_);
if (v___x_339_ == 0)
{
lean_dec_ref(v_arg_336_);
lean_dec_ref(v_arg_323_);
return v___x_339_;
}
else
{
uint8_t v___x_340_; 
v___x_340_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(v_arg_336_);
lean_dec_ref(v_arg_336_);
if (v___x_340_ == 0)
{
lean_dec_ref(v_arg_323_);
return v___x_340_;
}
else
{
lean_object* v___x_341_; 
v___x_341_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_323_);
if (lean_obj_tag(v___x_341_) == 0)
{
return v___x_326_;
}
else
{
lean_dec_ref_known(v___x_341_, 1);
return v___x_340_;
}
}
}
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_324_);
lean_dec_ref(v_arg_323_);
return v___x_326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset___boxed(lean_object* v_e_342_){
_start:
{
uint8_t v_res_343_; lean_object* v_r_344_; 
v_res_343_ = l_Lean_Meta_Sym_isOffset(v_e_342_);
v_r_344_ = lean_box(v_res_343_);
return v_r_344_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isOffset_x27(lean_object* v_declName_345_, lean_object* v_p_346_){
_start:
{
uint8_t v___y_348_; lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__1));
v___x_351_ = lean_name_eq(v_declName_345_, v___x_350_);
if (v___x_351_ == 0)
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19));
v___x_353_ = lean_name_eq(v_declName_345_, v___x_352_);
v___y_348_ = v___x_353_;
goto v___jp_347_;
}
else
{
v___y_348_ = v___x_351_;
goto v___jp_347_;
}
v___jp_347_:
{
if (v___y_348_ == 0)
{
lean_dec_ref(v_p_346_);
return v___y_348_;
}
else
{
uint8_t v___x_349_; 
v___x_349_ = l_Lean_Meta_Sym_isOffset(v_p_346_);
return v___x_349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x27___boxed(lean_object* v_declName_354_, lean_object* v_p_355_){
_start:
{
uint8_t v_res_356_; lean_object* v_r_357_; 
v_res_356_ = l_Lean_Meta_Sym_isOffset_x27(v_declName_354_, v_p_355_);
lean_dec(v_declName_354_);
v_r_357_ = lean_box(v_res_356_);
return v_r_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_toOffset(lean_object* v_e_358_){
_start:
{
lean_object* v___x_365_; uint8_t v___x_366_; 
lean_inc_ref(v_e_358_);
v___x_365_ = l_Lean_Expr_cleanupAnnotations(v_e_358_);
v___x_366_ = l_Lean_Expr_isApp(v___x_365_);
if (v___x_366_ == 0)
{
lean_dec_ref(v___x_365_);
goto v___jp_359_;
}
else
{
lean_object* v_arg_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v_arg_367_ = lean_ctor_get(v___x_365_, 1);
lean_inc_ref(v_arg_367_);
v___x_368_ = l_Lean_Expr_appFnCleanup___redArg(v___x_365_);
v___x_369_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__1));
v___x_370_ = l_Lean_Expr_isConstOf(v___x_368_, v___x_369_);
if (v___x_370_ == 0)
{
uint8_t v___x_371_; 
v___x_371_ = l_Lean_Expr_isApp(v___x_368_);
if (v___x_371_ == 0)
{
lean_dec_ref(v___x_368_);
lean_dec_ref(v_arg_367_);
goto v___jp_359_;
}
else
{
lean_object* v_arg_372_; lean_object* v___x_373_; uint8_t v___x_374_; 
v_arg_372_ = lean_ctor_get(v___x_368_, 1);
lean_inc_ref(v_arg_372_);
v___x_373_ = l_Lean_Expr_appFnCleanup___redArg(v___x_368_);
v___x_374_ = l_Lean_Expr_isApp(v___x_373_);
if (v___x_374_ == 0)
{
lean_dec_ref(v___x_373_);
lean_dec_ref(v_arg_372_);
lean_dec_ref(v_arg_367_);
goto v___jp_359_;
}
else
{
lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; 
v___x_375_ = l_Lean_Expr_appFnCleanup___redArg(v___x_373_);
v___x_376_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__4));
v___x_377_ = l_Lean_Expr_isConstOf(v___x_375_, v___x_376_);
if (v___x_377_ == 0)
{
uint8_t v___x_378_; 
v___x_378_ = l_Lean_Expr_isApp(v___x_375_);
if (v___x_378_ == 0)
{
lean_dec_ref(v___x_375_);
lean_dec_ref(v_arg_372_);
lean_dec_ref(v_arg_367_);
goto v___jp_359_;
}
else
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = l_Lean_Expr_appFnCleanup___redArg(v___x_375_);
v___x_380_ = l_Lean_Expr_isApp(v___x_379_);
if (v___x_380_ == 0)
{
lean_dec_ref(v___x_379_);
lean_dec_ref(v_arg_372_);
lean_dec_ref(v_arg_367_);
goto v___jp_359_;
}
else
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = l_Lean_Expr_appFnCleanup___redArg(v___x_379_);
v___x_382_ = l_Lean_Expr_isApp(v___x_381_);
if (v___x_382_ == 0)
{
lean_dec_ref(v___x_381_);
lean_dec_ref(v_arg_372_);
lean_dec_ref(v_arg_367_);
goto v___jp_359_;
}
else
{
lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_383_ = l_Lean_Expr_appFnCleanup___redArg(v___x_381_);
v___x_384_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19));
v___x_385_ = l_Lean_Expr_isConstOf(v___x_383_, v___x_384_);
lean_dec_ref(v___x_383_);
if (v___x_385_ == 0)
{
lean_dec_ref(v_arg_372_);
lean_dec_ref(v_arg_367_);
goto v___jp_359_;
}
else
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_367_);
if (lean_obj_tag(v___x_386_) == 1)
{
lean_object* v_val_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
lean_dec_ref(v_e_358_);
v_val_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_val_387_);
lean_dec_ref_known(v___x_386_, 1);
v___x_388_ = l_Lean_Meta_Sym_toOffset(v_arg_372_);
v___x_389_ = l_Lean_Meta_Sym_Offset_inc(v___x_388_, v_val_387_);
lean_dec(v_val_387_);
return v___x_389_;
}
else
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec(v___x_386_);
lean_dec_ref(v_arg_372_);
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_391_, 0, v_e_358_);
lean_ctor_set(v___x_391_, 1, v___x_390_);
return v___x_391_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_375_);
lean_dec_ref(v_arg_367_);
if (lean_obj_tag(v_arg_372_) == 9)
{
lean_object* v_a_392_; 
v_a_392_ = lean_ctor_get(v_arg_372_, 0);
lean_inc_ref(v_a_392_);
lean_dec_ref_known(v_arg_372_, 1);
if (lean_obj_tag(v_a_392_) == 0)
{
lean_object* v_val_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_400_; 
lean_dec_ref(v_e_358_);
v_val_393_ = lean_ctor_get(v_a_392_, 0);
v_isSharedCheck_400_ = !lean_is_exclusive(v_a_392_);
if (v_isSharedCheck_400_ == 0)
{
v___x_395_ = v_a_392_;
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_val_393_);
lean_dec(v_a_392_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_400_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_398_; 
if (v_isShared_396_ == 0)
{
v___x_398_ = v___x_395_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_399_; 
v_reuseFailAlloc_399_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_399_, 0, v_val_393_);
v___x_398_ = v_reuseFailAlloc_399_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
return v___x_398_;
}
}
}
else
{
lean_dec_ref(v_a_392_);
goto v___jp_362_;
}
}
else
{
lean_dec_ref(v_arg_372_);
goto v___jp_362_;
}
}
}
}
}
else
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
lean_dec_ref(v___x_368_);
lean_dec_ref(v_e_358_);
v___x_401_ = l_Lean_Meta_Sym_toOffset(v_arg_367_);
v___x_402_ = lean_unsigned_to_nat(1u);
v___x_403_ = l_Lean_Meta_Sym_Offset_inc(v___x_401_, v___x_402_);
return v___x_403_;
}
}
v___jp_359_:
{
lean_object* v___x_360_; lean_object* v___x_361_; 
v___x_360_ = lean_unsigned_to_nat(0u);
v___x_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_361_, 0, v_e_358_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
return v___x_361_;
}
v___jp_362_:
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = lean_unsigned_to_nat(0u);
v___x_364_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_364_, 0, v_e_358_);
lean_ctor_set(v___x_364_, 1, v___x_363_);
return v___x_364_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatExpr(lean_object* v_e_404_){
_start:
{
lean_object* v___x_405_; uint8_t v___x_406_; 
v___x_405_ = l_Lean_Expr_cleanupAnnotations(v_e_404_);
v___x_406_ = l_Lean_Expr_isApp(v___x_405_);
if (v___x_406_ == 0)
{
lean_dec_ref(v___x_405_);
return v___x_406_;
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_407_ = l_Lean_Expr_appFnCleanup___redArg(v___x_405_);
v___x_408_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__1));
v___x_409_ = l_Lean_Expr_isConstOf(v___x_407_, v___x_408_);
if (v___x_409_ == 0)
{
uint8_t v___x_410_; 
v___x_410_ = l_Lean_Expr_isApp(v___x_407_);
if (v___x_410_ == 0)
{
lean_dec_ref(v___x_407_);
return v___x_410_;
}
else
{
lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_411_ = l_Lean_Expr_appFnCleanup___redArg(v___x_407_);
v___x_412_ = l_Lean_Expr_isApp(v___x_411_);
if (v___x_412_ == 0)
{
lean_dec_ref(v___x_411_);
return v___x_412_;
}
else
{
lean_object* v_arg_413_; lean_object* v___x_414_; lean_object* v___x_415_; uint8_t v___x_416_; 
v_arg_413_ = lean_ctor_get(v___x_411_, 1);
lean_inc_ref(v_arg_413_);
v___x_414_ = l_Lean_Expr_appFnCleanup___redArg(v___x_411_);
v___x_415_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__4));
v___x_416_ = l_Lean_Expr_isConstOf(v___x_414_, v___x_415_);
if (v___x_416_ == 0)
{
uint8_t v___x_417_; 
lean_dec_ref(v_arg_413_);
v___x_417_ = l_Lean_Expr_isApp(v___x_414_);
if (v___x_417_ == 0)
{
lean_dec_ref(v___x_414_);
return v___x_417_;
}
else
{
lean_object* v_arg_418_; lean_object* v___x_419_; uint8_t v___x_420_; 
v_arg_418_ = lean_ctor_get(v___x_414_, 1);
lean_inc_ref(v_arg_418_);
v___x_419_ = l_Lean_Expr_appFnCleanup___redArg(v___x_414_);
v___x_420_ = l_Lean_Expr_isApp(v___x_419_);
if (v___x_420_ == 0)
{
lean_dec_ref(v___x_419_);
lean_dec_ref(v_arg_418_);
return v___x_420_;
}
else
{
lean_object* v___x_421_; uint8_t v___x_422_; 
v___x_421_ = l_Lean_Expr_appFnCleanup___redArg(v___x_419_);
v___x_422_ = l_Lean_Expr_isApp(v___x_421_);
if (v___x_422_ == 0)
{
lean_dec_ref(v___x_421_);
lean_dec_ref(v_arg_418_);
return v___x_422_;
}
else
{
lean_object* v___x_423_; lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_423_ = l_Lean_Expr_appFnCleanup___redArg(v___x_421_);
v___x_424_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__7));
v___x_425_ = l_Lean_Expr_isConstOf(v___x_423_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__10));
v___x_427_ = l_Lean_Expr_isConstOf(v___x_423_, v___x_426_);
if (v___x_427_ == 0)
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__13));
v___x_429_ = l_Lean_Expr_isConstOf(v___x_423_, v___x_428_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_430_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__16));
v___x_431_ = l_Lean_Expr_isConstOf(v___x_423_, v___x_430_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; uint8_t v___x_433_; 
v___x_432_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19));
v___x_433_ = l_Lean_Expr_isConstOf(v___x_423_, v___x_432_);
lean_dec_ref(v___x_423_);
if (v___x_433_ == 0)
{
lean_dec_ref(v_arg_418_);
return v___x_433_;
}
else
{
uint8_t v___x_434_; 
v___x_434_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(v_arg_418_);
lean_dec_ref(v_arg_418_);
return v___x_434_;
}
}
else
{
uint8_t v___x_435_; 
lean_dec_ref(v___x_423_);
v___x_435_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(v_arg_418_);
lean_dec_ref(v_arg_418_);
return v___x_435_;
}
}
else
{
uint8_t v___x_436_; 
lean_dec_ref(v___x_423_);
v___x_436_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(v_arg_418_);
lean_dec_ref(v_arg_418_);
return v___x_436_;
}
}
else
{
uint8_t v___x_437_; 
lean_dec_ref(v___x_423_);
v___x_437_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(v_arg_418_);
lean_dec_ref(v_arg_418_);
return v___x_437_;
}
}
else
{
uint8_t v___x_438_; 
lean_dec_ref(v___x_423_);
v___x_438_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(v_arg_418_);
lean_dec_ref(v_arg_418_);
return v___x_438_;
}
}
}
}
}
else
{
uint8_t v___x_439_; 
lean_dec_ref(v___x_414_);
v___x_439_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(v_arg_413_);
lean_dec_ref(v_arg_413_);
return v___x_439_;
}
}
}
}
else
{
lean_dec_ref(v___x_407_);
return v___x_409_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatExpr___boxed(lean_object* v_e_440_){
_start:
{
uint8_t v_res_441_; lean_object* v_r_442_; 
v_res_441_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatExpr(v_e_440_);
v_r_442_ = lean_box(v_res_441_);
return v_r_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isNatValue_x3f(lean_object* v_e_443_){
_start:
{
uint8_t v___x_444_; 
lean_inc_ref(v_e_443_);
v___x_444_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatExpr(v_e_443_);
if (v___x_444_ == 0)
{
lean_object* v___x_445_; 
lean_dec_ref(v_e_443_);
v___x_445_ = lean_box(0);
return v___x_445_;
}
else
{
lean_object* v___x_446_; 
v___x_446_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_e_443_);
return v___x_446_;
}
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Offset(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Offset(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Offset(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_LitValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Offset(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Offset(builtin);
}
#ifdef __cplusplus
}
#endif
