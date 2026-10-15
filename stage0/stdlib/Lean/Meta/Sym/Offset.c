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
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Meta_Sym_getNatValue_x3f(lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorIdx___impl___boxed(lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isQuasiOffset(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isQuasiOffset___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isOffset_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_toOffset(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatExpr___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isNatValue_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Lean_Meta_Sym_Offset_ctorIdx___impl(v_x_3_);
lean_dec_ref(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
lean_object* v_k_7_; lean_object* v___x_8_; 
v_k_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_k_7_);
lean_dec_ref_known(v_t_5_, 1);
v___x_8_ = lean_apply_1(v_k_6_, v_k_7_);
return v___x_8_;
}
else
{
lean_object* v_e_9_; lean_object* v_k_10_; lean_object* v___x_11_; 
v_e_9_ = lean_ctor_get(v_t_5_, 0);
lean_inc_ref(v_e_9_);
v_k_10_ = lean_ctor_get(v_t_5_, 1);
lean_inc(v_k_10_);
lean_dec_ref_known(v_t_5_, 2);
v___x_11_ = lean_apply_2(v_k_6_, v_e_9_, v_k_10_);
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim(lean_object* v_motive_12_, lean_object* v_ctorIdx_13_, lean_object* v_t_14_, lean_object* v_h_15_, lean_object* v_k_16_){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_14_, v_k_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_ctorElim___boxed(lean_object* v_motive_18_, lean_object* v_ctorIdx_19_, lean_object* v_t_20_, lean_object* v_h_21_, lean_object* v_k_22_){
_start:
{
lean_object* v_res_23_; 
v_res_23_ = l_Lean_Meta_Sym_Offset_ctorElim(v_motive_18_, v_ctorIdx_19_, v_t_20_, v_h_21_, v_k_22_);
lean_dec(v_ctorIdx_19_);
return v_res_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_num_elim___redArg(lean_object* v_t_24_, lean_object* v_num_25_){
_start:
{
lean_object* v___x_26_; 
v___x_26_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_24_, v_num_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_num_elim(lean_object* v_motive_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_num_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_28_, v_num_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_add_elim___redArg(lean_object* v_t_32_, lean_object* v_add_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_32_, v_add_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_add_elim(lean_object* v_motive_35_, lean_object* v_t_36_, lean_object* v_h_37_, lean_object* v_add_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Lean_Meta_Sym_Offset_ctorElim___redArg(v_t_36_, v_add_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_inc(lean_object* v_x_44_, lean_object* v_x_45_){
_start:
{
if (lean_obj_tag(v_x_44_) == 0)
{
lean_object* v_k_46_; lean_object* v___x_48_; uint8_t v_isShared_49_; uint8_t v_isSharedCheck_54_; 
v_k_46_ = lean_ctor_get(v_x_44_, 0);
v_isSharedCheck_54_ = !lean_is_exclusive(v_x_44_);
if (v_isSharedCheck_54_ == 0)
{
v___x_48_ = v_x_44_;
v_isShared_49_ = v_isSharedCheck_54_;
goto v_resetjp_47_;
}
else
{
lean_inc(v_k_46_);
lean_dec(v_x_44_);
v___x_48_ = lean_box(0);
v_isShared_49_ = v_isSharedCheck_54_;
goto v_resetjp_47_;
}
v_resetjp_47_:
{
lean_object* v___x_50_; lean_object* v___x_52_; 
v___x_50_ = lean_nat_add(v_k_46_, v_x_45_);
lean_dec(v_k_46_);
if (v_isShared_49_ == 0)
{
lean_ctor_set(v___x_48_, 0, v___x_50_);
v___x_52_ = v___x_48_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_50_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
else
{
lean_object* v_e_55_; lean_object* v_k_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_64_; 
v_e_55_ = lean_ctor_get(v_x_44_, 0);
v_k_56_ = lean_ctor_get(v_x_44_, 1);
v_isSharedCheck_64_ = !lean_is_exclusive(v_x_44_);
if (v_isSharedCheck_64_ == 0)
{
v___x_58_ = v_x_44_;
v_isShared_59_ = v_isSharedCheck_64_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_k_56_);
lean_inc(v_e_55_);
lean_dec(v_x_44_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_64_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_60_ = lean_nat_add(v_k_56_, v_x_45_);
lean_dec(v_k_56_);
if (v_isShared_59_ == 0)
{
lean_ctor_set(v___x_58_, 1, v___x_60_);
v___x_62_ = v___x_58_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_63_; 
v_reuseFailAlloc_63_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_63_, 0, v_e_55_);
lean_ctor_set(v_reuseFailAlloc_63_, 1, v___x_60_);
v___x_62_ = v_reuseFailAlloc_63_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
return v___x_62_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Offset_inc___boxed(lean_object* v_x_65_, lean_object* v_x_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_Lean_Meta_Sym_Offset_inc(v_x_65_, v_x_66_);
lean_dec(v_x_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit(lean_object* v_e_106_){
_start:
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = l_Lean_Expr_cleanupAnnotations(v_e_106_);
v___x_108_ = l_Lean_Expr_isApp(v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
lean_dec_ref(v___x_107_);
v___x_109_ = lean_box(0);
return v___x_109_;
}
else
{
lean_object* v_arg_110_; lean_object* v___x_111_; lean_object* v___x_112_; uint8_t v___x_113_; 
v_arg_110_ = lean_ctor_get(v___x_107_, 1);
lean_inc_ref(v_arg_110_);
v___x_111_ = l_Lean_Expr_appFnCleanup___redArg(v___x_107_);
v___x_112_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__1));
v___x_113_ = l_Lean_Expr_isConstOf(v___x_111_, v___x_112_);
if (v___x_113_ == 0)
{
uint8_t v___x_114_; 
v___x_114_ = l_Lean_Expr_isApp(v___x_111_);
if (v___x_114_ == 0)
{
lean_object* v___x_115_; 
lean_dec_ref(v___x_111_);
lean_dec_ref(v_arg_110_);
v___x_115_ = lean_box(0);
return v___x_115_;
}
else
{
lean_object* v_arg_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v_arg_116_ = lean_ctor_get(v___x_111_, 1);
lean_inc_ref(v_arg_116_);
v___x_117_ = l_Lean_Expr_appFnCleanup___redArg(v___x_111_);
v___x_118_ = l_Lean_Expr_isApp(v___x_117_);
if (v___x_118_ == 0)
{
lean_object* v___x_119_; 
lean_dec_ref(v___x_117_);
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_arg_110_);
v___x_119_ = lean_box(0);
return v___x_119_;
}
else
{
lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_120_ = l_Lean_Expr_appFnCleanup___redArg(v___x_117_);
v___x_121_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__4));
v___x_122_ = l_Lean_Expr_isConstOf(v___x_120_, v___x_121_);
if (v___x_122_ == 0)
{
uint8_t v___x_123_; 
v___x_123_ = l_Lean_Expr_isApp(v___x_120_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; 
lean_dec_ref(v___x_120_);
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_arg_110_);
v___x_124_ = lean_box(0);
return v___x_124_;
}
else
{
lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_125_ = l_Lean_Expr_appFnCleanup___redArg(v___x_120_);
v___x_126_ = l_Lean_Expr_isApp(v___x_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; 
lean_dec_ref(v___x_125_);
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_arg_110_);
v___x_127_ = lean_box(0);
return v___x_127_;
}
else
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = l_Lean_Expr_appFnCleanup___redArg(v___x_125_);
v___x_129_ = l_Lean_Expr_isApp(v___x_128_);
if (v___x_129_ == 0)
{
lean_object* v___x_130_; 
lean_dec_ref(v___x_128_);
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_arg_110_);
v___x_130_ = lean_box(0);
return v___x_130_;
}
else
{
lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_131_ = l_Lean_Expr_appFnCleanup___redArg(v___x_128_);
v___x_132_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__7));
v___x_133_ = l_Lean_Expr_isConstOf(v___x_131_, v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_134_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__10));
v___x_135_ = l_Lean_Expr_isConstOf(v___x_131_, v___x_134_);
if (v___x_135_ == 0)
{
lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_136_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__13));
v___x_137_ = l_Lean_Expr_isConstOf(v___x_131_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_138_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__16));
v___x_139_ = l_Lean_Expr_isConstOf(v___x_131_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_140_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19));
v___x_141_ = l_Lean_Expr_isConstOf(v___x_131_, v___x_140_);
lean_dec_ref(v___x_131_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; 
lean_dec_ref(v_arg_116_);
lean_dec_ref(v_arg_110_);
v___x_142_ = lean_box(0);
return v___x_142_;
}
else
{
lean_object* v___x_143_; 
v___x_143_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_116_);
if (lean_obj_tag(v___x_143_) == 0)
{
lean_dec_ref(v_arg_110_);
return v___x_143_;
}
else
{
lean_object* v_val_144_; lean_object* v___x_145_; 
v_val_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc(v_val_144_);
lean_dec_ref_known(v___x_143_, 1);
v___x_145_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_110_);
if (lean_obj_tag(v___x_145_) == 0)
{
lean_dec(v_val_144_);
return v___x_145_;
}
else
{
lean_object* v_val_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_154_; 
v_val_146_ = lean_ctor_get(v___x_145_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v___x_145_);
if (v_isSharedCheck_154_ == 0)
{
v___x_148_ = v___x_145_;
v_isShared_149_ = v_isSharedCheck_154_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_val_146_);
lean_dec(v___x_145_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_154_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_150_ = lean_nat_add(v_val_144_, v_val_146_);
lean_dec(v_val_146_);
lean_dec(v_val_144_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 0, v___x_150_);
v___x_152_ = v___x_148_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_150_);
v___x_152_ = v_reuseFailAlloc_153_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
return v___x_152_;
}
}
}
}
}
}
else
{
lean_object* v___x_155_; 
lean_dec_ref(v___x_131_);
v___x_155_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_116_);
if (lean_obj_tag(v___x_155_) == 0)
{
lean_dec_ref(v_arg_110_);
return v___x_155_;
}
else
{
lean_object* v_val_156_; lean_object* v___x_157_; 
v_val_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_val_156_);
lean_dec_ref_known(v___x_155_, 1);
v___x_157_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_110_);
if (lean_obj_tag(v___x_157_) == 0)
{
lean_dec(v_val_156_);
return v___x_157_;
}
else
{
lean_object* v_val_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_166_; 
v_val_158_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_166_ == 0)
{
v___x_160_ = v___x_157_;
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_val_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_166_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_164_; 
v___x_162_ = lean_nat_sub(v_val_156_, v_val_158_);
lean_dec(v_val_158_);
lean_dec(v_val_156_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 0, v___x_162_);
v___x_164_ = v___x_160_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v___x_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
}
else
{
lean_object* v___x_167_; 
lean_dec_ref(v___x_131_);
v___x_167_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_116_);
if (lean_obj_tag(v___x_167_) == 0)
{
lean_dec_ref(v_arg_110_);
return v___x_167_;
}
else
{
lean_object* v_val_168_; lean_object* v___x_169_; 
v_val_168_ = lean_ctor_get(v___x_167_, 0);
lean_inc(v_val_168_);
lean_dec_ref_known(v___x_167_, 1);
v___x_169_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_110_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_dec(v_val_168_);
return v___x_169_;
}
else
{
lean_object* v_val_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_178_; 
v_val_170_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_178_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_178_ == 0)
{
v___x_172_ = v___x_169_;
v_isShared_173_ = v_isSharedCheck_178_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_val_170_);
lean_dec(v___x_169_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_178_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_174_; lean_object* v___x_176_; 
v___x_174_ = lean_nat_mul(v_val_168_, v_val_170_);
lean_dec(v_val_170_);
lean_dec(v_val_168_);
if (v_isShared_173_ == 0)
{
lean_ctor_set(v___x_172_, 0, v___x_174_);
v___x_176_ = v___x_172_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
else
{
lean_object* v___x_179_; 
lean_dec_ref(v___x_131_);
v___x_179_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_116_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_dec_ref(v_arg_110_);
return v___x_179_;
}
else
{
lean_object* v_val_180_; lean_object* v___x_181_; 
v_val_180_ = lean_ctor_get(v___x_179_, 0);
lean_inc(v_val_180_);
lean_dec_ref_known(v___x_179_, 1);
v___x_181_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_110_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_dec(v_val_180_);
return v___x_181_;
}
else
{
lean_object* v_val_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_190_; 
v_val_182_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_190_ == 0)
{
v___x_184_ = v___x_181_;
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_val_182_);
lean_dec(v___x_181_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_190_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_186_ = lean_nat_div(v_val_180_, v_val_182_);
lean_dec(v_val_182_);
lean_dec(v_val_180_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_186_);
v___x_188_ = v___x_184_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v___x_186_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
return v___x_188_;
}
}
}
}
}
}
else
{
lean_object* v___x_191_; 
lean_dec_ref(v___x_131_);
v___x_191_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_116_);
if (lean_obj_tag(v___x_191_) == 0)
{
lean_dec_ref(v_arg_110_);
return v___x_191_;
}
else
{
lean_object* v_val_192_; lean_object* v___x_193_; 
v_val_192_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_val_192_);
lean_dec_ref_known(v___x_191_, 1);
v___x_193_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_110_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_dec(v_val_192_);
return v___x_193_;
}
else
{
lean_object* v_val_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_202_; 
v_val_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_202_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_202_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_202_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_val_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_202_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v___x_200_; 
v___x_198_ = lean_nat_mod(v_val_192_, v_val_194_);
lean_dec(v_val_194_);
lean_dec(v_val_192_);
if (v_isShared_197_ == 0)
{
lean_ctor_set(v___x_196_, 0, v___x_198_);
v___x_200_ = v___x_196_;
goto v_reusejp_199_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_198_);
v___x_200_ = v_reuseFailAlloc_201_;
goto v_reusejp_199_;
}
v_reusejp_199_:
{
return v___x_200_;
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
lean_object* v___x_203_; 
lean_dec_ref(v___x_120_);
lean_dec_ref(v_arg_110_);
v___x_203_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_116_);
return v___x_203_;
}
}
}
}
else
{
lean_object* v___x_204_; 
lean_dec_ref(v___x_111_);
v___x_204_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_110_);
if (lean_obj_tag(v___x_204_) == 0)
{
return v___x_204_;
}
else
{
lean_object* v_val_205_; lean_object* v___x_207_; uint8_t v_isShared_208_; uint8_t v_isSharedCheck_214_; 
v_val_205_ = lean_ctor_get(v___x_204_, 0);
v_isSharedCheck_214_ = !lean_is_exclusive(v___x_204_);
if (v_isSharedCheck_214_ == 0)
{
v___x_207_ = v___x_204_;
v_isShared_208_ = v_isSharedCheck_214_;
goto v_resetjp_206_;
}
else
{
lean_inc(v_val_205_);
lean_dec(v___x_204_);
v___x_207_ = lean_box(0);
v_isShared_208_ = v_isSharedCheck_214_;
goto v_resetjp_206_;
}
v_resetjp_206_:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_209_ = lean_unsigned_to_nat(1u);
v___x_210_ = lean_nat_add(v_val_205_, v___x_209_);
lean_dec(v_val_205_);
if (v_isShared_208_ == 0)
{
lean_ctor_set(v___x_207_, 0, v___x_210_);
v___x_212_ = v___x_207_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v___x_210_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(lean_object* v_e_215_){
_start:
{
switch(lean_obj_tag(v_e_215_))
{
case 9:
{
lean_object* v_a_216_; 
v_a_216_ = lean_ctor_get(v_e_215_, 0);
lean_inc_ref(v_a_216_);
lean_dec_ref_known(v_e_215_, 1);
if (lean_obj_tag(v_a_216_) == 0)
{
lean_object* v_val_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
v_val_217_ = lean_ctor_get(v_a_216_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v_a_216_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v_a_216_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_val_217_);
lean_dec(v_a_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
lean_ctor_set_tag(v___x_219_, 1);
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_val_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
else
{
lean_object* v___x_225_; 
lean_dec_ref(v_a_216_);
v___x_225_ = lean_box(0);
return v___x_225_;
}
}
case 10:
{
lean_object* v_expr_226_; 
v_expr_226_ = lean_ctor_get(v_e_215_, 1);
lean_inc_ref(v_expr_226_);
lean_dec_ref_known(v_e_215_, 2);
v_e_215_ = v_expr_226_;
goto _start;
}
case 4:
{
lean_object* v_declName_228_; 
v_declName_228_ = lean_ctor_get(v_e_215_, 0);
lean_inc(v_declName_228_);
lean_dec_ref_known(v_e_215_, 2);
if (lean_obj_tag(v_declName_228_) == 1)
{
lean_object* v_pre_229_; 
v_pre_229_ = lean_ctor_get(v_declName_228_, 0);
lean_inc(v_pre_229_);
if (lean_obj_tag(v_pre_229_) == 1)
{
lean_object* v_pre_230_; 
v_pre_230_ = lean_ctor_get(v_pre_229_, 0);
if (lean_obj_tag(v_pre_230_) == 0)
{
lean_object* v_str_231_; lean_object* v_str_232_; lean_object* v___x_233_; uint8_t v___x_234_; 
v_str_231_ = lean_ctor_get(v_declName_228_, 1);
lean_inc_ref(v_str_231_);
lean_dec_ref_known(v_declName_228_, 2);
v_str_232_ = lean_ctor_get(v_pre_229_, 1);
lean_inc_ref(v_str_232_);
lean_dec_ref_known(v_pre_229_, 2);
v___x_233_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f___closed__0));
v___x_234_ = lean_string_dec_eq(v_str_232_, v___x_233_);
lean_dec_ref(v_str_232_);
if (v___x_234_ == 0)
{
lean_object* v___x_235_; 
lean_dec_ref(v_str_231_);
v___x_235_ = lean_box(0);
return v___x_235_;
}
else
{
lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f___closed__1));
v___x_237_ = lean_string_dec_eq(v_str_231_, v___x_236_);
lean_dec_ref(v_str_231_);
if (v___x_237_ == 0)
{
lean_object* v___x_238_; 
v___x_238_ = lean_box(0);
return v___x_238_;
}
else
{
lean_object* v___x_239_; 
v___x_239_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f___closed__2));
return v___x_239_;
}
}
}
else
{
lean_object* v___x_240_; 
lean_dec_ref_known(v_pre_229_, 2);
lean_dec_ref_known(v_declName_228_, 2);
v___x_240_ = lean_box(0);
return v___x_240_;
}
}
else
{
lean_object* v___x_241_; 
lean_dec(v_pre_229_);
lean_dec_ref_known(v_declName_228_, 2);
v___x_241_ = lean_box(0);
return v___x_241_;
}
}
else
{
lean_object* v___x_242_; 
lean_dec(v_declName_228_);
v___x_242_ = lean_box(0);
return v___x_242_;
}
}
case 5:
{
lean_object* v___x_243_; 
v___x_243_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit(v_e_215_);
return v___x_243_;
}
case 2:
{
lean_object* v___x_244_; 
v___x_244_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit(v_e_215_);
return v___x_244_;
}
default: 
{
lean_object* v___x_245_; 
lean_dec_ref(v_e_215_);
v___x_245_ = lean_box(0);
return v___x_245_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f(lean_object* v_e_248_){
_start:
{
lean_object* v___x_249_; uint8_t v___x_250_; 
v___x_249_ = l_Lean_Expr_cleanupAnnotations(v_e_248_);
v___x_250_ = l_Lean_Expr_isApp(v___x_249_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; 
lean_dec_ref(v___x_249_);
v___x_251_ = lean_box(0);
return v___x_251_;
}
else
{
lean_object* v_arg_252_; lean_object* v___x_253_; lean_object* v___x_254_; uint8_t v___x_255_; 
v_arg_252_ = lean_ctor_get(v___x_249_, 1);
lean_inc_ref(v_arg_252_);
v___x_253_ = l_Lean_Expr_appFnCleanup___redArg(v___x_249_);
v___x_254_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__1));
v___x_255_ = l_Lean_Expr_isConstOf(v___x_253_, v___x_254_);
if (v___x_255_ == 0)
{
uint8_t v___x_256_; 
v___x_256_ = l_Lean_Expr_isApp(v___x_253_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; 
lean_dec_ref(v___x_253_);
lean_dec_ref(v_arg_252_);
v___x_257_ = lean_box(0);
return v___x_257_;
}
else
{
lean_object* v_arg_258_; lean_object* v___x_259_; uint8_t v___x_260_; 
v_arg_258_ = lean_ctor_get(v___x_253_, 1);
lean_inc_ref(v_arg_258_);
v___x_259_ = l_Lean_Expr_appFnCleanup___redArg(v___x_253_);
v___x_260_ = l_Lean_Expr_isApp(v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___x_261_; 
lean_dec_ref(v___x_259_);
lean_dec_ref(v_arg_258_);
lean_dec_ref(v_arg_252_);
v___x_261_ = lean_box(0);
return v___x_261_;
}
else
{
lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_262_ = l_Lean_Expr_appFnCleanup___redArg(v___x_259_);
v___x_263_ = l_Lean_Expr_isApp(v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; 
lean_dec_ref(v___x_262_);
lean_dec_ref(v_arg_258_);
lean_dec_ref(v_arg_252_);
v___x_264_ = lean_box(0);
return v___x_264_;
}
else
{
lean_object* v___x_265_; uint8_t v___x_266_; 
v___x_265_ = l_Lean_Expr_appFnCleanup___redArg(v___x_262_);
v___x_266_ = l_Lean_Expr_isApp(v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
lean_dec_ref(v___x_265_);
lean_dec_ref(v_arg_258_);
lean_dec_ref(v_arg_252_);
v___x_267_ = lean_box(0);
return v___x_267_;
}
else
{
lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = l_Lean_Expr_appFnCleanup___redArg(v___x_265_);
v___x_269_ = l_Lean_Expr_isApp(v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; 
lean_dec_ref(v___x_268_);
lean_dec_ref(v_arg_258_);
lean_dec_ref(v_arg_252_);
v___x_270_ = lean_box(0);
return v___x_270_;
}
else
{
lean_object* v_arg_271_; lean_object* v___x_272_; lean_object* v___x_273_; uint8_t v___x_274_; 
v_arg_271_ = lean_ctor_get(v___x_268_, 1);
lean_inc_ref(v_arg_271_);
v___x_272_ = l_Lean_Expr_appFnCleanup___redArg(v___x_268_);
v___x_273_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19));
v___x_274_ = l_Lean_Expr_isConstOf(v___x_272_, v___x_273_);
lean_dec_ref(v___x_272_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; 
lean_dec_ref(v_arg_271_);
lean_dec_ref(v_arg_258_);
lean_dec_ref(v_arg_252_);
v___x_275_ = lean_box(0);
return v___x_275_;
}
else
{
lean_object* v___x_276_; uint8_t v___x_277_; 
v___x_276_ = ((lean_object*)(l_Lean_Meta_Sym_isOffset_x3f___closed__0));
v___x_277_ = l_Lean_Expr_isConstOf(v_arg_271_, v___x_276_);
lean_dec_ref(v_arg_271_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; 
lean_dec_ref(v_arg_258_);
lean_dec_ref(v_arg_252_);
v___x_278_ = lean_box(0);
return v___x_278_;
}
else
{
lean_object* v___x_279_; 
v___x_279_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_252_);
if (lean_obj_tag(v___x_279_) == 0)
{
lean_object* v___x_280_; 
lean_dec_ref(v_arg_258_);
v___x_280_ = lean_box(0);
return v___x_280_;
}
else
{
lean_object* v_val_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_290_; 
v_val_281_ = lean_ctor_get(v___x_279_, 0);
v_isSharedCheck_290_ = !lean_is_exclusive(v___x_279_);
if (v_isSharedCheck_290_ == 0)
{
v___x_283_ = v___x_279_;
v_isShared_284_ = v_isSharedCheck_290_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_val_281_);
lean_dec(v___x_279_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_290_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_288_; 
v___x_285_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isOffset_x3f_get(v_arg_258_);
v___x_286_ = l_Lean_Meta_Sym_Offset_inc(v___x_285_, v_val_281_);
lean_dec(v_val_281_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_286_);
v___x_288_ = v___x_283_;
goto v_reusejp_287_;
}
else
{
lean_object* v_reuseFailAlloc_289_; 
v_reuseFailAlloc_289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
v___x_288_ = v_reuseFailAlloc_289_;
goto v_reusejp_287_;
}
v_reusejp_287_:
{
return v___x_288_;
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
lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
lean_dec_ref(v___x_253_);
v___x_291_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isOffset_x3f_get(v_arg_252_);
v___x_292_ = lean_unsigned_to_nat(1u);
v___x_293_ = l_Lean_Meta_Sym_Offset_inc(v___x_291_, v___x_292_);
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isOffset_x3f_get(lean_object* v_e_295_){
_start:
{
lean_object* v___x_296_; 
lean_inc_ref(v_e_295_);
v___x_296_ = l_Lean_Meta_Sym_isOffset_x3f(v_e_295_);
if (lean_obj_tag(v___x_296_) == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_298_, 0, v_e_295_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
return v___x_298_;
}
else
{
lean_object* v_val_299_; 
lean_dec_ref(v_e_295_);
v_val_299_ = lean_ctor_get(v___x_296_, 0);
lean_inc(v_val_299_);
lean_dec_ref_known(v___x_296_, 1);
return v_val_299_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f_x27(lean_object* v_declName_300_, lean_object* v_p_301_){
_start:
{
uint8_t v___y_303_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_306_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__1));
v___x_307_ = lean_name_eq(v_declName_300_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19));
v___x_309_ = lean_name_eq(v_declName_300_, v___x_308_);
v___y_303_ = v___x_309_;
goto v___jp_302_;
}
else
{
v___y_303_ = v___x_307_;
goto v___jp_302_;
}
v___jp_302_:
{
if (v___y_303_ == 0)
{
lean_object* v___x_304_; 
lean_dec_ref(v_p_301_);
v___x_304_ = lean_box(0);
return v___x_304_;
}
else
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_Meta_Sym_isOffset_x3f(v_p_301_);
return v___x_305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x3f_x27___boxed(lean_object* v_declName_310_, lean_object* v_p_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l_Lean_Meta_Sym_isOffset_x3f_x27(v_declName_310_, v_p_311_);
lean_dec(v_declName_310_);
return v_res_312_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(lean_object* v_e_313_){
_start:
{
lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_314_ = ((lean_object*)(l_Lean_Meta_Sym_isOffset_x3f___closed__0));
v___x_315_ = l_Lean_Expr_isConstOf(v_e_313_, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType___boxed(lean_object* v_e_316_){
_start:
{
uint8_t v_res_317_; lean_object* v_r_318_; 
v_res_317_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(v_e_316_);
lean_dec_ref(v_e_316_);
v_r_318_ = lean_box(v_res_317_);
return v_r_318_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isOffset(lean_object* v_e_319_){
_start:
{
lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_320_ = l_Lean_Expr_cleanupAnnotations(v_e_319_);
v___x_321_ = l_Lean_Expr_isApp(v___x_320_);
if (v___x_321_ == 0)
{
lean_dec_ref(v___x_320_);
return v___x_321_;
}
else
{
lean_object* v_arg_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; 
v_arg_322_ = lean_ctor_get(v___x_320_, 1);
lean_inc_ref(v_arg_322_);
v___x_323_ = l_Lean_Expr_appFnCleanup___redArg(v___x_320_);
v___x_324_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__1));
v___x_325_ = l_Lean_Expr_isConstOf(v___x_323_, v___x_324_);
if (v___x_325_ == 0)
{
uint8_t v___x_326_; 
v___x_326_ = l_Lean_Expr_isApp(v___x_323_);
if (v___x_326_ == 0)
{
lean_dec_ref(v___x_323_);
lean_dec_ref(v_arg_322_);
return v___x_326_;
}
else
{
lean_object* v___x_327_; uint8_t v___x_328_; 
v___x_327_ = l_Lean_Expr_appFnCleanup___redArg(v___x_323_);
v___x_328_ = l_Lean_Expr_isApp(v___x_327_);
if (v___x_328_ == 0)
{
lean_dec_ref(v___x_327_);
lean_dec_ref(v_arg_322_);
return v___x_328_;
}
else
{
lean_object* v___x_329_; uint8_t v___x_330_; 
v___x_329_ = l_Lean_Expr_appFnCleanup___redArg(v___x_327_);
v___x_330_ = l_Lean_Expr_isApp(v___x_329_);
if (v___x_330_ == 0)
{
lean_dec_ref(v___x_329_);
lean_dec_ref(v_arg_322_);
return v___x_330_;
}
else
{
lean_object* v___x_331_; uint8_t v___x_332_; 
v___x_331_ = l_Lean_Expr_appFnCleanup___redArg(v___x_329_);
v___x_332_ = l_Lean_Expr_isApp(v___x_331_);
if (v___x_332_ == 0)
{
lean_dec_ref(v___x_331_);
lean_dec_ref(v_arg_322_);
return v___x_332_;
}
else
{
lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_333_ = l_Lean_Expr_appFnCleanup___redArg(v___x_331_);
v___x_334_ = l_Lean_Expr_isApp(v___x_333_);
if (v___x_334_ == 0)
{
lean_dec_ref(v___x_333_);
lean_dec_ref(v_arg_322_);
return v___x_334_;
}
else
{
lean_object* v_arg_335_; lean_object* v___x_336_; lean_object* v___x_337_; uint8_t v___x_338_; 
v_arg_335_ = lean_ctor_get(v___x_333_, 1);
lean_inc_ref(v_arg_335_);
v___x_336_ = l_Lean_Expr_appFnCleanup___redArg(v___x_333_);
v___x_337_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19));
v___x_338_ = l_Lean_Expr_isConstOf(v___x_336_, v___x_337_);
lean_dec_ref(v___x_336_);
if (v___x_338_ == 0)
{
lean_dec_ref(v_arg_335_);
lean_dec_ref(v_arg_322_);
return v___x_338_;
}
else
{
uint8_t v___x_339_; 
v___x_339_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(v_arg_335_);
lean_dec_ref(v_arg_335_);
if (v___x_339_ == 0)
{
lean_dec_ref(v_arg_322_);
return v___x_339_;
}
else
{
lean_object* v___x_340_; 
v___x_340_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_arg_322_);
if (lean_obj_tag(v___x_340_) == 0)
{
return v___x_325_;
}
else
{
lean_dec_ref_known(v___x_340_, 1);
return v___x_339_;
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
lean_dec_ref(v___x_323_);
lean_dec_ref(v_arg_322_);
return v___x_325_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset___boxed(lean_object* v_e_341_){
_start:
{
uint8_t v_res_342_; lean_object* v_r_343_; 
v_res_342_ = l_Lean_Meta_Sym_isOffset(v_e_341_);
v_r_343_ = lean_box(v_res_342_);
return v_r_343_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isQuasiOffset(lean_object* v_p_344_){
_start:
{
lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_345_ = l_Lean_Expr_cleanupAnnotations(v_p_344_);
v___x_346_ = l_Lean_Expr_isApp(v___x_345_);
if (v___x_346_ == 0)
{
lean_dec_ref(v___x_345_);
return v___x_346_;
}
else
{
lean_object* v_arg_347_; lean_object* v___x_348_; uint8_t v___x_349_; 
v_arg_347_ = lean_ctor_get(v___x_345_, 1);
lean_inc_ref(v_arg_347_);
v___x_348_ = l_Lean_Expr_appFnCleanup___redArg(v___x_345_);
v___x_349_ = l_Lean_Expr_isApp(v___x_348_);
if (v___x_349_ == 0)
{
lean_dec_ref(v___x_348_);
lean_dec_ref(v_arg_347_);
return v___x_349_;
}
else
{
lean_object* v___x_350_; uint8_t v___x_351_; 
v___x_350_ = l_Lean_Expr_appFnCleanup___redArg(v___x_348_);
v___x_351_ = l_Lean_Expr_isApp(v___x_350_);
if (v___x_351_ == 0)
{
lean_dec_ref(v___x_350_);
lean_dec_ref(v_arg_347_);
return v___x_351_;
}
else
{
lean_object* v___x_352_; uint8_t v___x_353_; 
v___x_352_ = l_Lean_Expr_appFnCleanup___redArg(v___x_350_);
v___x_353_ = l_Lean_Expr_isApp(v___x_352_);
if (v___x_353_ == 0)
{
lean_dec_ref(v___x_352_);
lean_dec_ref(v_arg_347_);
return v___x_353_;
}
else
{
lean_object* v___x_354_; uint8_t v___x_355_; 
v___x_354_ = l_Lean_Expr_appFnCleanup___redArg(v___x_352_);
v___x_355_ = l_Lean_Expr_isApp(v___x_354_);
if (v___x_355_ == 0)
{
lean_dec_ref(v___x_354_);
lean_dec_ref(v_arg_347_);
return v___x_355_;
}
else
{
lean_object* v___x_356_; uint8_t v___x_357_; 
v___x_356_ = l_Lean_Expr_appFnCleanup___redArg(v___x_354_);
v___x_357_ = l_Lean_Expr_isApp(v___x_356_);
if (v___x_357_ == 0)
{
lean_dec_ref(v___x_356_);
lean_dec_ref(v_arg_347_);
return v___x_357_;
}
else
{
lean_object* v_arg_358_; lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v_arg_358_ = lean_ctor_get(v___x_356_, 1);
lean_inc_ref(v_arg_358_);
v___x_359_ = l_Lean_Expr_appFnCleanup___redArg(v___x_356_);
v___x_360_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19));
v___x_361_ = l_Lean_Expr_isConstOf(v___x_359_, v___x_360_);
lean_dec_ref(v___x_359_);
if (v___x_361_ == 0)
{
lean_dec_ref(v_arg_358_);
lean_dec_ref(v_arg_347_);
return v___x_361_;
}
else
{
uint8_t v___x_362_; 
v___x_362_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(v_arg_358_);
lean_dec_ref(v_arg_358_);
if (v___x_362_ == 0)
{
lean_dec_ref(v_arg_347_);
return v___x_362_;
}
else
{
uint8_t v___x_363_; 
v___x_363_ = l_Lean_Expr_hasLooseBVars(v_arg_347_);
lean_dec_ref(v_arg_347_);
return v___x_363_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isQuasiOffset___boxed(lean_object* v_p_364_){
_start:
{
uint8_t v_res_365_; lean_object* v_r_366_; 
v_res_365_ = l_Lean_Meta_Sym_isQuasiOffset(v_p_364_);
v_r_366_ = lean_box(v_res_365_);
return v_r_366_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Sym_isOffset_x27(lean_object* v_declName_367_, lean_object* v_p_368_){
_start:
{
uint8_t v___y_370_; lean_object* v___x_372_; uint8_t v___x_373_; 
v___x_372_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__1));
v___x_373_ = lean_name_eq(v_declName_367_, v___x_372_);
if (v___x_373_ == 0)
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19));
v___x_375_ = lean_name_eq(v_declName_367_, v___x_374_);
v___y_370_ = v___x_375_;
goto v___jp_369_;
}
else
{
v___y_370_ = v___x_373_;
goto v___jp_369_;
}
v___jp_369_:
{
if (v___y_370_ == 0)
{
lean_dec_ref(v_p_368_);
return v___y_370_;
}
else
{
uint8_t v___x_371_; 
v___x_371_ = l_Lean_Meta_Sym_isOffset(v_p_368_);
return v___x_371_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isOffset_x27___boxed(lean_object* v_declName_376_, lean_object* v_p_377_){
_start:
{
uint8_t v_res_378_; lean_object* v_r_379_; 
v_res_378_ = l_Lean_Meta_Sym_isOffset_x27(v_declName_376_, v_p_377_);
lean_dec(v_declName_376_);
v_r_379_ = lean_box(v_res_378_);
return v_r_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_toOffset(lean_object* v_e_380_){
_start:
{
lean_object* v___x_387_; uint8_t v___x_388_; 
lean_inc_ref(v_e_380_);
v___x_387_ = l_Lean_Expr_cleanupAnnotations(v_e_380_);
v___x_388_ = l_Lean_Expr_isApp(v___x_387_);
if (v___x_388_ == 0)
{
lean_dec_ref(v___x_387_);
goto v___jp_381_;
}
else
{
lean_object* v_arg_389_; lean_object* v___x_390_; lean_object* v___x_391_; uint8_t v___x_392_; 
v_arg_389_ = lean_ctor_get(v___x_387_, 1);
lean_inc_ref(v_arg_389_);
v___x_390_ = l_Lean_Expr_appFnCleanup___redArg(v___x_387_);
v___x_391_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__1));
v___x_392_ = l_Lean_Expr_isConstOf(v___x_390_, v___x_391_);
if (v___x_392_ == 0)
{
uint8_t v___x_393_; 
v___x_393_ = l_Lean_Expr_isApp(v___x_390_);
if (v___x_393_ == 0)
{
lean_dec_ref(v___x_390_);
lean_dec_ref(v_arg_389_);
goto v___jp_381_;
}
else
{
lean_object* v_arg_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v_arg_394_ = lean_ctor_get(v___x_390_, 1);
lean_inc_ref(v_arg_394_);
v___x_395_ = l_Lean_Expr_appFnCleanup___redArg(v___x_390_);
v___x_396_ = l_Lean_Expr_isApp(v___x_395_);
if (v___x_396_ == 0)
{
lean_dec_ref(v___x_395_);
lean_dec_ref(v_arg_394_);
lean_dec_ref(v_arg_389_);
goto v___jp_381_;
}
else
{
lean_object* v___x_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_397_ = l_Lean_Expr_appFnCleanup___redArg(v___x_395_);
v___x_398_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__4));
v___x_399_ = l_Lean_Expr_isConstOf(v___x_397_, v___x_398_);
if (v___x_399_ == 0)
{
uint8_t v___x_400_; 
v___x_400_ = l_Lean_Expr_isApp(v___x_397_);
if (v___x_400_ == 0)
{
lean_dec_ref(v___x_397_);
lean_dec_ref(v_arg_394_);
lean_dec_ref(v_arg_389_);
goto v___jp_381_;
}
else
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = l_Lean_Expr_appFnCleanup___redArg(v___x_397_);
v___x_402_ = l_Lean_Expr_isApp(v___x_401_);
if (v___x_402_ == 0)
{
lean_dec_ref(v___x_401_);
lean_dec_ref(v_arg_394_);
lean_dec_ref(v_arg_389_);
goto v___jp_381_;
}
else
{
lean_object* v___x_403_; uint8_t v___x_404_; 
v___x_403_ = l_Lean_Expr_appFnCleanup___redArg(v___x_401_);
v___x_404_ = l_Lean_Expr_isApp(v___x_403_);
if (v___x_404_ == 0)
{
lean_dec_ref(v___x_403_);
lean_dec_ref(v_arg_394_);
lean_dec_ref(v_arg_389_);
goto v___jp_381_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_405_ = l_Lean_Expr_appFnCleanup___redArg(v___x_403_);
v___x_406_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19));
v___x_407_ = l_Lean_Expr_isConstOf(v___x_405_, v___x_406_);
lean_dec_ref(v___x_405_);
if (v___x_407_ == 0)
{
lean_dec_ref(v_arg_394_);
lean_dec_ref(v_arg_389_);
goto v___jp_381_;
}
else
{
lean_object* v___x_408_; 
v___x_408_ = l_Lean_Meta_Sym_getNatValue_x3f(v_arg_389_);
if (lean_obj_tag(v___x_408_) == 1)
{
lean_object* v_val_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec_ref(v_e_380_);
v_val_409_ = lean_ctor_get(v___x_408_, 0);
lean_inc(v_val_409_);
lean_dec_ref_known(v___x_408_, 1);
v___x_410_ = l_Lean_Meta_Sym_toOffset(v_arg_394_);
v___x_411_ = l_Lean_Meta_Sym_Offset_inc(v___x_410_, v_val_409_);
lean_dec(v_val_409_);
return v___x_411_;
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; 
lean_dec(v___x_408_);
lean_dec_ref(v_arg_394_);
v___x_412_ = lean_unsigned_to_nat(0u);
v___x_413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_413_, 0, v_e_380_);
lean_ctor_set(v___x_413_, 1, v___x_412_);
return v___x_413_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_397_);
lean_dec_ref(v_arg_389_);
if (lean_obj_tag(v_arg_394_) == 9)
{
lean_object* v_a_414_; 
v_a_414_ = lean_ctor_get(v_arg_394_, 0);
lean_inc_ref(v_a_414_);
lean_dec_ref_known(v_arg_394_, 1);
if (lean_obj_tag(v_a_414_) == 0)
{
lean_object* v_val_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_422_; 
lean_dec_ref(v_e_380_);
v_val_415_ = lean_ctor_get(v_a_414_, 0);
v_isSharedCheck_422_ = !lean_is_exclusive(v_a_414_);
if (v_isSharedCheck_422_ == 0)
{
v___x_417_ = v_a_414_;
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_val_415_);
lean_dec(v_a_414_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_422_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_420_; 
if (v_isShared_418_ == 0)
{
v___x_420_ = v___x_417_;
goto v_reusejp_419_;
}
else
{
lean_object* v_reuseFailAlloc_421_; 
v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_421_, 0, v_val_415_);
v___x_420_ = v_reuseFailAlloc_421_;
goto v_reusejp_419_;
}
v_reusejp_419_:
{
return v___x_420_;
}
}
}
else
{
lean_dec_ref(v_a_414_);
goto v___jp_384_;
}
}
else
{
lean_dec_ref(v_arg_394_);
goto v___jp_384_;
}
}
}
}
}
else
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec_ref(v___x_390_);
lean_dec_ref(v_e_380_);
v___x_423_ = l_Lean_Meta_Sym_toOffset(v_arg_389_);
v___x_424_ = lean_unsigned_to_nat(1u);
v___x_425_ = l_Lean_Meta_Sym_Offset_inc(v___x_423_, v___x_424_);
return v___x_425_;
}
}
v___jp_381_:
{
lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_382_ = lean_unsigned_to_nat(0u);
v___x_383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_383_, 0, v_e_380_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
return v___x_383_;
}
v___jp_384_:
{
lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_385_ = lean_unsigned_to_nat(0u);
v___x_386_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_386_, 0, v_e_380_);
lean_ctor_set(v___x_386_, 1, v___x_385_);
return v___x_386_;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatExpr(lean_object* v_e_426_){
_start:
{
lean_object* v___x_427_; uint8_t v___x_428_; 
v___x_427_ = l_Lean_Expr_cleanupAnnotations(v_e_426_);
v___x_428_ = l_Lean_Expr_isApp(v___x_427_);
if (v___x_428_ == 0)
{
lean_dec_ref(v___x_427_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; uint8_t v___x_431_; 
v___x_429_ = l_Lean_Expr_appFnCleanup___redArg(v___x_427_);
v___x_430_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__1));
v___x_431_ = l_Lean_Expr_isConstOf(v___x_429_, v___x_430_);
if (v___x_431_ == 0)
{
uint8_t v___x_432_; 
v___x_432_ = l_Lean_Expr_isApp(v___x_429_);
if (v___x_432_ == 0)
{
lean_dec_ref(v___x_429_);
return v___x_432_;
}
else
{
lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = l_Lean_Expr_appFnCleanup___redArg(v___x_429_);
v___x_434_ = l_Lean_Expr_isApp(v___x_433_);
if (v___x_434_ == 0)
{
lean_dec_ref(v___x_433_);
return v___x_434_;
}
else
{
lean_object* v_arg_435_; lean_object* v___x_436_; lean_object* v___x_437_; uint8_t v___x_438_; 
v_arg_435_ = lean_ctor_get(v___x_433_, 1);
lean_inc_ref(v_arg_435_);
v___x_436_ = l_Lean_Expr_appFnCleanup___redArg(v___x_433_);
v___x_437_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__4));
v___x_438_ = l_Lean_Expr_isConstOf(v___x_436_, v___x_437_);
if (v___x_438_ == 0)
{
uint8_t v___x_439_; 
lean_dec_ref(v_arg_435_);
v___x_439_ = l_Lean_Expr_isApp(v___x_436_);
if (v___x_439_ == 0)
{
lean_dec_ref(v___x_436_);
return v___x_439_;
}
else
{
lean_object* v_arg_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v_arg_440_ = lean_ctor_get(v___x_436_, 1);
lean_inc_ref(v_arg_440_);
v___x_441_ = l_Lean_Expr_appFnCleanup___redArg(v___x_436_);
v___x_442_ = l_Lean_Expr_isApp(v___x_441_);
if (v___x_442_ == 0)
{
lean_dec_ref(v___x_441_);
lean_dec_ref(v_arg_440_);
return v___x_442_;
}
else
{
lean_object* v___x_443_; uint8_t v___x_444_; 
v___x_443_ = l_Lean_Expr_appFnCleanup___redArg(v___x_441_);
v___x_444_ = l_Lean_Expr_isApp(v___x_443_);
if (v___x_444_ == 0)
{
lean_dec_ref(v___x_443_);
lean_dec_ref(v_arg_440_);
return v___x_444_;
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_445_ = l_Lean_Expr_appFnCleanup___redArg(v___x_443_);
v___x_446_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__7));
v___x_447_ = l_Lean_Expr_isConstOf(v___x_445_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; uint8_t v___x_449_; 
v___x_448_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__10));
v___x_449_ = l_Lean_Expr_isConstOf(v___x_445_, v___x_448_);
if (v___x_449_ == 0)
{
lean_object* v___x_450_; uint8_t v___x_451_; 
v___x_450_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__13));
v___x_451_ = l_Lean_Expr_isConstOf(v___x_445_, v___x_450_);
if (v___x_451_ == 0)
{
lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_452_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__16));
v___x_453_ = l_Lean_Expr_isConstOf(v___x_445_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = ((lean_object*)(l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f_visit___closed__19));
v___x_455_ = l_Lean_Expr_isConstOf(v___x_445_, v___x_454_);
lean_dec_ref(v___x_445_);
if (v___x_455_ == 0)
{
lean_dec_ref(v_arg_440_);
return v___x_455_;
}
else
{
uint8_t v___x_456_; 
v___x_456_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(v_arg_440_);
lean_dec_ref(v_arg_440_);
return v___x_456_;
}
}
else
{
uint8_t v___x_457_; 
lean_dec_ref(v___x_445_);
v___x_457_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(v_arg_440_);
lean_dec_ref(v_arg_440_);
return v___x_457_;
}
}
else
{
uint8_t v___x_458_; 
lean_dec_ref(v___x_445_);
v___x_458_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(v_arg_440_);
lean_dec_ref(v_arg_440_);
return v___x_458_;
}
}
else
{
uint8_t v___x_459_; 
lean_dec_ref(v___x_445_);
v___x_459_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(v_arg_440_);
lean_dec_ref(v_arg_440_);
return v___x_459_;
}
}
else
{
uint8_t v___x_460_; 
lean_dec_ref(v___x_445_);
v___x_460_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(v_arg_440_);
lean_dec_ref(v_arg_440_);
return v___x_460_;
}
}
}
}
}
else
{
uint8_t v___x_461_; 
lean_dec_ref(v___x_436_);
v___x_461_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatType(v_arg_435_);
lean_dec_ref(v_arg_435_);
return v___x_461_;
}
}
}
}
else
{
lean_dec_ref(v___x_429_);
return v___x_431_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatExpr___boxed(lean_object* v_e_462_){
_start:
{
uint8_t v_res_463_; lean_object* v_r_464_; 
v_res_463_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatExpr(v_e_462_);
v_r_464_ = lean_box(v_res_463_);
return v_r_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_isNatValue_x3f(lean_object* v_e_465_){
_start:
{
uint8_t v___x_466_; 
lean_inc_ref(v_e_465_);
v___x_466_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_isNatExpr(v_e_465_);
if (v___x_466_ == 0)
{
lean_object* v___x_467_; 
lean_dec_ref(v_e_465_);
v___x_467_ = lean_box(0);
return v___x_467_;
}
else
{
lean_object* v___x_468_; 
v___x_468_ = l___private_Lean_Meta_Sym_Offset_0__Lean_Meta_Sym_evalNat_x3f(v_e_465_);
return v___x_468_;
}
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_LitValues(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Offset(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
