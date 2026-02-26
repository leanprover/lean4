// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.ToExpr
// Imports: public import Init.Grind.Ring.CommSemiringAdapter public import Lean.ToExpr
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
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CommRing"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Power"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__3_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__4_value;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__3_value),LEAN_SCALAR_PTR_LITERAL(16, 141, 247, 27, 18, 183, 30, 2)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__4_value),LEAN_SCALAR_PTR_LITERAL(168, 214, 85, 26, 138, 209, 235, 137)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__5_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__6;
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPower(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_ofPower, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__0_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__3_value),LEAN_SCALAR_PTR_LITERAL(16, 141, 247, 27, 18, 183, 30, 2)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprPower;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Mon"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 118, 178, 112, 106, 72, 235)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__1_value),LEAN_SCALAR_PTR_LITERAL(100, 251, 130, 52, 9, 153, 3, 255)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__3;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mult"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 118, 178, 112, 106, 72, 235)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__4_value),LEAN_SCALAR_PTR_LITERAL(55, 131, 127, 87, 57, 224, 125, 17)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofMon(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_ofMon, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 118, 178, 112, 106, 72, 235)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprMon;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Poly"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 149, 121, 227, 179, 241, 101, 21)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(119, 139, 207, 255, 85, 141, 219, 244)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__3;
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__4;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__5 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__5_value;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__6_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__5_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__6_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__7_value;
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__8;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__9;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__10;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__11_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__11_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__13;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__14_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__11_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__14_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__15 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__16;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__18_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__18_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__18_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__18_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 149, 121, 227, 179, 241, 101, 21)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__18_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__17_value),LEAN_SCALAR_PTR_LITERAL(94, 151, 214, 187, 220, 212, 168, 30)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__18 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__18_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__19;
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_ofPoly, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 149, 121, 227, 179, 241, 101, 21)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(99, 190, 53, 58, 106, 245, 204, 195)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__2;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__4_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(253, 68, 252, 101, 77, 40, 4, 69)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__5;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intCast"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__7_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(106, 165, 135, 38, 200, 151, 160, 243)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__7 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__8;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "var"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__9 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__10_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__10_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__10_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(238, 57, 165, 242, 124, 239, 142, 33)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__10 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__11;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__12_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__12_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__12_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__12_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__12_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__6_value),LEAN_SCALAR_PTR_LITERAL(96, 56, 201, 33, 233, 202, 126, 81)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__12 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__12_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__13;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__14_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__14_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__14_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__14_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__14_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__17_value),LEAN_SCALAR_PTR_LITERAL(242, 241, 111, 76, 152, 68, 199, 119)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__14 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__14_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__15;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sub"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__16 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__16_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__17_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__17_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__17_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__17_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__17_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__16_value),LEAN_SCALAR_PTR_LITERAL(233, 86, 87, 90, 25, 204, 73, 66)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__17 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__17_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__18;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mul"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__19 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__19_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__20_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__20_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__20_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__20_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__20_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__19_value),LEAN_SCALAR_PTR_LITERAL(156, 111, 47, 235, 106, 244, 157, 23)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__20 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__20_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__21;
static const lean_string_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pow"};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__22 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__22_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__23_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__23_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__23_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__23_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__23_value_aux_3),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__22_value),LEAN_SCALAR_PTR_LITERAL(123, 249, 64, 127, 207, 177, 28, 229)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__23 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__23_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__24;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__2;
static lean_once_cell_t l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr;
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__5));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPower(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPower___closed__6);
x_5 = l_Lean_mkNatLit(x_2);
x_6 = l_Lean_mkNatLit(x_3);
x_7 = l_Lean_mkAppB(x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__2);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprPower(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprPower___closed__3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__5));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofMon(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__3);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__6, &l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__6_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofMon___closed__6);
x_6 = l_Lean_Meta_Grind_Arith_CommRing_ofPower(x_3);
x_7 = l_Lean_Meta_Grind_Arith_CommRing_ofMon(x_4);
x_8 = l_Lean_mkAppB(x_5, x_6, x_7);
return x_8;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__2);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprMon(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprMon___closed__3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__8);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__9, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__9_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__9);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__7));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__12));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__15));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__19(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__18));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__3);
x_4 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__4);
x_5 = lean_int_dec_le(x_4, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__10);
x_7 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__13, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__13_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__13);
x_8 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__16, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__16_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__16);
x_9 = lean_int_neg(x_2);
lean_dec(x_2);
x_10 = l_Int_toNat(x_9);
lean_dec(x_9);
x_11 = l_Lean_instToExprInt_mkNat(x_10);
x_12 = l_Lean_mkApp3(x_6, x_7, x_8, x_11);
x_13 = l_Lean_Expr_app___override(x_3, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Int_toNat(x_2);
lean_dec(x_2);
x_15 = l_Lean_instToExprInt_mkNat(x_14);
x_16 = l_Lean_Expr_app___override(x_3, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_26; uint8_t x_27; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_19);
lean_dec_ref(x_1);
x_20 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__19, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__19_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__19);
x_26 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__4);
x_27 = lean_int_dec_le(x_26, x_17);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__10);
x_29 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__13, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__13_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__13);
x_30 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__16, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__16_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__16);
x_31 = lean_int_neg(x_17);
lean_dec(x_17);
x_32 = l_Int_toNat(x_31);
lean_dec(x_31);
x_33 = l_Lean_instToExprInt_mkNat(x_32);
x_34 = l_Lean_mkApp3(x_28, x_29, x_30, x_33);
x_21 = x_34;
goto block_25;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = l_Int_toNat(x_17);
lean_dec(x_17);
x_36 = l_Lean_instToExprInt_mkNat(x_35);
x_21 = x_36;
goto block_25;
}
block_25:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = l_Lean_Meta_Grind_Arith_CommRing_ofMon(x_18);
x_23 = l_Lean_Meta_Grind_Arith_CommRing_ofPoly(x_19);
x_24 = l_Lean_mkApp3(x_20, x_21, x_22, x_23);
return x_24;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__2);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly___closed__3);
return x_1;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__7));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__10));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__12));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__14));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__18(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__17));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__21(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__20));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__24(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__23));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec_ref(x_1);
x_3 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__2);
x_4 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__4);
x_5 = lean_int_dec_le(x_4, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__10);
x_7 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__13, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__13_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__13);
x_8 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__16, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__16_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__16);
x_9 = lean_int_neg(x_2);
lean_dec(x_2);
x_10 = l_Int_toNat(x_9);
lean_dec(x_9);
x_11 = l_Lean_instToExprInt_mkNat(x_10);
x_12 = l_Lean_mkApp3(x_6, x_7, x_8, x_11);
x_13 = l_Lean_Expr_app___override(x_3, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Int_toNat(x_2);
lean_dec(x_2);
x_15 = l_Lean_instToExprInt_mkNat(x_14);
x_16 = l_Lean_Expr_app___override(x_3, x_15);
return x_16;
}
}
case 1:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_dec_ref(x_1);
x_18 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__5, &l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__5_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__5);
x_19 = l_Lean_mkNatLit(x_17);
x_20 = l_Lean_Expr_app___override(x_18, x_19);
return x_20;
}
case 2:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec_ref(x_1);
x_22 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__8, &l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__8_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__8);
x_23 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__4, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__4_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__4);
x_24 = lean_int_dec_le(x_23, x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__10, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__10_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__10);
x_26 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__13, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__13_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__13);
x_27 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__16, &l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__16_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofPoly___closed__16);
x_28 = lean_int_neg(x_21);
lean_dec(x_21);
x_29 = l_Int_toNat(x_28);
lean_dec(x_28);
x_30 = l_Lean_instToExprInt_mkNat(x_29);
x_31 = l_Lean_mkApp3(x_25, x_26, x_27, x_30);
x_32 = l_Lean_Expr_app___override(x_22, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Int_toNat(x_21);
lean_dec(x_21);
x_34 = l_Lean_instToExprInt_mkNat(x_33);
x_35 = l_Lean_Expr_app___override(x_22, x_34);
return x_35;
}
}
case 3:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
lean_dec_ref(x_1);
x_37 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__11, &l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__11_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__11);
x_38 = l_Lean_mkNatLit(x_36);
x_39 = l_Lean_Expr_app___override(x_37, x_38);
return x_39;
}
case 4:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_40);
lean_dec_ref(x_1);
x_41 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__13, &l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__13_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__13);
x_42 = l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(x_40);
x_43 = l_Lean_Expr_app___override(x_41, x_42);
return x_43;
}
case 5:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_45);
lean_dec_ref(x_1);
x_46 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__15, &l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__15_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__15);
x_47 = l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(x_44);
x_48 = l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(x_45);
x_49 = l_Lean_mkAppB(x_46, x_47, x_48);
return x_49;
}
case 6:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_50);
x_51 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_51);
lean_dec_ref(x_1);
x_52 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__18, &l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__18_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__18);
x_53 = l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(x_50);
x_54 = l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(x_51);
x_55 = l_Lean_mkAppB(x_52, x_53, x_54);
return x_55;
}
case 7:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_56);
x_57 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_57);
lean_dec_ref(x_1);
x_58 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__21, &l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__21_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__21);
x_59 = l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(x_56);
x_60 = l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(x_57);
x_61 = l_Lean_mkAppB(x_58, x_59, x_60);
return x_61;
}
default: 
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_62 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_62);
x_63 = lean_ctor_get(x_1, 1);
lean_inc(x_63);
lean_dec_ref(x_1);
x_64 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__24, &l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__24_once, _init_l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr___closed__24);
x_65 = l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(x_62);
x_66 = l_Lean_mkNatLit(x_63);
x_67 = l_Lean_mkAppB(x_64, x_65, x_66);
return x_67;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__2, &l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__2_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__2);
x_2 = ((lean_object*)(l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__3, &l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__3_once, _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr___closed__3);
return x_1;
}
}
lean_object* initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin);
lean_object* initialize_Lean_ToExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_ToExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_CommRing_instToExprPower = _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprPower();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instToExprPower);
l_Lean_Meta_Grind_Arith_CommRing_instToExprMon = _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprMon();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instToExprMon);
l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly = _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly);
l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr = _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
