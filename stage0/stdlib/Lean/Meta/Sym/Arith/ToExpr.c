// Lean compiler output
// Module: Lean.Meta.Sym.Arith.ToExpr
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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_Arith_mkIntLitK___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_mkIntLitK___closed__0;
static const lean_string_object l_Lean_Meta_Sym_Arith_mkIntLitK___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_Meta_Sym_Arith_mkIntLitK___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkIntLitK___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_mkIntLitK___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_Meta_Sym_Arith_mkIntLitK___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkIntLitK___closed__2_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_mkIntLitK___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_mkIntLitK___closed__1_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_mkIntLitK___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_mkIntLitK___closed__3_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_mkIntLitK___closed__2_value),LEAN_SCALAR_PTR_LITERAL(192, 66, 133, 102, 95, 170, 134, 92)}};
static const lean_object* l_Lean_Meta_Sym_Arith_mkIntLitK___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkIntLitK___closed__3_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_mkIntLitK___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_mkIntLitK___closed__4;
static const lean_string_object l_Lean_Meta_Sym_Arith_mkIntLitK___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "negSucc"};
static const lean_object* l_Lean_Meta_Sym_Arith_mkIntLitK___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkIntLitK___closed__5_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_mkIntLitK___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_mkIntLitK___closed__1_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_mkIntLitK___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_mkIntLitK___closed__6_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_mkIntLitK___closed__5_value),LEAN_SCALAR_PTR_LITERAL(181, 236, 205, 0, 179, 53, 99, 201)}};
static const lean_object* l_Lean_Meta_Sym_Arith_mkIntLitK___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Arith_mkIntLitK___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_mkIntLitK___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_mkIntLitK___closed__7;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_mkIntLitK(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_mkIntLitK___boxed(lean_object*);
static const lean_string_object l_Lean_Meta_Sym_Arith_ofPower___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_Sym_Arith_ofPower___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_ofPower___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Grind"};
static const lean_object* l_Lean_Meta_Sym_Arith_ofPower___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__1_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_ofPower___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "CommRing"};
static const lean_object* l_Lean_Meta_Sym_Arith_ofPower___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__2_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_ofPower___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Power"};
static const lean_object* l_Lean_Meta_Sym_Arith_ofPower___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__3_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_ofPower___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Meta_Sym_Arith_ofPower___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofPower___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofPower___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofPower___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofPower___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__3_value),LEAN_SCALAR_PTR_LITERAL(16, 141, 247, 27, 18, 183, 30, 2)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofPower___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__4_value),LEAN_SCALAR_PTR_LITERAL(168, 214, 85, 26, 138, 209, 235, 137)}};
static const lean_object* l_Lean_Meta_Sym_Arith_ofPower___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_ofPower___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_ofPower___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ofPower(lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Arith_instToExprPower___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Arith_ofPower, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Arith_instToExprPower___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_instToExprPower___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_instToExprPower___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_instToExprPower___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_instToExprPower___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_instToExprPower___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_instToExprPower___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_instToExprPower___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_instToExprPower___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__3_value),LEAN_SCALAR_PTR_LITERAL(16, 141, 247, 27, 18, 183, 30, 2)}};
static const lean_object* l_Lean_Meta_Sym_Arith_instToExprPower___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_instToExprPower___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_instToExprPower___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_instToExprPower___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_instToExprPower___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_instToExprPower___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instToExprPower;
static const lean_string_object l_Lean_Meta_Sym_Arith_ofMon___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Mon"};
static const lean_object* l_Lean_Meta_Sym_Arith_ofMon___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofMon___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_ofMon___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Lean_Meta_Sym_Arith_ofMon___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofMon___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofMon___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofMon___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofMon___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofMon___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofMon___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofMon___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofMon___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_ofMon___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 118, 178, 112, 106, 72, 235)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofMon___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofMon___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Sym_Arith_ofMon___closed__1_value),LEAN_SCALAR_PTR_LITERAL(100, 251, 130, 52, 9, 153, 3, 255)}};
static const lean_object* l_Lean_Meta_Sym_Arith_ofMon___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofMon___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_ofMon___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_ofMon___closed__3;
static const lean_string_object l_Lean_Meta_Sym_Arith_ofMon___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "mult"};
static const lean_object* l_Lean_Meta_Sym_Arith_ofMon___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofMon___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofMon___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofMon___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofMon___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofMon___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofMon___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofMon___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofMon___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_ofMon___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 118, 178, 112, 106, 72, 235)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofMon___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofMon___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Sym_Arith_ofMon___closed__4_value),LEAN_SCALAR_PTR_LITERAL(55, 131, 127, 87, 57, 224, 125, 17)}};
static const lean_object* l_Lean_Meta_Sym_Arith_ofMon___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofMon___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_ofMon___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_ofMon___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ofMon(lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Arith_instToExprMon___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Arith_ofMon, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Arith_instToExprMon___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_instToExprMon___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_instToExprMon___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_instToExprMon___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_instToExprMon___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_instToExprMon___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_instToExprMon___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_instToExprMon___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_instToExprMon___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_ofMon___closed__0_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 118, 178, 112, 106, 72, 235)}};
static const lean_object* l_Lean_Meta_Sym_Arith_instToExprMon___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_instToExprMon___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_instToExprMon___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_instToExprMon___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_instToExprMon___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_instToExprMon___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instToExprMon;
static const lean_string_object l_Lean_Meta_Sym_Arith_ofPoly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Poly"};
static const lean_object* l_Lean_Meta_Sym_Arith_ofPoly___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__0_value;
static const lean_string_object l_Lean_Meta_Sym_Arith_ofPoly___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Meta_Sym_Arith_ofPoly___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 149, 121, 227, 179, 241, 101, 21)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value_aux_3),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(119, 139, 207, 255, 85, 141, 219, 244)}};
static const lean_object* l_Lean_Meta_Sym_Arith_ofPoly___closed__2 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__2_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_ofPoly___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_ofPoly___closed__3;
static const lean_string_object l_Lean_Meta_Sym_Arith_ofPoly___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lean_Meta_Sym_Arith_ofPoly___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__4_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofPoly___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofPoly___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__5_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofPoly___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__5_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofPoly___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__5_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 149, 121, 227, 179, 241, 101, 21)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofPoly___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__5_value_aux_3),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__4_value),LEAN_SCALAR_PTR_LITERAL(94, 151, 214, 187, 220, 212, 168, 30)}};
static const lean_object* l_Lean_Meta_Sym_Arith_ofPoly___closed__5 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__5_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_ofPoly___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_ofPoly___closed__6;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ofPoly(lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Arith_instToExprPoly___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Arith_ofPoly, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Arith_instToExprPoly___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_instToExprPoly___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 149, 121, 227, 179, 241, 101, 21)}};
static const lean_object* l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_instToExprPoly___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_instToExprPoly___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_instToExprPoly___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_instToExprPoly___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instToExprPoly;
static const lean_string_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Expr"};
static const lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value_aux_3),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__1_value),LEAN_SCALAR_PTR_LITERAL(99, 190, 53, 58, 106, 245, 204, 195)}};
static const lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_ofRingExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__2;
static const lean_string_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "natCast"};
static const lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__3 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value_aux_3),((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__3_value),LEAN_SCALAR_PTR_LITERAL(253, 68, 252, 101, 77, 40, 4, 69)}};
static const lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_ofRingExpr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__5;
static const lean_string_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "intCast"};
static const lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__6 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__6_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value_aux_3),((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__6_value),LEAN_SCALAR_PTR_LITERAL(106, 165, 135, 38, 200, 151, 160, 243)}};
static const lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_ofRingExpr___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__8;
static const lean_string_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "var"};
static const lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__9 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__9_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value_aux_3),((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__9_value),LEAN_SCALAR_PTR_LITERAL(238, 57, 165, 242, 124, 239, 142, 33)}};
static const lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_ofRingExpr___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__11;
static const lean_string_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__12 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__12_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__13_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__13_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__13_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__13_value_aux_3),((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__12_value),LEAN_SCALAR_PTR_LITERAL(96, 56, 201, 33, 233, 202, 126, 81)}};
static const lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__13 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_ofRingExpr___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__14;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__15_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__15_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__15_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__15_value_aux_3),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPoly___closed__4_value),LEAN_SCALAR_PTR_LITERAL(242, 241, 111, 76, 152, 68, 199, 119)}};
static const lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__15 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__15_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_ofRingExpr___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__16;
static const lean_string_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sub"};
static const lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__17 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__17_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__18_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__18_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__18_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__18_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__18_value_aux_3),((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__17_value),LEAN_SCALAR_PTR_LITERAL(233, 86, 87, 90, 25, 204, 73, 66)}};
static const lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__18 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__18_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_ofRingExpr___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__19;
static const lean_string_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "mul"};
static const lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__20 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__20_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__21_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__21_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__21_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__21_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__21_value_aux_3),((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__20_value),LEAN_SCALAR_PTR_LITERAL(156, 111, 47, 235, 106, 244, 157, 23)}};
static const lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__21 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__21_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_ofRingExpr___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__22;
static const lean_string_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "pow"};
static const lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__23 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__23_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__24_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__24_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__24_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__24_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_ofRingExpr___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__24_value_aux_3),((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__23_value),LEAN_SCALAR_PTR_LITERAL(123, 249, 64, 127, 207, 177, 28, 229)}};
static const lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__24 = (const lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__24_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_ofRingExpr___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr___closed__25;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr(lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Arith_instToExprExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Arith_ofRingExpr, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Arith_instToExprExpr___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Arith_instToExprExpr___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__1_value),LEAN_SCALAR_PTR_LITERAL(116, 4, 170, 185, 29, 24, 60, 188)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1_value_aux_1),((lean_object*)&l_Lean_Meta_Sym_Arith_ofPower___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 3, 54, 198, 92, 149, 38, 227)}};
static const lean_ctor_object l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1_value_aux_2),((lean_object*)&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 58, 170, 233, 188, 73, 178, 21)}};
static const lean_object* l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_instToExprExpr___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_instToExprExpr___closed__2;
static lean_once_cell_t l_Lean_Meta_Sym_Arith_instToExprExpr___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Arith_instToExprExpr___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_instToExprExpr;
static lean_object* _init_l_Lean_Meta_Sym_Arith_mkIntLitK___closed__0(void){
_start:
{
lean_object* v_natZero_1_; lean_object* v_intZero_2_; 
v_natZero_1_ = lean_unsigned_to_nat(0u);
v_intZero_2_ = lean_nat_to_int(v_natZero_1_);
return v_intZero_2_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_mkIntLitK___closed__4(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_box(0);
v___x_9_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_mkIntLitK___closed__3));
v___x_10_ = l_Lean_mkConst(v___x_9_, v___x_8_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_mkIntLitK___closed__7(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_15_ = lean_box(0);
v___x_16_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_mkIntLitK___closed__6));
v___x_17_ = l_Lean_mkConst(v___x_16_, v___x_15_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_mkIntLitK(lean_object* v_k_18_){
_start:
{
lean_object* v_intZero_19_; uint8_t v_isNeg_20_; 
v_intZero_19_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_mkIntLitK___closed__0, &l_Lean_Meta_Sym_Arith_mkIntLitK___closed__0_once, _init_l_Lean_Meta_Sym_Arith_mkIntLitK___closed__0);
v_isNeg_20_ = lean_int_dec_lt(v_k_18_, v_intZero_19_);
if (v_isNeg_20_ == 0)
{
lean_object* v_a_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v_a_21_ = lean_nat_abs(v_k_18_);
v___x_22_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_mkIntLitK___closed__4, &l_Lean_Meta_Sym_Arith_mkIntLitK___closed__4_once, _init_l_Lean_Meta_Sym_Arith_mkIntLitK___closed__4);
v___x_23_ = l_Lean_mkRawNatLit(v_a_21_);
v___x_24_ = l_Lean_Expr_app___override(v___x_22_, v___x_23_);
return v___x_24_;
}
else
{
lean_object* v_abs_25_; lean_object* v_one_26_; lean_object* v_a_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v_abs_25_ = lean_nat_abs(v_k_18_);
v_one_26_ = lean_unsigned_to_nat(1u);
v_a_27_ = lean_nat_sub(v_abs_25_, v_one_26_);
lean_dec(v_abs_25_);
v___x_28_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_mkIntLitK___closed__7, &l_Lean_Meta_Sym_Arith_mkIntLitK___closed__7_once, _init_l_Lean_Meta_Sym_Arith_mkIntLitK___closed__7);
v___x_29_ = l_Lean_mkRawNatLit(v_a_27_);
v___x_30_ = l_Lean_Expr_app___override(v___x_28_, v___x_29_);
return v___x_30_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_mkIntLitK___boxed(lean_object* v_k_31_){
_start:
{
lean_object* v_res_32_; 
v_res_32_ = l_Lean_Meta_Sym_Arith_mkIntLitK(v_k_31_);
lean_dec(v_k_31_);
return v_res_32_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_ofPower___closed__6(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_44_ = lean_box(0);
v___x_45_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_ofPower___closed__5));
v___x_46_ = l_Lean_mkConst(v___x_45_, v___x_44_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ofPower(lean_object* v_p_47_){
_start:
{
lean_object* v_x_48_; lean_object* v_k_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v_x_48_ = lean_ctor_get(v_p_47_, 0);
lean_inc(v_x_48_);
v_k_49_ = lean_ctor_get(v_p_47_, 1);
lean_inc(v_k_49_);
lean_dec_ref(v_p_47_);
v___x_50_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_ofPower___closed__6, &l_Lean_Meta_Sym_Arith_ofPower___closed__6_once, _init_l_Lean_Meta_Sym_Arith_ofPower___closed__6);
v___x_51_ = l_Lean_mkRawNatLit(v_x_48_);
v___x_52_ = l_Lean_mkRawNatLit(v_k_49_);
v___x_53_ = l_Lean_mkAppB(v___x_50_, v___x_51_, v___x_52_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instToExprPower___closed__2(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_box(0);
v___x_61_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_instToExprPower___closed__1));
v___x_62_ = l_Lean_mkConst(v___x_61_, v___x_60_);
return v___x_62_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instToExprPower___closed__3(void){
_start:
{
lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_63_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instToExprPower___closed__2, &l_Lean_Meta_Sym_Arith_instToExprPower___closed__2_once, _init_l_Lean_Meta_Sym_Arith_instToExprPower___closed__2);
v___x_64_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_instToExprPower___closed__0));
v___x_65_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_65_, 0, v___x_64_);
lean_ctor_set(v___x_65_, 1, v___x_63_);
return v___x_65_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instToExprPower(void){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instToExprPower___closed__3, &l_Lean_Meta_Sym_Arith_instToExprPower___closed__3_once, _init_l_Lean_Meta_Sym_Arith_instToExprPower___closed__3);
return v___x_66_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_ofMon___closed__3(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = lean_box(0);
v___x_76_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_ofMon___closed__2));
v___x_77_ = l_Lean_mkConst(v___x_76_, v___x_75_);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_ofMon___closed__6(void){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = lean_box(0);
v___x_86_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_ofMon___closed__5));
v___x_87_ = l_Lean_mkConst(v___x_86_, v___x_85_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ofMon(lean_object* v_m_88_){
_start:
{
if (lean_obj_tag(v_m_88_) == 0)
{
lean_object* v___x_89_; 
v___x_89_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_ofMon___closed__3, &l_Lean_Meta_Sym_Arith_ofMon___closed__3_once, _init_l_Lean_Meta_Sym_Arith_ofMon___closed__3);
return v___x_89_;
}
else
{
lean_object* v_p_90_; lean_object* v_m_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v_p_90_ = lean_ctor_get(v_m_88_, 0);
lean_inc_ref(v_p_90_);
v_m_91_ = lean_ctor_get(v_m_88_, 1);
lean_inc(v_m_91_);
lean_dec_ref_known(v_m_88_, 2);
v___x_92_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_ofMon___closed__6, &l_Lean_Meta_Sym_Arith_ofMon___closed__6_once, _init_l_Lean_Meta_Sym_Arith_ofMon___closed__6);
v___x_93_ = l_Lean_Meta_Sym_Arith_ofPower(v_p_90_);
v___x_94_ = l_Lean_Meta_Sym_Arith_ofMon(v_m_91_);
v___x_95_ = l_Lean_mkAppB(v___x_92_, v___x_93_, v___x_94_);
return v___x_95_;
}
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instToExprMon___closed__2(void){
_start:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_box(0);
v___x_103_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_instToExprMon___closed__1));
v___x_104_ = l_Lean_mkConst(v___x_103_, v___x_102_);
return v___x_104_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instToExprMon___closed__3(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v___x_105_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instToExprMon___closed__2, &l_Lean_Meta_Sym_Arith_instToExprMon___closed__2_once, _init_l_Lean_Meta_Sym_Arith_instToExprMon___closed__2);
v___x_106_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_instToExprMon___closed__0));
v___x_107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_107_, 0, v___x_106_);
lean_ctor_set(v___x_107_, 1, v___x_105_);
return v___x_107_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instToExprMon(void){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instToExprMon___closed__3, &l_Lean_Meta_Sym_Arith_instToExprMon___closed__3_once, _init_l_Lean_Meta_Sym_Arith_instToExprMon___closed__3);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__3(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_117_ = lean_box(0);
v___x_118_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_ofPoly___closed__2));
v___x_119_ = l_Lean_mkConst(v___x_118_, v___x_117_);
return v___x_119_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__6(void){
_start:
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
v___x_127_ = lean_box(0);
v___x_128_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_ofPoly___closed__5));
v___x_129_ = l_Lean_mkConst(v___x_128_, v___x_127_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ofPoly(lean_object* v_p_130_){
_start:
{
if (lean_obj_tag(v_p_130_) == 0)
{
lean_object* v_k_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v_k_131_ = lean_ctor_get(v_p_130_, 0);
lean_inc(v_k_131_);
lean_dec_ref_known(v_p_130_, 1);
v___x_132_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_ofPoly___closed__3, &l_Lean_Meta_Sym_Arith_ofPoly___closed__3_once, _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__3);
v___x_133_ = l_Lean_Meta_Sym_Arith_mkIntLitK(v_k_131_);
lean_dec(v_k_131_);
v___x_134_ = l_Lean_Expr_app___override(v___x_132_, v___x_133_);
return v___x_134_;
}
else
{
lean_object* v_k_135_; lean_object* v_v_136_; lean_object* v_p_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_k_135_ = lean_ctor_get(v_p_130_, 0);
lean_inc(v_k_135_);
v_v_136_ = lean_ctor_get(v_p_130_, 1);
lean_inc(v_v_136_);
v_p_137_ = lean_ctor_get(v_p_130_, 2);
lean_inc_ref(v_p_137_);
lean_dec_ref_known(v_p_130_, 3);
v___x_138_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_ofPoly___closed__6, &l_Lean_Meta_Sym_Arith_ofPoly___closed__6_once, _init_l_Lean_Meta_Sym_Arith_ofPoly___closed__6);
v___x_139_ = l_Lean_Meta_Sym_Arith_mkIntLitK(v_k_135_);
lean_dec(v_k_135_);
v___x_140_ = l_Lean_Meta_Sym_Arith_ofMon(v_v_136_);
v___x_141_ = l_Lean_Meta_Sym_Arith_ofPoly(v_p_137_);
v___x_142_ = l_Lean_mkApp3(v___x_138_, v___x_139_, v___x_140_, v___x_141_);
return v___x_142_;
}
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instToExprPoly___closed__2(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_149_ = lean_box(0);
v___x_150_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_instToExprPoly___closed__1));
v___x_151_ = l_Lean_mkConst(v___x_150_, v___x_149_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instToExprPoly___closed__3(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_152_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instToExprPoly___closed__2, &l_Lean_Meta_Sym_Arith_instToExprPoly___closed__2_once, _init_l_Lean_Meta_Sym_Arith_instToExprPoly___closed__2);
v___x_153_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_instToExprPoly___closed__0));
v___x_154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_154_, 0, v___x_153_);
lean_ctor_set(v___x_154_, 1, v___x_152_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instToExprPoly(void){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instToExprPoly___closed__3, &l_Lean_Meta_Sym_Arith_instToExprPoly___closed__3_once, _init_l_Lean_Meta_Sym_Arith_instToExprPoly___closed__3);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__2(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_163_ = lean_box(0);
v___x_164_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__1));
v___x_165_ = l_Lean_mkConst(v___x_164_, v___x_163_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__5(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_173_ = lean_box(0);
v___x_174_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__4));
v___x_175_ = l_Lean_mkConst(v___x_174_, v___x_173_);
return v___x_175_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__8(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; 
v___x_183_ = lean_box(0);
v___x_184_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__7));
v___x_185_ = l_Lean_mkConst(v___x_184_, v___x_183_);
return v___x_185_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__11(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = lean_box(0);
v___x_194_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__10));
v___x_195_ = l_Lean_mkConst(v___x_194_, v___x_193_);
return v___x_195_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__14(void){
_start:
{
lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_203_ = lean_box(0);
v___x_204_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__13));
v___x_205_ = l_Lean_mkConst(v___x_204_, v___x_203_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__16(void){
_start:
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_212_ = lean_box(0);
v___x_213_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__15));
v___x_214_ = l_Lean_mkConst(v___x_213_, v___x_212_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__19(void){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_222_ = lean_box(0);
v___x_223_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__18));
v___x_224_ = l_Lean_mkConst(v___x_223_, v___x_222_);
return v___x_224_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__22(void){
_start:
{
lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; 
v___x_232_ = lean_box(0);
v___x_233_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__21));
v___x_234_ = l_Lean_mkConst(v___x_233_, v___x_232_);
return v___x_234_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__25(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = lean_box(0);
v___x_243_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_ofRingExpr___closed__24));
v___x_244_ = l_Lean_mkConst(v___x_243_, v___x_242_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Arith_ofRingExpr(lean_object* v_e_245_){
_start:
{
switch(lean_obj_tag(v_e_245_))
{
case 0:
{
lean_object* v_k_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v_k_246_ = lean_ctor_get(v_e_245_, 0);
lean_inc(v_k_246_);
lean_dec_ref_known(v_e_245_, 1);
v___x_247_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__2, &l_Lean_Meta_Sym_Arith_ofRingExpr___closed__2_once, _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__2);
v___x_248_ = l_Lean_Meta_Sym_Arith_mkIntLitK(v_k_246_);
lean_dec(v_k_246_);
v___x_249_ = l_Lean_Expr_app___override(v___x_247_, v___x_248_);
return v___x_249_;
}
case 1:
{
lean_object* v_k_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v_k_250_ = lean_ctor_get(v_e_245_, 0);
lean_inc(v_k_250_);
lean_dec_ref_known(v_e_245_, 1);
v___x_251_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__5, &l_Lean_Meta_Sym_Arith_ofRingExpr___closed__5_once, _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__5);
v___x_252_ = l_Lean_mkRawNatLit(v_k_250_);
v___x_253_ = l_Lean_Expr_app___override(v___x_251_, v___x_252_);
return v___x_253_;
}
case 2:
{
lean_object* v_k_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_k_254_ = lean_ctor_get(v_e_245_, 0);
lean_inc(v_k_254_);
lean_dec_ref_known(v_e_245_, 1);
v___x_255_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__8, &l_Lean_Meta_Sym_Arith_ofRingExpr___closed__8_once, _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__8);
v___x_256_ = l_Lean_Meta_Sym_Arith_mkIntLitK(v_k_254_);
lean_dec(v_k_254_);
v___x_257_ = l_Lean_Expr_app___override(v___x_255_, v___x_256_);
return v___x_257_;
}
case 3:
{
lean_object* v_i_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_i_258_ = lean_ctor_get(v_e_245_, 0);
lean_inc(v_i_258_);
lean_dec_ref_known(v_e_245_, 1);
v___x_259_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__11, &l_Lean_Meta_Sym_Arith_ofRingExpr___closed__11_once, _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__11);
v___x_260_ = l_Lean_mkRawNatLit(v_i_258_);
v___x_261_ = l_Lean_Expr_app___override(v___x_259_, v___x_260_);
return v___x_261_;
}
case 4:
{
lean_object* v_a_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_a_262_ = lean_ctor_get(v_e_245_, 0);
lean_inc_ref(v_a_262_);
lean_dec_ref_known(v_e_245_, 1);
v___x_263_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__14, &l_Lean_Meta_Sym_Arith_ofRingExpr___closed__14_once, _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__14);
v___x_264_ = l_Lean_Meta_Sym_Arith_ofRingExpr(v_a_262_);
v___x_265_ = l_Lean_Expr_app___override(v___x_263_, v___x_264_);
return v___x_265_;
}
case 5:
{
lean_object* v_a_266_; lean_object* v_b_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v_a_266_ = lean_ctor_get(v_e_245_, 0);
lean_inc_ref(v_a_266_);
v_b_267_ = lean_ctor_get(v_e_245_, 1);
lean_inc_ref(v_b_267_);
lean_dec_ref_known(v_e_245_, 2);
v___x_268_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__16, &l_Lean_Meta_Sym_Arith_ofRingExpr___closed__16_once, _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__16);
v___x_269_ = l_Lean_Meta_Sym_Arith_ofRingExpr(v_a_266_);
v___x_270_ = l_Lean_Meta_Sym_Arith_ofRingExpr(v_b_267_);
v___x_271_ = l_Lean_mkAppB(v___x_268_, v___x_269_, v___x_270_);
return v___x_271_;
}
case 6:
{
lean_object* v_a_272_; lean_object* v_b_273_; lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_a_272_ = lean_ctor_get(v_e_245_, 0);
lean_inc_ref(v_a_272_);
v_b_273_ = lean_ctor_get(v_e_245_, 1);
lean_inc_ref(v_b_273_);
lean_dec_ref_known(v_e_245_, 2);
v___x_274_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__19, &l_Lean_Meta_Sym_Arith_ofRingExpr___closed__19_once, _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__19);
v___x_275_ = l_Lean_Meta_Sym_Arith_ofRingExpr(v_a_272_);
v___x_276_ = l_Lean_Meta_Sym_Arith_ofRingExpr(v_b_273_);
v___x_277_ = l_Lean_mkAppB(v___x_274_, v___x_275_, v___x_276_);
return v___x_277_;
}
case 7:
{
lean_object* v_a_278_; lean_object* v_b_279_; lean_object* v___x_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_a_278_ = lean_ctor_get(v_e_245_, 0);
lean_inc_ref(v_a_278_);
v_b_279_ = lean_ctor_get(v_e_245_, 1);
lean_inc_ref(v_b_279_);
lean_dec_ref_known(v_e_245_, 2);
v___x_280_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__22, &l_Lean_Meta_Sym_Arith_ofRingExpr___closed__22_once, _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__22);
v___x_281_ = l_Lean_Meta_Sym_Arith_ofRingExpr(v_a_278_);
v___x_282_ = l_Lean_Meta_Sym_Arith_ofRingExpr(v_b_279_);
v___x_283_ = l_Lean_mkAppB(v___x_280_, v___x_281_, v___x_282_);
return v___x_283_;
}
default: 
{
lean_object* v_a_284_; lean_object* v_k_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_a_284_ = lean_ctor_get(v_e_245_, 0);
lean_inc_ref(v_a_284_);
v_k_285_ = lean_ctor_get(v_e_245_, 1);
lean_inc(v_k_285_);
lean_dec_ref_known(v_e_245_, 2);
v___x_286_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_ofRingExpr___closed__25, &l_Lean_Meta_Sym_Arith_ofRingExpr___closed__25_once, _init_l_Lean_Meta_Sym_Arith_ofRingExpr___closed__25);
v___x_287_ = l_Lean_Meta_Sym_Arith_ofRingExpr(v_a_284_);
v___x_288_ = l_Lean_mkRawNatLit(v_k_285_);
v___x_289_ = l_Lean_mkAppB(v___x_286_, v___x_287_, v___x_288_);
return v___x_289_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instToExprExpr___closed__2(void){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_296_ = lean_box(0);
v___x_297_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_instToExprExpr___closed__1));
v___x_298_ = l_Lean_mkConst(v___x_297_, v___x_296_);
return v___x_298_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instToExprExpr___closed__3(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v___x_299_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instToExprExpr___closed__2, &l_Lean_Meta_Sym_Arith_instToExprExpr___closed__2_once, _init_l_Lean_Meta_Sym_Arith_instToExprExpr___closed__2);
v___x_300_ = ((lean_object*)(l_Lean_Meta_Sym_Arith_instToExprExpr___closed__0));
v___x_301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
lean_ctor_set(v___x_301_, 1, v___x_299_);
return v___x_301_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Arith_instToExprExpr(void){
_start:
{
lean_object* v___x_302_; 
v___x_302_ = lean_obj_once(&l_Lean_Meta_Sym_Arith_instToExprExpr___closed__3, &l_Lean_Meta_Sym_Arith_instToExprExpr___closed__3_once, _init_l_Lean_Meta_Sym_Arith_instToExprExpr___closed__3);
return v___x_302_;
}
}
lean_object* runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin);
lean_object* runtime_initialize_Lean_ToExpr(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_ToExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Sym_Arith_instToExprPower = _init_l_Lean_Meta_Sym_Arith_instToExprPower();
lean_mark_persistent(l_Lean_Meta_Sym_Arith_instToExprPower);
l_Lean_Meta_Sym_Arith_instToExprMon = _init_l_Lean_Meta_Sym_Arith_instToExprMon();
lean_mark_persistent(l_Lean_Meta_Sym_Arith_instToExprMon);
l_Lean_Meta_Sym_Arith_instToExprPoly = _init_l_Lean_Meta_Sym_Arith_instToExprPoly();
lean_mark_persistent(l_Lean_Meta_Sym_Arith_instToExprPoly);
l_Lean_Meta_Sym_Arith_instToExprExpr = _init_l_Lean_Meta_Sym_Arith_instToExprExpr();
lean_mark_persistent(l_Lean_Meta_Sym_Arith_instToExprExpr);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_ToExpr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin);
lean_object* initialize_Lean_ToExpr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_ToExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_ToExpr(builtin);
}
#ifdef __cplusplus
}
#endif
