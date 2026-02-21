// Lean compiler output
// Module: Lean.ToExpr
// Imports: public import Lean.ToLevel public import Init.Data.Rat.Basic
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
lean_object* l_Lean_mkNatLit(lean_object*);
static const lean_closure_object l_Lean_instToExprNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkNatLit, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprNat___closed__0 = (const lean_object*)&l_Lean_instToExprNat___closed__0_value;
static const lean_string_object l_Lean_instToExprNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_instToExprNat___closed__1 = (const lean_object*)&l_Lean_instToExprNat___closed__1_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_instToExprNat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprNat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_instToExprNat___closed__2 = (const lean_object*)&l_Lean_instToExprNat___closed__2_value;
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instToExprNat___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprNat___closed__3;
static lean_once_cell_t l_Lean_instToExprNat___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprNat___closed__4;
LEAN_EXPORT lean_object* l_Lean_instToExprNat;
static const lean_string_object l_Lean_instToExprInt_mkNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_instToExprInt_mkNat___closed__0 = (const lean_object*)&l_Lean_instToExprInt_mkNat___closed__0_value;
static const lean_string_object l_Lean_instToExprInt_mkNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_instToExprInt_mkNat___closed__1 = (const lean_object*)&l_Lean_instToExprInt_mkNat___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instToExprInt_mkNat___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_instToExprInt_mkNat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprInt_mkNat___closed__2_value_aux_0),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_instToExprInt_mkNat___closed__2 = (const lean_object*)&l_Lean_instToExprInt_mkNat___closed__2_value;
lean_object* l_Lean_Level_ofNat(lean_object*);
static lean_once_cell_t l_Lean_instToExprInt_mkNat___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt_mkNat___closed__3;
static lean_once_cell_t l_Lean_instToExprInt_mkNat___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt_mkNat___closed__4;
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instToExprInt_mkNat___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt_mkNat___closed__5;
static const lean_string_object l_Lean_instToExprInt_mkNat___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Int"};
static const lean_object* l_Lean_instToExprInt_mkNat___closed__6 = (const lean_object*)&l_Lean_instToExprInt_mkNat___closed__6_value;
static const lean_ctor_object l_Lean_instToExprInt_mkNat___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_object* l_Lean_instToExprInt_mkNat___closed__7 = (const lean_object*)&l_Lean_instToExprInt_mkNat___closed__7_value;
static lean_once_cell_t l_Lean_instToExprInt_mkNat___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt_mkNat___closed__8;
static const lean_string_object l_Lean_instToExprInt_mkNat___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instOfNat"};
static const lean_object* l_Lean_instToExprInt_mkNat___closed__9 = (const lean_object*)&l_Lean_instToExprInt_mkNat___closed__9_value;
static const lean_ctor_object l_Lean_instToExprInt_mkNat___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__9_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 253, 199, 38, 151, 242, 146)}};
static const lean_object* l_Lean_instToExprInt_mkNat___closed__10 = (const lean_object*)&l_Lean_instToExprInt_mkNat___closed__10_value;
static lean_once_cell_t l_Lean_instToExprInt_mkNat___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt_mkNat___closed__11;
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t l_Lean_instToExprInt___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt___lam__0___closed__0;
static const lean_string_object l_Lean_instToExprInt___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Neg"};
static const lean_object* l_Lean_instToExprInt___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprInt___lam__0___closed__1_value;
static const lean_string_object l_Lean_instToExprInt___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "neg"};
static const lean_object* l_Lean_instToExprInt___lam__0___closed__2 = (const lean_object*)&l_Lean_instToExprInt___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_instToExprInt___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(94, 4, 109, 108, 64, 81, 153, 133)}};
static const lean_ctor_object l_Lean_instToExprInt___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprInt___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_instToExprInt___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(105, 26, 70, 221, 245, 238, 127, 238)}};
static const lean_object* l_Lean_instToExprInt___lam__0___closed__3 = (const lean_object*)&l_Lean_instToExprInt___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_instToExprInt___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt___lam__0___closed__4;
static const lean_string_object l_Lean_instToExprInt___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instNegInt"};
static const lean_object* l_Lean_instToExprInt___lam__0___closed__5 = (const lean_object*)&l_Lean_instToExprInt___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_instToExprInt___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__6_value),LEAN_SCALAR_PTR_LITERAL(61, 25, 98, 154, 117, 127, 69, 97)}};
static const lean_ctor_object l_Lean_instToExprInt___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprInt___lam__0___closed__6_value_aux_0),((lean_object*)&l_Lean_instToExprInt___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(217, 109, 233, 1, 211, 122, 77, 88)}};
static const lean_object* l_Lean_instToExprInt___lam__0___closed__6 = (const lean_object*)&l_Lean_instToExprInt___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_instToExprInt___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt___lam__0___closed__7;
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprInt___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprInt___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToExprInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprInt___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprInt___closed__0 = (const lean_object*)&l_Lean_instToExprInt___closed__0_value;
static lean_once_cell_t l_Lean_instToExprInt___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt___closed__1;
LEAN_EXPORT lean_object* l_Lean_instToExprInt;
static const lean_string_object l_Lean_instToExprRat_mkNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Rat"};
static const lean_object* l_Lean_instToExprRat_mkNat___closed__0 = (const lean_object*)&l_Lean_instToExprRat_mkNat___closed__0_value;
static const lean_ctor_object l_Lean_instToExprRat_mkNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprRat_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 55, 105, 214, 206, 30, 120, 51)}};
static const lean_object* l_Lean_instToExprRat_mkNat___closed__1 = (const lean_object*)&l_Lean_instToExprRat_mkNat___closed__1_value;
static lean_once_cell_t l_Lean_instToExprRat_mkNat___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprRat_mkNat___closed__2;
static const lean_ctor_object l_Lean_instToExprRat_mkNat___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprRat_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 55, 105, 214, 206, 30, 120, 51)}};
static const lean_ctor_object l_Lean_instToExprRat_mkNat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprRat_mkNat___closed__3_value_aux_0),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__9_value),LEAN_SCALAR_PTR_LITERAL(217, 182, 143, 149, 136, 99, 16, 5)}};
static const lean_object* l_Lean_instToExprRat_mkNat___closed__3 = (const lean_object*)&l_Lean_instToExprRat_mkNat___closed__3_value;
static lean_once_cell_t l_Lean_instToExprRat_mkNat___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprRat_mkNat___closed__4;
LEAN_EXPORT lean_object* l_Lean_instToExprRat_mkNat(lean_object*);
static const lean_string_object l_Lean_instToExprRat_mkInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instNeg"};
static const lean_object* l_Lean_instToExprRat_mkInt___closed__0 = (const lean_object*)&l_Lean_instToExprRat_mkInt___closed__0_value;
static const lean_ctor_object l_Lean_instToExprRat_mkInt___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprRat_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 55, 105, 214, 206, 30, 120, 51)}};
static const lean_ctor_object l_Lean_instToExprRat_mkInt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprRat_mkInt___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprRat_mkInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 102, 18, 71, 142, 1, 9, 245)}};
static const lean_object* l_Lean_instToExprRat_mkInt___closed__1 = (const lean_object*)&l_Lean_instToExprRat_mkInt___closed__1_value;
static lean_once_cell_t l_Lean_instToExprRat_mkInt___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprRat_mkInt___closed__2;
LEAN_EXPORT lean_object* l_Lean_instToExprRat_mkInt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprRat_mkInt___boxed(lean_object*);
static const lean_string_object l_Lean_instToExprRat___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "HDiv"};
static const lean_object* l_Lean_instToExprRat___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprRat___lam__0___closed__0_value;
static const lean_string_object l_Lean_instToExprRat___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hDiv"};
static const lean_object* l_Lean_instToExprRat___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprRat___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instToExprRat___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprRat___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(74, 223, 78, 88, 255, 236, 144, 164)}};
static const lean_ctor_object l_Lean_instToExprRat___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprRat___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_instToExprRat___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(26, 183, 188, 240, 156, 118, 170, 84)}};
static const lean_object* l_Lean_instToExprRat___lam__0___closed__2 = (const lean_object*)&l_Lean_instToExprRat___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_instToExprRat___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprRat___lam__0___closed__3;
static lean_once_cell_t l_Lean_instToExprRat___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprRat___lam__0___closed__4;
static lean_once_cell_t l_Lean_instToExprRat___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprRat___lam__0___closed__5;
static const lean_string_object l_Lean_instToExprRat___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "instHDiv"};
static const lean_object* l_Lean_instToExprRat___lam__0___closed__6 = (const lean_object*)&l_Lean_instToExprRat___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_instToExprRat___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprRat___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(34, 70, 113, 198, 157, 211, 131, 18)}};
static const lean_object* l_Lean_instToExprRat___lam__0___closed__7 = (const lean_object*)&l_Lean_instToExprRat___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_instToExprRat___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprRat___lam__0___closed__8;
static const lean_string_object l_Lean_instToExprRat___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "instDiv"};
static const lean_object* l_Lean_instToExprRat___lam__0___closed__9 = (const lean_object*)&l_Lean_instToExprRat___lam__0___closed__9_value;
static const lean_ctor_object l_Lean_instToExprRat___lam__0___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprRat_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 55, 105, 214, 206, 30, 120, 51)}};
static const lean_ctor_object l_Lean_instToExprRat___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprRat___lam__0___closed__10_value_aux_0),((lean_object*)&l_Lean_instToExprRat___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(136, 163, 206, 229, 214, 76, 207, 233)}};
static const lean_object* l_Lean_instToExprRat___lam__0___closed__10 = (const lean_object*)&l_Lean_instToExprRat___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_instToExprRat___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprRat___lam__0___closed__11;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instToExprRat___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprRat___lam__0___closed__12;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprRat___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToExprRat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprRat___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprRat___closed__0 = (const lean_object*)&l_Lean_instToExprRat___closed__0_value;
static lean_once_cell_t l_Lean_instToExprRat___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprRat___closed__1;
LEAN_EXPORT lean_object* l_Lean_instToExprRat;
static const lean_string_object l_Lean_instToExprFin___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Fin"};
static const lean_object* l_Lean_instToExprFin___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprFin___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instToExprFin___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprFin___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_object* l_Lean_instToExprFin___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprFin___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprFin___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprFin___lam__0___closed__2;
static const lean_ctor_object l_Lean_instToExprFin___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprFin___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 91, 162, 2, 110, 238, 123, 219)}};
static const lean_ctor_object l_Lean_instToExprFin___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprFin___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__9_value),LEAN_SCALAR_PTR_LITERAL(92, 84, 52, 176, 228, 163, 228, 83)}};
static const lean_object* l_Lean_instToExprFin___lam__0___closed__3 = (const lean_object*)&l_Lean_instToExprFin___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_instToExprFin___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprFin___lam__0___closed__4;
static const lean_string_object l_Lean_instToExprFin___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "instNeZeroSucc"};
static const lean_object* l_Lean_instToExprFin___lam__0___closed__5 = (const lean_object*)&l_Lean_instToExprFin___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_instToExprFin___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprNat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_instToExprFin___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprFin___lam__0___closed__6_value_aux_0),((lean_object*)&l_Lean_instToExprFin___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(163, 205, 35, 215, 215, 220, 7, 150)}};
static const lean_object* l_Lean_instToExprFin___lam__0___closed__6 = (const lean_object*)&l_Lean_instToExprFin___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_instToExprFin___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprFin___lam__0___closed__7;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprFin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprFin(lean_object*);
static const lean_string_object l_Lean_instToExprBitVec___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l_Lean_instToExprBitVec___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprBitVec___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instToExprBitVec___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprBitVec___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l_Lean_instToExprBitVec___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprBitVec___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l_Lean_instToExprBitVec___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprBitVec___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprBitVec___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprBitVec___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_instToExprBitVec___lam__0(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instToExprBitVec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprBitVec___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l_Lean_instToExprBitVec___closed__0 = (const lean_object*)&l_Lean_instToExprBitVec___closed__0_value;
static lean_once_cell_t l_Lean_instToExprBitVec___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprBitVec___closed__1;
LEAN_EXPORT lean_object* l_Lean_instToExprBitVec(lean_object*);
static const lean_string_object l_Lean_instToExprUInt8___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UInt8"};
static const lean_object* l_Lean_instToExprUInt8___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprUInt8___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instToExprUInt8___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprUInt8___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_object* l_Lean_instToExprUInt8___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprUInt8___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprUInt8___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprUInt8___lam__0___closed__2;
static const lean_ctor_object l_Lean_instToExprUInt8___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprUInt8___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 254, 64, 72, 7, 99, 197, 218)}};
static const lean_ctor_object l_Lean_instToExprUInt8___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprUInt8___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__9_value),LEAN_SCALAR_PTR_LITERAL(106, 22, 191, 22, 91, 53, 63, 20)}};
static const lean_object* l_Lean_instToExprUInt8___lam__0___closed__3 = (const lean_object*)&l_Lean_instToExprUInt8___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_instToExprUInt8___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprUInt8___lam__0___closed__4;
lean_object* lean_uint8_to_nat(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToExprUInt8___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToExprUInt8___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToExprUInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprUInt8___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprUInt8___closed__0 = (const lean_object*)&l_Lean_instToExprUInt8___closed__0_value;
static lean_once_cell_t l_Lean_instToExprUInt8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprUInt8___closed__1;
LEAN_EXPORT lean_object* l_Lean_instToExprUInt8;
static const lean_string_object l_Lean_instToExprUInt16___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt16"};
static const lean_object* l_Lean_instToExprUInt16___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprUInt16___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instToExprUInt16___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprUInt16___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_object* l_Lean_instToExprUInt16___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprUInt16___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprUInt16___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprUInt16___lam__0___closed__2;
static const lean_ctor_object l_Lean_instToExprUInt16___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprUInt16___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(6, 214, 154, 233, 192, 74, 99, 135)}};
static const lean_ctor_object l_Lean_instToExprUInt16___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprUInt16___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__9_value),LEAN_SCALAR_PTR_LITERAL(100, 85, 82, 103, 43, 170, 82, 231)}};
static const lean_object* l_Lean_instToExprUInt16___lam__0___closed__3 = (const lean_object*)&l_Lean_instToExprUInt16___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_instToExprUInt16___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprUInt16___lam__0___closed__4;
lean_object* lean_uint16_to_nat(uint16_t);
LEAN_EXPORT lean_object* l_Lean_instToExprUInt16___lam__0(uint16_t);
LEAN_EXPORT lean_object* l_Lean_instToExprUInt16___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToExprUInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprUInt16___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprUInt16___closed__0 = (const lean_object*)&l_Lean_instToExprUInt16___closed__0_value;
static lean_once_cell_t l_Lean_instToExprUInt16___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprUInt16___closed__1;
LEAN_EXPORT lean_object* l_Lean_instToExprUInt16;
static const lean_string_object l_Lean_instToExprUInt32___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt32"};
static const lean_object* l_Lean_instToExprUInt32___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprUInt32___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instToExprUInt32___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprUInt32___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_object* l_Lean_instToExprUInt32___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprUInt32___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprUInt32___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprUInt32___lam__0___closed__2;
static const lean_ctor_object l_Lean_instToExprUInt32___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprUInt32___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(98, 192, 58, 241, 186, 14, 255, 186)}};
static const lean_ctor_object l_Lean_instToExprUInt32___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprUInt32___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__9_value),LEAN_SCALAR_PTR_LITERAL(112, 78, 205, 187, 174, 188, 116, 224)}};
static const lean_object* l_Lean_instToExprUInt32___lam__0___closed__3 = (const lean_object*)&l_Lean_instToExprUInt32___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_instToExprUInt32___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprUInt32___lam__0___closed__4;
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_instToExprUInt32___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_instToExprUInt32___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToExprUInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprUInt32___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprUInt32___closed__0 = (const lean_object*)&l_Lean_instToExprUInt32___closed__0_value;
static lean_once_cell_t l_Lean_instToExprUInt32___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprUInt32___closed__1;
LEAN_EXPORT lean_object* l_Lean_instToExprUInt32;
static const lean_string_object l_Lean_instToExprUInt64___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "UInt64"};
static const lean_object* l_Lean_instToExprUInt64___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprUInt64___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instToExprUInt64___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprUInt64___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_object* l_Lean_instToExprUInt64___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprUInt64___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprUInt64___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprUInt64___lam__0___closed__2;
static const lean_ctor_object l_Lean_instToExprUInt64___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprUInt64___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 113, 45, 150, 103, 228, 0, 41)}};
static const lean_ctor_object l_Lean_instToExprUInt64___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprUInt64___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__9_value),LEAN_SCALAR_PTR_LITERAL(8, 204, 85, 89, 36, 115, 101, 7)}};
static const lean_object* l_Lean_instToExprUInt64___lam__0___closed__3 = (const lean_object*)&l_Lean_instToExprUInt64___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_instToExprUInt64___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprUInt64___lam__0___closed__4;
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Lean_instToExprUInt64___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_Lean_instToExprUInt64___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToExprUInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprUInt64___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprUInt64___closed__0 = (const lean_object*)&l_Lean_instToExprUInt64___closed__0_value;
static lean_once_cell_t l_Lean_instToExprUInt64___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprUInt64___closed__1;
LEAN_EXPORT lean_object* l_Lean_instToExprUInt64;
static const lean_string_object l_Lean_instToExprUSize___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l_Lean_instToExprUSize___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprUSize___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instToExprUSize___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprUSize___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_object* l_Lean_instToExprUSize___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprUSize___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprUSize___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprUSize___lam__0___closed__2;
static const lean_ctor_object l_Lean_instToExprUSize___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprUSize___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_ctor_object l_Lean_instToExprUSize___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprUSize___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__9_value),LEAN_SCALAR_PTR_LITERAL(43, 155, 189, 13, 93, 69, 82, 247)}};
static const lean_object* l_Lean_instToExprUSize___lam__0___closed__3 = (const lean_object*)&l_Lean_instToExprUSize___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_instToExprUSize___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprUSize___lam__0___closed__4;
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_instToExprUSize___lam__0(size_t);
LEAN_EXPORT lean_object* l_Lean_instToExprUSize___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToExprUSize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprUSize___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprUSize___closed__0 = (const lean_object*)&l_Lean_instToExprUSize___closed__0_value;
static lean_once_cell_t l_Lean_instToExprUSize___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprUSize___closed__1;
LEAN_EXPORT lean_object* l_Lean_instToExprUSize;
static const lean_string_object l_Lean_instToExprInt8_mkNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Int8"};
static const lean_object* l_Lean_instToExprInt8_mkNat___closed__0 = (const lean_object*)&l_Lean_instToExprInt8_mkNat___closed__0_value;
static const lean_ctor_object l_Lean_instToExprInt8_mkNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt8_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_object* l_Lean_instToExprInt8_mkNat___closed__1 = (const lean_object*)&l_Lean_instToExprInt8_mkNat___closed__1_value;
static lean_once_cell_t l_Lean_instToExprInt8_mkNat___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt8_mkNat___closed__2;
static const lean_ctor_object l_Lean_instToExprInt8_mkNat___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt8_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_ctor_object l_Lean_instToExprInt8_mkNat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprInt8_mkNat___closed__3_value_aux_0),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__9_value),LEAN_SCALAR_PTR_LITERAL(127, 27, 42, 230, 33, 195, 2, 213)}};
static const lean_object* l_Lean_instToExprInt8_mkNat___closed__3 = (const lean_object*)&l_Lean_instToExprInt8_mkNat___closed__3_value;
static lean_once_cell_t l_Lean_instToExprInt8_mkNat___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt8_mkNat___closed__4;
LEAN_EXPORT lean_object* l_Lean_instToExprInt8_mkNat(lean_object*);
uint8_t lean_int8_of_nat(lean_object*);
static lean_once_cell_t l_Lean_instToExprInt8___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_instToExprInt8___lam__0___closed__0;
static const lean_ctor_object l_Lean_instToExprInt8___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt8_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_ctor_object l_Lean_instToExprInt8___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprInt8___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprRat_mkInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 136, 113, 74, 244, 2, 252, 64)}};
static const lean_object* l_Lean_instToExprInt8___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprInt8___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprInt8___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt8___lam__0___closed__2;
uint8_t lean_int8_dec_le(uint8_t, uint8_t);
lean_object* lean_int8_to_int(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToExprInt8___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToExprInt8___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToExprInt8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprInt8___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprInt8___closed__0 = (const lean_object*)&l_Lean_instToExprInt8___closed__0_value;
static lean_once_cell_t l_Lean_instToExprInt8___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt8___closed__1;
static lean_once_cell_t l_Lean_instToExprInt8___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt8___closed__2;
LEAN_EXPORT lean_object* l_Lean_instToExprInt8;
static const lean_string_object l_Lean_instToExprInt16_mkNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int16"};
static const lean_object* l_Lean_instToExprInt16_mkNat___closed__0 = (const lean_object*)&l_Lean_instToExprInt16_mkNat___closed__0_value;
static const lean_ctor_object l_Lean_instToExprInt16_mkNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt16_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_object* l_Lean_instToExprInt16_mkNat___closed__1 = (const lean_object*)&l_Lean_instToExprInt16_mkNat___closed__1_value;
static lean_once_cell_t l_Lean_instToExprInt16_mkNat___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt16_mkNat___closed__2;
static const lean_ctor_object l_Lean_instToExprInt16_mkNat___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt16_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_ctor_object l_Lean_instToExprInt16_mkNat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprInt16_mkNat___closed__3_value_aux_0),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__9_value),LEAN_SCALAR_PTR_LITERAL(27, 135, 2, 47, 242, 43, 34, 57)}};
static const lean_object* l_Lean_instToExprInt16_mkNat___closed__3 = (const lean_object*)&l_Lean_instToExprInt16_mkNat___closed__3_value;
static lean_once_cell_t l_Lean_instToExprInt16_mkNat___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt16_mkNat___closed__4;
LEAN_EXPORT lean_object* l_Lean_instToExprInt16_mkNat(lean_object*);
uint16_t lean_int16_of_nat(lean_object*);
static lean_once_cell_t l_Lean_instToExprInt16___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Lean_instToExprInt16___lam__0___closed__0;
static const lean_ctor_object l_Lean_instToExprInt16___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt16_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_ctor_object l_Lean_instToExprInt16___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprInt16___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprRat_mkInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 21, 130, 152, 152, 188, 226, 171)}};
static const lean_object* l_Lean_instToExprInt16___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprInt16___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprInt16___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt16___lam__0___closed__2;
uint8_t lean_int16_dec_le(uint16_t, uint16_t);
lean_object* lean_int16_to_int(uint16_t);
LEAN_EXPORT lean_object* l_Lean_instToExprInt16___lam__0(uint16_t);
LEAN_EXPORT lean_object* l_Lean_instToExprInt16___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToExprInt16___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprInt16___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprInt16___closed__0 = (const lean_object*)&l_Lean_instToExprInt16___closed__0_value;
static lean_once_cell_t l_Lean_instToExprInt16___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt16___closed__1;
static lean_once_cell_t l_Lean_instToExprInt16___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt16___closed__2;
LEAN_EXPORT lean_object* l_Lean_instToExprInt16;
static const lean_string_object l_Lean_instToExprInt32_mkNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int32"};
static const lean_object* l_Lean_instToExprInt32_mkNat___closed__0 = (const lean_object*)&l_Lean_instToExprInt32_mkNat___closed__0_value;
static const lean_ctor_object l_Lean_instToExprInt32_mkNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt32_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_object* l_Lean_instToExprInt32_mkNat___closed__1 = (const lean_object*)&l_Lean_instToExprInt32_mkNat___closed__1_value;
static lean_once_cell_t l_Lean_instToExprInt32_mkNat___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt32_mkNat___closed__2;
static const lean_ctor_object l_Lean_instToExprInt32_mkNat___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt32_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_ctor_object l_Lean_instToExprInt32_mkNat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprInt32_mkNat___closed__3_value_aux_0),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__9_value),LEAN_SCALAR_PTR_LITERAL(248, 229, 193, 13, 61, 199, 64, 179)}};
static const lean_object* l_Lean_instToExprInt32_mkNat___closed__3 = (const lean_object*)&l_Lean_instToExprInt32_mkNat___closed__3_value;
static lean_once_cell_t l_Lean_instToExprInt32_mkNat___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt32_mkNat___closed__4;
LEAN_EXPORT lean_object* l_Lean_instToExprInt32_mkNat(lean_object*);
uint32_t lean_int32_of_nat(lean_object*);
static lean_once_cell_t l_Lean_instToExprInt32___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Lean_instToExprInt32___lam__0___closed__0;
static const lean_ctor_object l_Lean_instToExprInt32___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt32_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_ctor_object l_Lean_instToExprInt32___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprInt32___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprRat_mkInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 86, 165, 75, 15, 11, 161, 233)}};
static const lean_object* l_Lean_instToExprInt32___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprInt32___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprInt32___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt32___lam__0___closed__2;
uint8_t lean_int32_dec_le(uint32_t, uint32_t);
lean_object* lean_int32_to_int(uint32_t);
LEAN_EXPORT lean_object* l_Lean_instToExprInt32___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_instToExprInt32___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToExprInt32___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprInt32___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprInt32___closed__0 = (const lean_object*)&l_Lean_instToExprInt32___closed__0_value;
static lean_once_cell_t l_Lean_instToExprInt32___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt32___closed__1;
static lean_once_cell_t l_Lean_instToExprInt32___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt32___closed__2;
LEAN_EXPORT lean_object* l_Lean_instToExprInt32;
static const lean_string_object l_Lean_instToExprInt64_mkNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Int64"};
static const lean_object* l_Lean_instToExprInt64_mkNat___closed__0 = (const lean_object*)&l_Lean_instToExprInt64_mkNat___closed__0_value;
static const lean_ctor_object l_Lean_instToExprInt64_mkNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt64_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_object* l_Lean_instToExprInt64_mkNat___closed__1 = (const lean_object*)&l_Lean_instToExprInt64_mkNat___closed__1_value;
static lean_once_cell_t l_Lean_instToExprInt64_mkNat___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt64_mkNat___closed__2;
static const lean_ctor_object l_Lean_instToExprInt64_mkNat___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt64_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_ctor_object l_Lean_instToExprInt64_mkNat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprInt64_mkNat___closed__3_value_aux_0),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__9_value),LEAN_SCALAR_PTR_LITERAL(101, 121, 108, 245, 111, 40, 94, 171)}};
static const lean_object* l_Lean_instToExprInt64_mkNat___closed__3 = (const lean_object*)&l_Lean_instToExprInt64_mkNat___closed__3_value;
static lean_once_cell_t l_Lean_instToExprInt64_mkNat___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt64_mkNat___closed__4;
LEAN_EXPORT lean_object* l_Lean_instToExprInt64_mkNat(lean_object*);
uint64_t lean_int64_of_nat(lean_object*);
static lean_once_cell_t l_Lean_instToExprInt64___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_instToExprInt64___lam__0___closed__0;
static const lean_ctor_object l_Lean_instToExprInt64___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt64_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_ctor_object l_Lean_instToExprInt64___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprInt64___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprRat_mkInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 152, 19, 102, 101, 167, 71, 92)}};
static const lean_object* l_Lean_instToExprInt64___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprInt64___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprInt64___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt64___lam__0___closed__2;
uint8_t lean_int64_dec_le(uint64_t, uint64_t);
lean_object* lean_int64_to_int_sint(uint64_t);
LEAN_EXPORT lean_object* l_Lean_instToExprInt64___lam__0(uint64_t);
LEAN_EXPORT lean_object* l_Lean_instToExprInt64___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToExprInt64___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprInt64___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprInt64___closed__0 = (const lean_object*)&l_Lean_instToExprInt64___closed__0_value;
static lean_once_cell_t l_Lean_instToExprInt64___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt64___closed__1;
static lean_once_cell_t l_Lean_instToExprInt64___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt64___closed__2;
LEAN_EXPORT lean_object* l_Lean_instToExprInt64;
static const lean_string_object l_Lean_instToExprISize_mkNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ISize"};
static const lean_object* l_Lean_instToExprISize_mkNat___closed__0 = (const lean_object*)&l_Lean_instToExprISize_mkNat___closed__0_value;
static const lean_ctor_object l_Lean_instToExprISize_mkNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprISize_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_object* l_Lean_instToExprISize_mkNat___closed__1 = (const lean_object*)&l_Lean_instToExprISize_mkNat___closed__1_value;
static lean_once_cell_t l_Lean_instToExprISize_mkNat___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprISize_mkNat___closed__2;
static const lean_ctor_object l_Lean_instToExprISize_mkNat___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprISize_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_ctor_object l_Lean_instToExprISize_mkNat___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprISize_mkNat___closed__3_value_aux_0),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__9_value),LEAN_SCALAR_PTR_LITERAL(108, 37, 89, 109, 22, 214, 192, 149)}};
static const lean_object* l_Lean_instToExprISize_mkNat___closed__3 = (const lean_object*)&l_Lean_instToExprISize_mkNat___closed__3_value;
static lean_once_cell_t l_Lean_instToExprISize_mkNat___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprISize_mkNat___closed__4;
LEAN_EXPORT lean_object* l_Lean_instToExprISize_mkNat(lean_object*);
size_t lean_isize_of_nat(lean_object*);
static lean_once_cell_t l_Lean_instToExprISize___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_instToExprISize___lam__0___closed__0;
static const lean_ctor_object l_Lean_instToExprISize___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprISize_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_ctor_object l_Lean_instToExprISize___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprISize___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprRat_mkInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 56, 140, 35, 97, 137, 251, 184)}};
static const lean_object* l_Lean_instToExprISize___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprISize___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprISize___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprISize___lam__0___closed__2;
uint8_t lean_isize_dec_le(size_t, size_t);
lean_object* lean_isize_to_int(size_t);
LEAN_EXPORT lean_object* l_Lean_instToExprISize___lam__0(size_t);
LEAN_EXPORT lean_object* l_Lean_instToExprISize___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToExprISize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprISize___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprISize___closed__0 = (const lean_object*)&l_Lean_instToExprISize___closed__0_value;
static lean_once_cell_t l_Lean_instToExprISize___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprISize___closed__1;
static lean_once_cell_t l_Lean_instToExprISize___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprISize___closed__2;
LEAN_EXPORT lean_object* l_Lean_instToExprISize;
static const lean_string_object l_Lean_instToExprBool___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l_Lean_instToExprBool___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprBool___lam__0___closed__0_value;
static const lean_string_object l_Lean_instToExprBool___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_instToExprBool___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprBool___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instToExprBool___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprBool___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_instToExprBool___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprBool___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_instToExprBool___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l_Lean_instToExprBool___lam__0___closed__2 = (const lean_object*)&l_Lean_instToExprBool___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_instToExprBool___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprBool___lam__0___closed__3;
static const lean_string_object l_Lean_instToExprBool___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_instToExprBool___lam__0___closed__4 = (const lean_object*)&l_Lean_instToExprBool___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_instToExprBool___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprBool___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l_Lean_instToExprBool___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprBool___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_instToExprBool___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(22, 245, 194, 28, 184, 9, 113, 128)}};
static const lean_object* l_Lean_instToExprBool___lam__0___closed__5 = (const lean_object*)&l_Lean_instToExprBool___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_instToExprBool___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprBool___lam__0___closed__6;
LEAN_EXPORT lean_object* l_Lean_instToExprBool___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToExprBool___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToExprBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprBool___closed__0 = (const lean_object*)&l_Lean_instToExprBool___closed__0_value;
static const lean_ctor_object l_Lean_instToExprBool___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprBool___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_object* l_Lean_instToExprBool___closed__1 = (const lean_object*)&l_Lean_instToExprBool___closed__1_value;
static lean_once_cell_t l_Lean_instToExprBool___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprBool___closed__2;
static lean_once_cell_t l_Lean_instToExprBool___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprBool___closed__3;
LEAN_EXPORT lean_object* l_Lean_instToExprBool;
static const lean_string_object l_Lean_instToExprChar___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l_Lean_instToExprChar___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprChar___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instToExprChar___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprChar___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l_Lean_instToExprChar___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprChar___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l_Lean_instToExprChar___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprChar___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprChar___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprChar___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_instToExprChar___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_instToExprChar___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_instToExprChar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprChar___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprChar___closed__0 = (const lean_object*)&l_Lean_instToExprChar___closed__0_value;
static const lean_ctor_object l_Lean_instToExprChar___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprChar___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_object* l_Lean_instToExprChar___closed__1 = (const lean_object*)&l_Lean_instToExprChar___closed__1_value;
static lean_once_cell_t l_Lean_instToExprChar___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprChar___closed__2;
static lean_once_cell_t l_Lean_instToExprChar___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprChar___closed__3;
LEAN_EXPORT lean_object* l_Lean_instToExprChar;
lean_object* l_Lean_mkStrLit(lean_object*);
static const lean_closure_object l_Lean_instToExprString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkStrLit, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprString___closed__0 = (const lean_object*)&l_Lean_instToExprString___closed__0_value;
static const lean_string_object l_Lean_instToExprString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_Lean_instToExprString___closed__1 = (const lean_object*)&l_Lean_instToExprString___closed__1_value;
static const lean_ctor_object l_Lean_instToExprString___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprString___closed__1_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l_Lean_instToExprString___closed__2 = (const lean_object*)&l_Lean_instToExprString___closed__2_value;
static lean_once_cell_t l_Lean_instToExprString___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprString___closed__3;
static lean_once_cell_t l_Lean_instToExprString___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprString___closed__4;
LEAN_EXPORT lean_object* l_Lean_instToExprString;
static const lean_string_object l_Lean_instToExprUnit___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Unit"};
static const lean_object* l_Lean_instToExprUnit___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprUnit___lam__0___closed__0_value;
static const lean_string_object l_Lean_instToExprUnit___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Lean_instToExprUnit___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprUnit___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instToExprUnit___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprUnit___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_ctor_object l_Lean_instToExprUnit___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprUnit___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_instToExprUnit___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(87, 186, 243, 194, 96, 12, 218, 7)}};
static const lean_object* l_Lean_instToExprUnit___lam__0___closed__2 = (const lean_object*)&l_Lean_instToExprUnit___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_instToExprUnit___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprUnit___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_instToExprUnit___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToExprUnit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprUnit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprUnit___closed__0 = (const lean_object*)&l_Lean_instToExprUnit___closed__0_value;
static const lean_ctor_object l_Lean_instToExprUnit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprUnit___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 84, 106, 234, 91, 210, 120, 136)}};
static const lean_object* l_Lean_instToExprUnit___closed__1 = (const lean_object*)&l_Lean_instToExprUnit___closed__1_value;
static lean_once_cell_t l_Lean_instToExprUnit___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprUnit___closed__2;
static lean_once_cell_t l_Lean_instToExprUnit___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprUnit___closed__3;
LEAN_EXPORT lean_object* l_Lean_instToExprUnit;
static const lean_string_object l_Lean_instToExprFilePath___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "System"};
static const lean_object* l_Lean_instToExprFilePath___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprFilePath___lam__0___closed__0_value;
static const lean_string_object l_Lean_instToExprFilePath___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "FilePath"};
static const lean_object* l_Lean_instToExprFilePath___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprFilePath___lam__0___closed__1_value;
static const lean_string_object l_Lean_instToExprFilePath___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_instToExprFilePath___lam__0___closed__2 = (const lean_object*)&l_Lean_instToExprFilePath___lam__0___closed__2_value;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instToExprFilePath___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprFilePath___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 7, 92, 194, 164, 177, 167, 52)}};
static const lean_ctor_object l_Lean_instToExprFilePath___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprFilePath___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_instToExprFilePath___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(249, 26, 71, 103, 26, 96, 3, 234)}};
static const lean_ctor_object l_Lean_instToExprFilePath___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprFilePath___lam__0___closed__3_value_aux_1),((lean_object*)&l_Lean_instToExprFilePath___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(245, 100, 64, 177, 244, 49, 208, 176)}};
static const lean_object* l_Lean_instToExprFilePath___lam__0___closed__3 = (const lean_object*)&l_Lean_instToExprFilePath___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_instToExprFilePath___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprFilePath___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_instToExprFilePath___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToExprFilePath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprFilePath___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprFilePath___closed__0 = (const lean_object*)&l_Lean_instToExprFilePath___closed__0_value;
static const lean_ctor_object l_Lean_instToExprFilePath___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprFilePath___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 7, 92, 194, 164, 177, 167, 52)}};
static const lean_ctor_object l_Lean_instToExprFilePath___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprFilePath___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprFilePath___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(249, 26, 71, 103, 26, 96, 3, 234)}};
static const lean_object* l_Lean_instToExprFilePath___closed__1 = (const lean_object*)&l_Lean_instToExprFilePath___closed__1_value;
static lean_once_cell_t l_Lean_instToExprFilePath___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprFilePath___closed__2;
static lean_once_cell_t l_Lean_instToExprFilePath___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprFilePath___closed__3;
LEAN_EXPORT lean_object* l_Lean_instToExprFilePath;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr_spec__0(lean_object*);
static const lean_string_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Name"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2_value_aux_0),((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2_value;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "mkStr"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__3 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__3_value;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.ToExpr"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__4 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__4_value;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "_private.Lean.ToExpr.0.Lean.Name.toExprAux.mkStr"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__5 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__5_value;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__6 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__6_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7;
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "anonymous"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__0 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__0_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1_value_aux_0),((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 163, 3, 148, 15, 163, 84, 121)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__3 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__3_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4_value_aux_0),((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 63, 218, 129, 21, 133, 119, 116)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5;
static const lean_string_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__6 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__6_value;
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7_value_aux_0),((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__1_value),LEAN_SCALAR_PTR_LITERAL(251, 222, 196, 1, 17, 104, 171, 184)}};
static const lean_ctor_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7_value_aux_1),((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__6_value),LEAN_SCALAR_PTR_LITERAL(35, 98, 18, 79, 25, 208, 83, 100)}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7_value;
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprName___private__1(lean_object*);
static const lean_closure_object l_Lean_instToExprName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprName___private__1, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprName___closed__0 = (const lean_object*)&l_Lean_instToExprName___closed__0_value;
static lean_once_cell_t l_Lean_instToExprName___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprName___closed__1;
static lean_once_cell_t l_Lean_instToExprName___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprName___closed__2;
LEAN_EXPORT lean_object* l_Lean_instToExprName;
static const lean_string_object l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Option"};
static const lean_object* l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__0_value;
static const lean_string_object l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "none"};
static const lean_object* l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(149, 114, 34, 228, 75, 195, 143, 131)}};
static const lean_object* l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "some"};
static const lean_object* l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_ctor_object l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(89, 148, 40, 55, 221, 242, 231, 67)}};
static const lean_object* l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_instToExprOptionOfToLevel___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instToExprOptionOfToLevel___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(95, 234, 177, 188, 3, 226, 91, 252)}};
static const lean_object* l_Lean_instToExprOptionOfToLevel___redArg___closed__0 = (const lean_object*)&l_Lean_instToExprOptionOfToLevel___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToExprOptionOfToLevel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprOptionOfToLevel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___private__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___private__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___private__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___private__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instToExprListOfToLevel___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_Lean_instToExprListOfToLevel___redArg___closed__0 = (const lean_object*)&l_Lean_instToExprListOfToLevel___redArg___closed__0_value;
static const lean_string_object l_Lean_instToExprListOfToLevel___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_instToExprListOfToLevel___redArg___closed__1 = (const lean_object*)&l_Lean_instToExprListOfToLevel___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instToExprListOfToLevel___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprListOfToLevel___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_instToExprListOfToLevel___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprListOfToLevel___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_instToExprListOfToLevel___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l_Lean_instToExprListOfToLevel___redArg___closed__2 = (const lean_object*)&l_Lean_instToExprListOfToLevel___redArg___closed__2_value;
static const lean_string_object l_Lean_instToExprListOfToLevel___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l_Lean_instToExprListOfToLevel___redArg___closed__3 = (const lean_object*)&l_Lean_instToExprListOfToLevel___redArg___closed__3_value;
static const lean_ctor_object l_Lean_instToExprListOfToLevel___redArg___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprListOfToLevel___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_instToExprListOfToLevel___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprListOfToLevel___redArg___closed__4_value_aux_0),((lean_object*)&l_Lean_instToExprListOfToLevel___redArg___closed__3_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l_Lean_instToExprListOfToLevel___redArg___closed__4 = (const lean_object*)&l_Lean_instToExprListOfToLevel___redArg___closed__4_value;
static const lean_ctor_object l_Lean_instToExprListOfToLevel___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprListOfToLevel___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_object* l_Lean_instToExprListOfToLevel___redArg___closed__5 = (const lean_object*)&l_Lean_instToExprListOfToLevel___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "toArray"};
static const lean_object* l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprListOfToLevel___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(225, 54, 189, 64, 249, 49, 198, 116)}};
static const lean_object* l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__1_value;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprArrayOfToLevel___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instToExprArrayOfToLevel___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l_Lean_instToExprArrayOfToLevel___redArg___closed__0 = (const lean_object*)&l_Lean_instToExprArrayOfToLevel___redArg___closed__0_value;
static const lean_ctor_object l_Lean_instToExprArrayOfToLevel___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprArrayOfToLevel___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_object* l_Lean_instToExprArrayOfToLevel___redArg___closed__1 = (const lean_object*)&l_Lean_instToExprArrayOfToLevel___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instToExprArrayOfToLevel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprArrayOfToLevel(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Prod"};
static const lean_object* l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_ctor_object l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprFilePath___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 121, 37, 123, 104, 28, 189, 89)}};
static const lean_object* l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__1_value;
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprProdOfToLevel___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instToExprProdOfToLevel___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(121, 119, 164, 206, 221, 118, 48, 212)}};
static const lean_object* l_Lean_instToExprProdOfToLevel___redArg___closed__0 = (const lean_object*)&l_Lean_instToExprProdOfToLevel___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_instToExprProdOfToLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprProdOfToLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_instToExprLiteral___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Literal"};
static const lean_object* l_Lean_instToExprLiteral___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprLiteral___lam__0___closed__0_value;
static const lean_string_object l_Lean_instToExprLiteral___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "natVal"};
static const lean_object* l_Lean_instToExprLiteral___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprLiteral___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_instToExprLiteral___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instToExprLiteral___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprLiteral___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_instToExprLiteral___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 22, 220, 12, 129, 114, 43, 97)}};
static const lean_ctor_object l_Lean_instToExprLiteral___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprLiteral___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_instToExprLiteral___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(64, 199, 201, 37, 137, 51, 1, 129)}};
static const lean_object* l_Lean_instToExprLiteral___lam__0___closed__2 = (const lean_object*)&l_Lean_instToExprLiteral___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_instToExprLiteral___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprLiteral___lam__0___closed__3;
static const lean_string_object l_Lean_instToExprLiteral___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "strVal"};
static const lean_object* l_Lean_instToExprLiteral___lam__0___closed__4 = (const lean_object*)&l_Lean_instToExprLiteral___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_instToExprLiteral___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instToExprLiteral___lam__0___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprLiteral___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_instToExprLiteral___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 22, 220, 12, 129, 114, 43, 97)}};
static const lean_ctor_object l_Lean_instToExprLiteral___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprLiteral___lam__0___closed__5_value_aux_1),((lean_object*)&l_Lean_instToExprLiteral___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(68, 214, 249, 146, 84, 160, 212, 27)}};
static const lean_object* l_Lean_instToExprLiteral___lam__0___closed__5 = (const lean_object*)&l_Lean_instToExprLiteral___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_instToExprLiteral___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprLiteral___lam__0___closed__6;
lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprLiteral___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToExprLiteral___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprLiteral___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprLiteral___closed__0 = (const lean_object*)&l_Lean_instToExprLiteral___closed__0_value;
static const lean_ctor_object l_Lean_instToExprLiteral___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instToExprLiteral___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprLiteral___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprLiteral___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 22, 220, 12, 129, 114, 43, 97)}};
static const lean_object* l_Lean_instToExprLiteral___closed__1 = (const lean_object*)&l_Lean_instToExprLiteral___closed__1_value;
static lean_once_cell_t l_Lean_instToExprLiteral___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprLiteral___closed__2;
static lean_once_cell_t l_Lean_instToExprLiteral___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprLiteral___closed__3;
LEAN_EXPORT lean_object* l_Lean_instToExprLiteral;
static const lean_string_object l_Lean_instToExprFVarId___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "FVarId"};
static const lean_object* l_Lean_instToExprFVarId___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprFVarId___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_instToExprFVarId___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instToExprFVarId___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprFVarId___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprFVarId___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(134, 80, 170, 214, 218, 146, 55, 86)}};
static const lean_ctor_object l_Lean_instToExprFVarId___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprFVarId___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_instToExprFilePath___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 212, 153, 136, 172, 214, 179, 96)}};
static const lean_object* l_Lean_instToExprFVarId___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprFVarId___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprFVarId___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprFVarId___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_instToExprFVarId___lam__0(lean_object*);
static const lean_closure_object l_Lean_instToExprFVarId___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instToExprFVarId___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprFVarId___closed__0 = (const lean_object*)&l_Lean_instToExprFVarId___closed__0_value;
static const lean_ctor_object l_Lean_instToExprFVarId___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instToExprFVarId___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprFVarId___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprFVarId___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(134, 80, 170, 214, 218, 146, 55, 86)}};
static const lean_object* l_Lean_instToExprFVarId___closed__1 = (const lean_object*)&l_Lean_instToExprFVarId___closed__1_value;
static lean_once_cell_t l_Lean_instToExprFVarId___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprFVarId___closed__2;
static lean_once_cell_t l_Lean_instToExprFVarId___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprFVarId___closed__3;
LEAN_EXPORT lean_object* l_Lean_instToExprFVarId;
static const lean_string_object l_Lean_instToExprPreresolved___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean_instToExprPreresolved___lam__0___closed__0 = (const lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__0_value;
static const lean_string_object l_Lean_instToExprPreresolved___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Preresolved"};
static const lean_object* l_Lean_instToExprPreresolved___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__1_value;
static const lean_string_object l_Lean_instToExprPreresolved___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namespace"};
static const lean_object* l_Lean_instToExprPreresolved___lam__0___closed__2 = (const lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__2_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instToExprPreresolved___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instToExprPreresolved___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 144, 98, 72, 115, 31, 20, 74)}};
static const lean_ctor_object l_Lean_instToExprPreresolved___lam__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__3_value_aux_1),((lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(203, 115, 25, 42, 173, 164, 230, 137)}};
static const lean_ctor_object l_Lean_instToExprPreresolved___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__3_value_aux_2),((lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(141, 91, 234, 5, 195, 77, 204, 210)}};
static const lean_object* l_Lean_instToExprPreresolved___lam__0___closed__3 = (const lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_instToExprPreresolved___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprPreresolved___lam__0___closed__4;
static const lean_string_object l_Lean_instToExprPreresolved___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "decl"};
static const lean_object* l_Lean_instToExprPreresolved___lam__0___closed__5 = (const lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_instToExprPreresolved___lam__0___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instToExprPreresolved___lam__0___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__6_value_aux_0),((lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 144, 98, 72, 115, 31, 20, 74)}};
static const lean_ctor_object l_Lean_instToExprPreresolved___lam__0___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__6_value_aux_1),((lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(203, 115, 25, 42, 173, 164, 230, 137)}};
static const lean_ctor_object l_Lean_instToExprPreresolved___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__6_value_aux_2),((lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(10, 43, 252, 229, 158, 70, 246, 135)}};
static const lean_object* l_Lean_instToExprPreresolved___lam__0___closed__6 = (const lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_instToExprPreresolved___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprPreresolved___lam__0___closed__7;
static const lean_ctor_object l_Lean_instToExprPreresolved___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_instToExprPreresolved___lam__0___closed__8 = (const lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_instToExprPreresolved___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprPreresolved___lam__0___closed__9;
static lean_once_cell_t l_Lean_instToExprPreresolved___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprPreresolved___lam__0___closed__10;
static lean_once_cell_t l_Lean_instToExprPreresolved___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprPreresolved___lam__0___closed__11;
static lean_once_cell_t l_Lean_instToExprPreresolved___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprPreresolved___lam__0___closed__12;
LEAN_EXPORT lean_object* l_Lean_instToExprPreresolved___lam__0(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instToExprPreresolved___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprPreresolved___closed__0;
static const lean_ctor_object l_Lean_instToExprPreresolved___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_instToExprPreresolved___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprPreresolved___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 144, 98, 72, 115, 31, 20, 74)}};
static const lean_ctor_object l_Lean_instToExprPreresolved___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprPreresolved___closed__1_value_aux_1),((lean_object*)&l_Lean_instToExprPreresolved___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(203, 115, 25, 42, 173, 164, 230, 137)}};
static const lean_object* l_Lean_instToExprPreresolved___closed__1 = (const lean_object*)&l_Lean_instToExprPreresolved___closed__1_value;
static lean_once_cell_t l_Lean_instToExprPreresolved___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprPreresolved___closed__2;
static lean_once_cell_t l_Lean_instToExprPreresolved___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprPreresolved___closed__3;
LEAN_EXPORT lean_object* l_Lean_instToExprPreresolved;
static lean_object* _init_l_Lean_instToExprNat___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprNat___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprNat___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprNat___closed__3, &l_Lean_instToExprNat___closed__3_once, _init_l_Lean_instToExprNat___closed__3);
x_2 = ((lean_object*)(l_Lean_instToExprNat___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprNat(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprNat___closed__4, &l_Lean_instToExprNat___closed__4_once, _init_l_Lean_instToExprNat___closed__4);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprInt_mkNat___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = l_Lean_Level_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instToExprInt_mkNat___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__3, &l_Lean_instToExprInt_mkNat___closed__3_once, _init_l_Lean_instToExprInt_mkNat___closed__3);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt_mkNat___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__4, &l_Lean_instToExprInt_mkNat___closed__4_once, _init_l_Lean_instToExprInt_mkNat___closed__4);
x_2 = ((lean_object*)(l_Lean_instToExprInt_mkNat___closed__2));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt_mkNat___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprInt_mkNat___closed__7));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt_mkNat___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprInt_mkNat___closed__10));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt_mkNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_mkRawNatLit(x_1);
x_3 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
x_4 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__8, &l_Lean_instToExprInt_mkNat___closed__8_once, _init_l_Lean_instToExprInt_mkNat___closed__8);
x_5 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__11, &l_Lean_instToExprInt_mkNat___closed__11_once, _init_l_Lean_instToExprInt_mkNat___closed__11);
lean_inc_ref(x_2);
x_6 = l_Lean_Expr_app___override(x_5, x_2);
x_7 = l_Lean_mkApp3(x_3, x_4, x_2, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_instToExprInt___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instToExprInt___lam__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__4, &l_Lean_instToExprInt_mkNat___closed__4_once, _init_l_Lean_instToExprInt_mkNat___closed__4);
x_2 = ((lean_object*)(l_Lean_instToExprInt___lam__0___closed__3));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt___lam__0___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprInt___lam__0___closed__6));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__0, &l_Lean_instToExprInt___lam__0___closed__0_once, _init_l_Lean_instToExprInt___lam__0___closed__0);
x_3 = lean_int_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__4, &l_Lean_instToExprInt___lam__0___closed__4_once, _init_l_Lean_instToExprInt___lam__0___closed__4);
x_5 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__8, &l_Lean_instToExprInt_mkNat___closed__8_once, _init_l_Lean_instToExprInt_mkNat___closed__8);
x_6 = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__7, &l_Lean_instToExprInt___lam__0___closed__7_once, _init_l_Lean_instToExprInt___lam__0___closed__7);
x_7 = lean_int_neg(x_1);
x_8 = l_Int_toNat(x_7);
lean_dec(x_7);
x_9 = l_Lean_instToExprInt_mkNat(x_8);
x_10 = l_Lean_mkApp3(x_4, x_5, x_6, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Int_toNat(x_1);
x_12 = l_Lean_instToExprInt_mkNat(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instToExprInt___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instToExprInt___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__8, &l_Lean_instToExprInt_mkNat___closed__8_once, _init_l_Lean_instToExprInt_mkNat___closed__8);
x_2 = ((lean_object*)(l_Lean_instToExprInt___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprInt___closed__1, &l_Lean_instToExprInt___closed__1_once, _init_l_Lean_instToExprInt___closed__1);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprRat_mkNat___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprRat_mkNat___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprRat_mkNat___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprRat_mkNat___closed__3));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprRat_mkNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_mkRawNatLit(x_1);
x_3 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
x_4 = lean_obj_once(&l_Lean_instToExprRat_mkNat___closed__2, &l_Lean_instToExprRat_mkNat___closed__2_once, _init_l_Lean_instToExprRat_mkNat___closed__2);
x_5 = lean_obj_once(&l_Lean_instToExprRat_mkNat___closed__4, &l_Lean_instToExprRat_mkNat___closed__4_once, _init_l_Lean_instToExprRat_mkNat___closed__4);
lean_inc_ref(x_2);
x_6 = l_Lean_Expr_app___override(x_5, x_2);
x_7 = l_Lean_mkApp3(x_3, x_4, x_2, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_instToExprRat_mkInt___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprRat_mkInt___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprRat_mkInt(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__0, &l_Lean_instToExprInt___lam__0___closed__0_once, _init_l_Lean_instToExprInt___lam__0___closed__0);
x_3 = lean_int_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__4, &l_Lean_instToExprInt___lam__0___closed__4_once, _init_l_Lean_instToExprInt___lam__0___closed__4);
x_5 = lean_obj_once(&l_Lean_instToExprRat_mkNat___closed__2, &l_Lean_instToExprRat_mkNat___closed__2_once, _init_l_Lean_instToExprRat_mkNat___closed__2);
x_6 = lean_obj_once(&l_Lean_instToExprRat_mkInt___closed__2, &l_Lean_instToExprRat_mkInt___closed__2_once, _init_l_Lean_instToExprRat_mkInt___closed__2);
x_7 = lean_int_neg(x_1);
x_8 = l_Int_toNat(x_7);
lean_dec(x_7);
x_9 = l_Lean_instToExprRat_mkNat(x_8);
x_10 = l_Lean_mkApp3(x_4, x_5, x_6, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Int_toNat(x_1);
x_12 = l_Lean_instToExprRat_mkNat(x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprRat_mkInt___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instToExprRat_mkInt(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instToExprRat___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__4, &l_Lean_instToExprInt_mkNat___closed__4_once, _init_l_Lean_instToExprInt_mkNat___closed__4);
x_2 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__3, &l_Lean_instToExprInt_mkNat___closed__3_once, _init_l_Lean_instToExprInt_mkNat___closed__3);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprRat___lam__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprRat___lam__0___closed__3, &l_Lean_instToExprRat___lam__0___closed__3_once, _init_l_Lean_instToExprRat___lam__0___closed__3);
x_2 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__3, &l_Lean_instToExprInt_mkNat___closed__3_once, _init_l_Lean_instToExprInt_mkNat___closed__3);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprRat___lam__0___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprRat___lam__0___closed__4, &l_Lean_instToExprRat___lam__0___closed__4_once, _init_l_Lean_instToExprRat___lam__0___closed__4);
x_2 = ((lean_object*)(l_Lean_instToExprRat___lam__0___closed__2));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprRat___lam__0___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__4, &l_Lean_instToExprInt_mkNat___closed__4_once, _init_l_Lean_instToExprInt_mkNat___closed__4);
x_2 = ((lean_object*)(l_Lean_instToExprRat___lam__0___closed__7));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprRat___lam__0___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprRat___lam__0___closed__10));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprRat___lam__0___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&l_Lean_instToExprRat___lam__0___closed__11, &l_Lean_instToExprRat___lam__0___closed__11_once, _init_l_Lean_instToExprRat___lam__0___closed__11);
x_2 = lean_obj_once(&l_Lean_instToExprRat_mkNat___closed__2, &l_Lean_instToExprRat_mkNat___closed__2_once, _init_l_Lean_instToExprRat_mkNat___closed__2);
x_3 = lean_obj_once(&l_Lean_instToExprRat___lam__0___closed__8, &l_Lean_instToExprRat___lam__0___closed__8_once, _init_l_Lean_instToExprRat___lam__0___closed__8);
x_4 = l_Lean_mkAppB(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprRat___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec_ref(x_1);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_obj_once(&l_Lean_instToExprRat___lam__0___closed__5, &l_Lean_instToExprRat___lam__0___closed__5_once, _init_l_Lean_instToExprRat___lam__0___closed__5);
x_7 = lean_obj_once(&l_Lean_instToExprRat_mkNat___closed__2, &l_Lean_instToExprRat_mkNat___closed__2_once, _init_l_Lean_instToExprRat_mkNat___closed__2);
x_8 = lean_obj_once(&l_Lean_instToExprRat___lam__0___closed__12, &l_Lean_instToExprRat___lam__0___closed__12_once, _init_l_Lean_instToExprRat___lam__0___closed__12);
x_9 = l_Lean_instToExprRat_mkInt(x_2);
lean_dec(x_2);
x_10 = lean_nat_to_int(x_3);
x_11 = l_Lean_instToExprRat_mkInt(x_10);
lean_dec(x_10);
x_12 = l_Lean_mkApp6(x_6, x_7, x_7, x_7, x_8, x_9, x_11);
return x_12;
}
else
{
lean_object* x_13; 
lean_dec(x_3);
x_13 = l_Lean_instToExprRat_mkInt(x_2);
lean_dec(x_2);
return x_13;
}
}
}
static lean_object* _init_l_Lean_instToExprRat___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprRat_mkNat___closed__2, &l_Lean_instToExprRat_mkNat___closed__2_once, _init_l_Lean_instToExprRat_mkNat___closed__2);
x_2 = ((lean_object*)(l_Lean_instToExprRat___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprRat(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprRat___closed__1, &l_Lean_instToExprRat___closed__1_once, _init_l_Lean_instToExprRat___closed__1);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprFin___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprFin___lam__0___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprFin___lam__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprFin___lam__0___closed__3));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprFin___lam__0___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprFin___lam__0___closed__6));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprFin___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = l_Lean_mkRawNatLit(x_2);
x_4 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
x_5 = lean_obj_once(&l_Lean_instToExprFin___lam__0___closed__2, &l_Lean_instToExprFin___lam__0___closed__2_once, _init_l_Lean_instToExprFin___lam__0___closed__2);
lean_inc(x_1);
x_6 = l_Lean_mkNatLit(x_1);
lean_inc_ref(x_6);
x_7 = l_Lean_Expr_app___override(x_5, x_6);
x_8 = lean_obj_once(&l_Lean_instToExprFin___lam__0___closed__4, &l_Lean_instToExprFin___lam__0___closed__4_once, _init_l_Lean_instToExprFin___lam__0___closed__4);
x_9 = lean_obj_once(&l_Lean_instToExprFin___lam__0___closed__7, &l_Lean_instToExprFin___lam__0___closed__7_once, _init_l_Lean_instToExprFin___lam__0___closed__7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_1, x_10);
lean_dec(x_1);
x_12 = l_Lean_mkNatLit(x_11);
x_13 = l_Lean_Expr_app___override(x_9, x_12);
lean_inc_ref(x_3);
x_14 = l_Lean_mkApp3(x_8, x_6, x_13, x_3);
x_15 = l_Lean_mkApp3(x_4, x_7, x_3, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprFin(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_instToExprFin___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_obj_once(&l_Lean_instToExprFin___lam__0___closed__2, &l_Lean_instToExprFin___lam__0___closed__2_once, _init_l_Lean_instToExprFin___lam__0___closed__2);
x_4 = l_Lean_mkNatLit(x_1);
x_5 = l_Lean_Expr_app___override(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instToExprBitVec___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprBitVec___lam__0___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprBitVec___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_obj_once(&l_Lean_instToExprBitVec___lam__0___closed__2, &l_Lean_instToExprBitVec___lam__0___closed__2_once, _init_l_Lean_instToExprBitVec___lam__0___closed__2);
x_4 = l_Lean_mkNatLit(x_1);
x_5 = l_Lean_mkNatLit(x_2);
x_6 = l_Lean_mkAppB(x_3, x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instToExprBitVec___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprBitVec___closed__0));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprBitVec(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_instToExprBitVec___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_obj_once(&l_Lean_instToExprBitVec___closed__1, &l_Lean_instToExprBitVec___closed__1_once, _init_l_Lean_instToExprBitVec___closed__1);
x_4 = l_Lean_mkNatLit(x_1);
x_5 = l_Lean_Expr_app___override(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instToExprUInt8___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprUInt8___lam__0___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUInt8___lam__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprUInt8___lam__0___closed__3));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt8___lam__0(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_uint8_to_nat(x_1);
x_3 = l_Lean_mkRawNatLit(x_2);
x_4 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
x_5 = lean_obj_once(&l_Lean_instToExprUInt8___lam__0___closed__2, &l_Lean_instToExprUInt8___lam__0___closed__2_once, _init_l_Lean_instToExprUInt8___lam__0___closed__2);
x_6 = lean_obj_once(&l_Lean_instToExprUInt8___lam__0___closed__4, &l_Lean_instToExprUInt8___lam__0___closed__4_once, _init_l_Lean_instToExprUInt8___lam__0___closed__4);
lean_inc_ref(x_3);
x_7 = l_Lean_Expr_app___override(x_6, x_3);
x_8 = l_Lean_mkApp3(x_4, x_5, x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt8___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_instToExprUInt8___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUInt8___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprUInt8___lam__0___closed__2, &l_Lean_instToExprUInt8___lam__0___closed__2_once, _init_l_Lean_instToExprUInt8___lam__0___closed__2);
x_2 = ((lean_object*)(l_Lean_instToExprUInt8___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUInt8(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprUInt8___closed__1, &l_Lean_instToExprUInt8___closed__1_once, _init_l_Lean_instToExprUInt8___closed__1);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprUInt16___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprUInt16___lam__0___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUInt16___lam__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprUInt16___lam__0___closed__3));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt16___lam__0(uint16_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_uint16_to_nat(x_1);
x_3 = l_Lean_mkRawNatLit(x_2);
x_4 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
x_5 = lean_obj_once(&l_Lean_instToExprUInt16___lam__0___closed__2, &l_Lean_instToExprUInt16___lam__0___closed__2_once, _init_l_Lean_instToExprUInt16___lam__0___closed__2);
x_6 = lean_obj_once(&l_Lean_instToExprUInt16___lam__0___closed__4, &l_Lean_instToExprUInt16___lam__0___closed__4_once, _init_l_Lean_instToExprUInt16___lam__0___closed__4);
lean_inc_ref(x_3);
x_7 = l_Lean_Expr_app___override(x_6, x_3);
x_8 = l_Lean_mkApp3(x_4, x_5, x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt16___lam__0___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_instToExprUInt16___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUInt16___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprUInt16___lam__0___closed__2, &l_Lean_instToExprUInt16___lam__0___closed__2_once, _init_l_Lean_instToExprUInt16___lam__0___closed__2);
x_2 = ((lean_object*)(l_Lean_instToExprUInt16___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUInt16(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprUInt16___closed__1, &l_Lean_instToExprUInt16___closed__1_once, _init_l_Lean_instToExprUInt16___closed__1);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprUInt32___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprUInt32___lam__0___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUInt32___lam__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprUInt32___lam__0___closed__3));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt32___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = l_Lean_mkRawNatLit(x_2);
x_4 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
x_5 = lean_obj_once(&l_Lean_instToExprUInt32___lam__0___closed__2, &l_Lean_instToExprUInt32___lam__0___closed__2_once, _init_l_Lean_instToExprUInt32___lam__0___closed__2);
x_6 = lean_obj_once(&l_Lean_instToExprUInt32___lam__0___closed__4, &l_Lean_instToExprUInt32___lam__0___closed__4_once, _init_l_Lean_instToExprUInt32___lam__0___closed__4);
lean_inc_ref(x_3);
x_7 = l_Lean_Expr_app___override(x_6, x_3);
x_8 = l_Lean_mkApp3(x_4, x_5, x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt32___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToExprUInt32___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUInt32___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprUInt32___lam__0___closed__2, &l_Lean_instToExprUInt32___lam__0___closed__2_once, _init_l_Lean_instToExprUInt32___lam__0___closed__2);
x_2 = ((lean_object*)(l_Lean_instToExprUInt32___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUInt32(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprUInt32___closed__1, &l_Lean_instToExprUInt32___closed__1_once, _init_l_Lean_instToExprUInt32___closed__1);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprUInt64___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprUInt64___lam__0___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUInt64___lam__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprUInt64___lam__0___closed__3));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt64___lam__0(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_uint64_to_nat(x_1);
x_3 = l_Lean_mkRawNatLit(x_2);
x_4 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
x_5 = lean_obj_once(&l_Lean_instToExprUInt64___lam__0___closed__2, &l_Lean_instToExprUInt64___lam__0___closed__2_once, _init_l_Lean_instToExprUInt64___lam__0___closed__2);
x_6 = lean_obj_once(&l_Lean_instToExprUInt64___lam__0___closed__4, &l_Lean_instToExprUInt64___lam__0___closed__4_once, _init_l_Lean_instToExprUInt64___lam__0___closed__4);
lean_inc_ref(x_3);
x_7 = l_Lean_Expr_app___override(x_6, x_3);
x_8 = l_Lean_mkApp3(x_4, x_5, x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt64___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_3 = l_Lean_instToExprUInt64___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUInt64___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprUInt64___lam__0___closed__2, &l_Lean_instToExprUInt64___lam__0___closed__2_once, _init_l_Lean_instToExprUInt64___lam__0___closed__2);
x_2 = ((lean_object*)(l_Lean_instToExprUInt64___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUInt64(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprUInt64___closed__1, &l_Lean_instToExprUInt64___closed__1_once, _init_l_Lean_instToExprUInt64___closed__1);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprUSize___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprUSize___lam__0___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUSize___lam__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprUSize___lam__0___closed__3));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUSize___lam__0(size_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_usize_to_nat(x_1);
x_3 = l_Lean_mkRawNatLit(x_2);
x_4 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
x_5 = lean_obj_once(&l_Lean_instToExprUSize___lam__0___closed__2, &l_Lean_instToExprUSize___lam__0___closed__2_once, _init_l_Lean_instToExprUSize___lam__0___closed__2);
x_6 = lean_obj_once(&l_Lean_instToExprUSize___lam__0___closed__4, &l_Lean_instToExprUSize___lam__0___closed__4_once, _init_l_Lean_instToExprUSize___lam__0___closed__4);
lean_inc_ref(x_3);
x_7 = l_Lean_Expr_app___override(x_6, x_3);
x_8 = l_Lean_mkApp3(x_4, x_5, x_3, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUSize___lam__0___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToExprUSize___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUSize___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprUSize___lam__0___closed__2, &l_Lean_instToExprUSize___lam__0___closed__2_once, _init_l_Lean_instToExprUSize___lam__0___closed__2);
x_2 = ((lean_object*)(l_Lean_instToExprUSize___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUSize(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprUSize___closed__1, &l_Lean_instToExprUSize___closed__1_once, _init_l_Lean_instToExprUSize___closed__1);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprInt8_mkNat___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprInt8_mkNat___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt8_mkNat___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprInt8_mkNat___closed__3));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt8_mkNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_mkRawNatLit(x_1);
x_3 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
x_4 = lean_obj_once(&l_Lean_instToExprInt8_mkNat___closed__2, &l_Lean_instToExprInt8_mkNat___closed__2_once, _init_l_Lean_instToExprInt8_mkNat___closed__2);
x_5 = lean_obj_once(&l_Lean_instToExprInt8_mkNat___closed__4, &l_Lean_instToExprInt8_mkNat___closed__4_once, _init_l_Lean_instToExprInt8_mkNat___closed__4);
lean_inc_ref(x_2);
x_6 = l_Lean_Expr_app___override(x_5, x_2);
x_7 = l_Lean_mkApp3(x_3, x_4, x_2, x_6);
return x_7;
}
}
static uint8_t _init_l_Lean_instToExprInt8___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_int8_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instToExprInt8___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprInt8___lam__0___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt8___lam__0(uint8_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; 
x_2 = lean_uint8_once(&l_Lean_instToExprInt8___lam__0___closed__0, &l_Lean_instToExprInt8___lam__0___closed__0_once, _init_l_Lean_instToExprInt8___lam__0___closed__0);
x_3 = lean_int8_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__4, &l_Lean_instToExprInt___lam__0___closed__4_once, _init_l_Lean_instToExprInt___lam__0___closed__4);
x_5 = lean_obj_once(&l_Lean_instToExprInt8_mkNat___closed__2, &l_Lean_instToExprInt8_mkNat___closed__2_once, _init_l_Lean_instToExprInt8_mkNat___closed__2);
x_6 = lean_obj_once(&l_Lean_instToExprInt8___lam__0___closed__2, &l_Lean_instToExprInt8___lam__0___closed__2_once, _init_l_Lean_instToExprInt8___lam__0___closed__2);
x_7 = lean_int8_to_int(x_1);
x_8 = lean_int_neg(x_7);
x_9 = l_Int_toNat(x_8);
lean_dec(x_8);
x_10 = l_Lean_instToExprInt8_mkNat(x_9);
x_11 = l_Lean_mkApp3(x_4, x_5, x_6, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_int8_to_int(x_1);
x_13 = l_Int_toNat(x_12);
x_14 = l_Lean_instToExprInt8_mkNat(x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt8___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_instToExprInt8___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt8___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprInt8_mkNat___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt8___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprInt8___closed__1, &l_Lean_instToExprInt8___closed__1_once, _init_l_Lean_instToExprInt8___closed__1);
x_2 = ((lean_object*)(l_Lean_instToExprInt8___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt8(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprInt8___closed__2, &l_Lean_instToExprInt8___closed__2_once, _init_l_Lean_instToExprInt8___closed__2);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprInt16_mkNat___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprInt16_mkNat___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt16_mkNat___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprInt16_mkNat___closed__3));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt16_mkNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_mkRawNatLit(x_1);
x_3 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
x_4 = lean_obj_once(&l_Lean_instToExprInt16_mkNat___closed__2, &l_Lean_instToExprInt16_mkNat___closed__2_once, _init_l_Lean_instToExprInt16_mkNat___closed__2);
x_5 = lean_obj_once(&l_Lean_instToExprInt16_mkNat___closed__4, &l_Lean_instToExprInt16_mkNat___closed__4_once, _init_l_Lean_instToExprInt16_mkNat___closed__4);
lean_inc_ref(x_2);
x_6 = l_Lean_Expr_app___override(x_5, x_2);
x_7 = l_Lean_mkApp3(x_3, x_4, x_2, x_6);
return x_7;
}
}
static uint16_t _init_l_Lean_instToExprInt16___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; uint16_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_int16_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instToExprInt16___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprInt16___lam__0___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt16___lam__0(uint16_t x_1) {
_start:
{
uint16_t x_2; uint8_t x_3; 
x_2 = lean_uint16_once(&l_Lean_instToExprInt16___lam__0___closed__0, &l_Lean_instToExprInt16___lam__0___closed__0_once, _init_l_Lean_instToExprInt16___lam__0___closed__0);
x_3 = lean_int16_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__4, &l_Lean_instToExprInt___lam__0___closed__4_once, _init_l_Lean_instToExprInt___lam__0___closed__4);
x_5 = lean_obj_once(&l_Lean_instToExprInt16_mkNat___closed__2, &l_Lean_instToExprInt16_mkNat___closed__2_once, _init_l_Lean_instToExprInt16_mkNat___closed__2);
x_6 = lean_obj_once(&l_Lean_instToExprInt16___lam__0___closed__2, &l_Lean_instToExprInt16___lam__0___closed__2_once, _init_l_Lean_instToExprInt16___lam__0___closed__2);
x_7 = lean_int16_to_int(x_1);
x_8 = lean_int_neg(x_7);
x_9 = l_Int_toNat(x_8);
lean_dec(x_8);
x_10 = l_Lean_instToExprInt16_mkNat(x_9);
x_11 = l_Lean_mkApp3(x_4, x_5, x_6, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_int16_to_int(x_1);
x_13 = l_Int_toNat(x_12);
x_14 = l_Lean_instToExprInt16_mkNat(x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt16___lam__0___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_instToExprInt16___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt16___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprInt16_mkNat___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt16___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprInt16___closed__1, &l_Lean_instToExprInt16___closed__1_once, _init_l_Lean_instToExprInt16___closed__1);
x_2 = ((lean_object*)(l_Lean_instToExprInt16___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt16(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprInt16___closed__2, &l_Lean_instToExprInt16___closed__2_once, _init_l_Lean_instToExprInt16___closed__2);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprInt32_mkNat___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprInt32_mkNat___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt32_mkNat___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprInt32_mkNat___closed__3));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt32_mkNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_mkRawNatLit(x_1);
x_3 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
x_4 = lean_obj_once(&l_Lean_instToExprInt32_mkNat___closed__2, &l_Lean_instToExprInt32_mkNat___closed__2_once, _init_l_Lean_instToExprInt32_mkNat___closed__2);
x_5 = lean_obj_once(&l_Lean_instToExprInt32_mkNat___closed__4, &l_Lean_instToExprInt32_mkNat___closed__4_once, _init_l_Lean_instToExprInt32_mkNat___closed__4);
lean_inc_ref(x_2);
x_6 = l_Lean_Expr_app___override(x_5, x_2);
x_7 = l_Lean_mkApp3(x_3, x_4, x_2, x_6);
return x_7;
}
}
static uint32_t _init_l_Lean_instToExprInt32___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_int32_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instToExprInt32___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprInt32___lam__0___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt32___lam__0(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = lean_uint32_once(&l_Lean_instToExprInt32___lam__0___closed__0, &l_Lean_instToExprInt32___lam__0___closed__0_once, _init_l_Lean_instToExprInt32___lam__0___closed__0);
x_3 = lean_int32_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__4, &l_Lean_instToExprInt___lam__0___closed__4_once, _init_l_Lean_instToExprInt___lam__0___closed__4);
x_5 = lean_obj_once(&l_Lean_instToExprInt32_mkNat___closed__2, &l_Lean_instToExprInt32_mkNat___closed__2_once, _init_l_Lean_instToExprInt32_mkNat___closed__2);
x_6 = lean_obj_once(&l_Lean_instToExprInt32___lam__0___closed__2, &l_Lean_instToExprInt32___lam__0___closed__2_once, _init_l_Lean_instToExprInt32___lam__0___closed__2);
x_7 = lean_int32_to_int(x_1);
x_8 = lean_int_neg(x_7);
lean_dec(x_7);
x_9 = l_Int_toNat(x_8);
lean_dec(x_8);
x_10 = l_Lean_instToExprInt32_mkNat(x_9);
x_11 = l_Lean_mkApp3(x_4, x_5, x_6, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_int32_to_int(x_1);
x_13 = l_Int_toNat(x_12);
lean_dec(x_12);
x_14 = l_Lean_instToExprInt32_mkNat(x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt32___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToExprInt32___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt32___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprInt32_mkNat___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt32___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprInt32___closed__1, &l_Lean_instToExprInt32___closed__1_once, _init_l_Lean_instToExprInt32___closed__1);
x_2 = ((lean_object*)(l_Lean_instToExprInt32___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt32(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprInt32___closed__2, &l_Lean_instToExprInt32___closed__2_once, _init_l_Lean_instToExprInt32___closed__2);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprInt64_mkNat___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprInt64_mkNat___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt64_mkNat___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprInt64_mkNat___closed__3));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt64_mkNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_mkRawNatLit(x_1);
x_3 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
x_4 = lean_obj_once(&l_Lean_instToExprInt64_mkNat___closed__2, &l_Lean_instToExprInt64_mkNat___closed__2_once, _init_l_Lean_instToExprInt64_mkNat___closed__2);
x_5 = lean_obj_once(&l_Lean_instToExprInt64_mkNat___closed__4, &l_Lean_instToExprInt64_mkNat___closed__4_once, _init_l_Lean_instToExprInt64_mkNat___closed__4);
lean_inc_ref(x_2);
x_6 = l_Lean_Expr_app___override(x_5, x_2);
x_7 = l_Lean_mkApp3(x_3, x_4, x_2, x_6);
return x_7;
}
}
static uint64_t _init_l_Lean_instToExprInt64___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_int64_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instToExprInt64___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprInt64___lam__0___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt64___lam__0(uint64_t x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; 
x_2 = lean_uint64_once(&l_Lean_instToExprInt64___lam__0___closed__0, &l_Lean_instToExprInt64___lam__0___closed__0_once, _init_l_Lean_instToExprInt64___lam__0___closed__0);
x_3 = lean_int64_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__4, &l_Lean_instToExprInt___lam__0___closed__4_once, _init_l_Lean_instToExprInt___lam__0___closed__4);
x_5 = lean_obj_once(&l_Lean_instToExprInt64_mkNat___closed__2, &l_Lean_instToExprInt64_mkNat___closed__2_once, _init_l_Lean_instToExprInt64_mkNat___closed__2);
x_6 = lean_obj_once(&l_Lean_instToExprInt64___lam__0___closed__2, &l_Lean_instToExprInt64___lam__0___closed__2_once, _init_l_Lean_instToExprInt64___lam__0___closed__2);
x_7 = lean_int64_to_int_sint(x_1);
x_8 = lean_int_neg(x_7);
lean_dec(x_7);
x_9 = l_Int_toNat(x_8);
lean_dec(x_8);
x_10 = l_Lean_instToExprInt64_mkNat(x_9);
x_11 = l_Lean_mkApp3(x_4, x_5, x_6, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_int64_to_int_sint(x_1);
x_13 = l_Int_toNat(x_12);
lean_dec(x_12);
x_14 = l_Lean_instToExprInt64_mkNat(x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt64___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec_ref(x_1);
x_3 = l_Lean_instToExprInt64___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt64___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprInt64_mkNat___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt64___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprInt64___closed__1, &l_Lean_instToExprInt64___closed__1_once, _init_l_Lean_instToExprInt64___closed__1);
x_2 = ((lean_object*)(l_Lean_instToExprInt64___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprInt64(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprInt64___closed__2, &l_Lean_instToExprInt64___closed__2_once, _init_l_Lean_instToExprInt64___closed__2);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprISize_mkNat___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprISize_mkNat___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprISize_mkNat___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprISize_mkNat___closed__3));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprISize_mkNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_Lean_mkRawNatLit(x_1);
x_3 = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
x_4 = lean_obj_once(&l_Lean_instToExprISize_mkNat___closed__2, &l_Lean_instToExprISize_mkNat___closed__2_once, _init_l_Lean_instToExprISize_mkNat___closed__2);
x_5 = lean_obj_once(&l_Lean_instToExprISize_mkNat___closed__4, &l_Lean_instToExprISize_mkNat___closed__4_once, _init_l_Lean_instToExprISize_mkNat___closed__4);
lean_inc_ref(x_2);
x_6 = l_Lean_Expr_app___override(x_5, x_2);
x_7 = l_Lean_mkApp3(x_3, x_4, x_2, x_6);
return x_7;
}
}
static size_t _init_l_Lean_instToExprISize___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; size_t x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_isize_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instToExprISize___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprISize___lam__0___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprISize___lam__0(size_t x_1) {
_start:
{
size_t x_2; uint8_t x_3; 
x_2 = lean_usize_once(&l_Lean_instToExprISize___lam__0___closed__0, &l_Lean_instToExprISize___lam__0___closed__0_once, _init_l_Lean_instToExprISize___lam__0___closed__0);
x_3 = lean_isize_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__4, &l_Lean_instToExprInt___lam__0___closed__4_once, _init_l_Lean_instToExprInt___lam__0___closed__4);
x_5 = lean_obj_once(&l_Lean_instToExprISize_mkNat___closed__2, &l_Lean_instToExprISize_mkNat___closed__2_once, _init_l_Lean_instToExprISize_mkNat___closed__2);
x_6 = lean_obj_once(&l_Lean_instToExprISize___lam__0___closed__2, &l_Lean_instToExprISize___lam__0___closed__2_once, _init_l_Lean_instToExprISize___lam__0___closed__2);
x_7 = lean_isize_to_int(x_1);
x_8 = lean_int_neg(x_7);
lean_dec(x_7);
x_9 = l_Int_toNat(x_8);
lean_dec(x_8);
x_10 = l_Lean_instToExprISize_mkNat(x_9);
x_11 = l_Lean_mkApp3(x_4, x_5, x_6, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_isize_to_int(x_1);
x_13 = l_Int_toNat(x_12);
lean_dec(x_12);
x_14 = l_Lean_instToExprISize_mkNat(x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprISize___lam__0___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToExprISize___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprISize___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprISize_mkNat___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprISize___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprISize___closed__1, &l_Lean_instToExprISize___closed__1_once, _init_l_Lean_instToExprISize___closed__1);
x_2 = ((lean_object*)(l_Lean_instToExprISize___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprISize(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprISize___closed__2, &l_Lean_instToExprISize___closed__2_once, _init_l_Lean_instToExprISize___closed__2);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprBool___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprBool___lam__0___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprBool___lam__0___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprBool___lam__0___closed__5));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprBool___lam__0(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lean_instToExprBool___lam__0___closed__3, &l_Lean_instToExprBool___lam__0___closed__3_once, _init_l_Lean_instToExprBool___lam__0___closed__3);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_obj_once(&l_Lean_instToExprBool___lam__0___closed__6, &l_Lean_instToExprBool___lam__0___closed__6_once, _init_l_Lean_instToExprBool___lam__0___closed__6);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprBool___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = l_Lean_instToExprBool___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprBool___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprBool___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprBool___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprBool___closed__2, &l_Lean_instToExprBool___closed__2_once, _init_l_Lean_instToExprBool___closed__2);
x_2 = ((lean_object*)(l_Lean_instToExprBool___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprBool(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprBool___closed__3, &l_Lean_instToExprBool___closed__3_once, _init_l_Lean_instToExprBool___closed__3);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprChar___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprChar___lam__0___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprChar___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_obj_once(&l_Lean_instToExprChar___lam__0___closed__2, &l_Lean_instToExprChar___lam__0___closed__2_once, _init_l_Lean_instToExprChar___lam__0___closed__2);
x_3 = lean_uint32_to_nat(x_1);
x_4 = l_Lean_mkRawNatLit(x_3);
x_5 = l_Lean_Expr_app___override(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprChar___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToExprChar___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprChar___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprChar___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprChar___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprChar___closed__2, &l_Lean_instToExprChar___closed__2_once, _init_l_Lean_instToExprChar___closed__2);
x_2 = ((lean_object*)(l_Lean_instToExprChar___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprChar(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprChar___closed__3, &l_Lean_instToExprChar___closed__3_once, _init_l_Lean_instToExprChar___closed__3);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprString___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprString___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprString___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprString___closed__3, &l_Lean_instToExprString___closed__3_once, _init_l_Lean_instToExprString___closed__3);
x_2 = ((lean_object*)(l_Lean_instToExprString___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprString(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprString___closed__4, &l_Lean_instToExprString___closed__4_once, _init_l_Lean_instToExprString___closed__4);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprUnit___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprUnit___lam__0___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUnit___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_obj_once(&l_Lean_instToExprUnit___lam__0___closed__3, &l_Lean_instToExprUnit___lam__0___closed__3_once, _init_l_Lean_instToExprUnit___lam__0___closed__3);
return x_2;
}
}
static lean_object* _init_l_Lean_instToExprUnit___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprUnit___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUnit___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprUnit___closed__2, &l_Lean_instToExprUnit___closed__2_once, _init_l_Lean_instToExprUnit___closed__2);
x_2 = ((lean_object*)(l_Lean_instToExprUnit___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprUnit(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprUnit___closed__3, &l_Lean_instToExprUnit___closed__3_once, _init_l_Lean_instToExprUnit___closed__3);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprFilePath___lam__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprFilePath___lam__0___closed__3));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprFilePath___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_obj_once(&l_Lean_instToExprFilePath___lam__0___closed__4, &l_Lean_instToExprFilePath___lam__0___closed__4_once, _init_l_Lean_instToExprFilePath___lam__0___closed__4);
x_3 = l_Lean_mkStrLit(x_1);
x_4 = l_Lean_Expr_app___override(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instToExprFilePath___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprFilePath___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprFilePath___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprFilePath___closed__2, &l_Lean_instToExprFilePath___closed__2_once, _init_l_Lean_instToExprFilePath___closed__2);
x_2 = ((lean_object*)(l_Lean_instToExprFilePath___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprFilePath(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprFilePath___closed__3, &l_Lean_instToExprFilePath___closed__3_once, _init_l_Lean_instToExprFilePath___closed__3);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_lt(x_3, x_2);
if (x_4 == 0)
{
lean_dec(x_2);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(8u);
x_6 = lean_nat_dec_le(x_2, x_5);
lean_dec(x_2);
return x_6;
}
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_1 = x_7;
x_2 = x_9;
goto _start;
}
default: 
{
uint8_t x_11; 
lean_dec(x_2);
x_11 = 0;
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedExpr;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__6));
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(221u);
x_4 = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__5));
x_5 = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__4));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_4 = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2));
x_5 = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__3));
x_6 = l_Nat_reprFast(x_2);
x_7 = lean_string_append(x_5, x_6);
lean_dec_ref(x_6);
x_8 = l_Lean_Name_str___override(x_4, x_7);
x_9 = lean_box(0);
x_10 = l_Lean_mkConst(x_8, x_9);
x_11 = l_Array_reverse___redArg(x_3);
x_12 = l_Lean_mkAppN(x_10, x_11);
lean_dec_ref(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_2, x_15);
lean_dec(x_2);
x_17 = l_Lean_mkStrLit(x_14);
x_18 = lean_array_push(x_3, x_17);
x_1 = x_13;
x_2 = x_16;
x_3 = x_18;
goto _start;
}
default: 
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7, &l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7_once, _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7);
x_21 = l_panic___at___00__private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr_spec__0(x_20);
return x_21;
}
}
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2, &l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2_once, _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2);
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5, &l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5_once, _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5);
x_6 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(x_3);
x_7 = l_Lean_mkStrLit(x_4);
x_8 = l_Lean_mkAppB(x_5, x_6, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec_ref(x_1);
x_11 = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8, &l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8_once, _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8);
x_12 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(x_9);
x_13 = l_Lean_mkNatLit(x_10);
x_14 = l_Lean_mkAppB(x_11, x_12, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__0, &l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__0_once, _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__0);
x_6 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr(x_1, x_2, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprName___private__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instToExprName___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprName___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprName___closed__1, &l_Lean_instToExprName___closed__1_once, _init_l_Lean_instToExprName___closed__1);
x_2 = ((lean_object*)(l_Lean_instToExprName___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprName(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprName___closed__2, &l_Lean_instToExprName___closed__2_once, _init_l_Lean_instToExprName___closed__2);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprOptionOfToLevel___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec_ref(x_3);
x_5 = ((lean_object*)(l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__2));
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_mkConst(x_5, x_7);
x_9 = l_Lean_Expr_app___override(x_8, x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec_ref(x_4);
x_11 = ((lean_object*)(l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__4));
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_mkConst(x_11, x_13);
x_15 = lean_apply_1(x_3, x_10);
x_16 = l_Lean_mkAppB(x_14, x_2, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprOptionOfToLevel___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_5);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_instToExprOptionOfToLevel___redArg___lam__0), 4, 3);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_5);
lean_closure_set(x_6, 2, x_4);
x_7 = ((lean_object*)(l_Lean_instToExprOptionOfToLevel___redArg___closed__0));
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_mkConst(x_7, x_9);
x_11 = l_Lean_Expr_app___override(x_10, x_5);
lean_ctor_set(x_2, 1, x_11);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_2);
lean_inc_ref(x_13);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_instToExprOptionOfToLevel___redArg___lam__0), 4, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_12);
x_15 = ((lean_object*)(l_Lean_instToExprOptionOfToLevel___redArg___closed__0));
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_mkConst(x_15, x_17);
x_19 = l_Lean_Expr_app___override(x_18, x_13);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprOptionOfToLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instToExprOptionOfToLevel___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec_ref(x_3);
lean_dec_ref(x_1);
lean_inc_ref(x_2);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec_ref(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
x_8 = lean_apply_1(x_7, x_5);
lean_inc_ref(x_3);
x_9 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(x_1, x_2, x_3, x_6);
x_10 = l_Lean_mkAppB(x_3, x_8, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_ToExpr_0__Lean_List_toExprAux(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___private__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___private__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_instToExprListOfToLevel___private__1___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___private__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___private__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_instToExprListOfToLevel___private__1(x_1, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
x_4 = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__2));
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_inc_ref(x_6);
x_7 = l_Lean_mkConst(x_4, x_6);
lean_inc_ref(x_3);
x_8 = l_Lean_Expr_app___override(x_7, x_3);
x_9 = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__4));
lean_inc_ref(x_6);
x_10 = l_Lean_mkConst(x_9, x_6);
lean_inc_ref(x_3);
x_11 = l_Lean_Expr_app___override(x_10, x_3);
x_12 = lean_alloc_closure((void*)(l_Lean_instToExprListOfToLevel___private__1___boxed), 5, 4);
lean_closure_set(x_12, 0, lean_box(0));
lean_closure_set(x_12, 1, x_2);
lean_closure_set(x_12, 2, x_8);
lean_closure_set(x_12, 3, x_11);
x_13 = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__5));
x_14 = l_Lean_mkConst(x_13, x_6);
x_15 = l_Lean_Expr_app___override(x_14, x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instToExprListOfToLevel___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprArrayOfToLevel___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = ((lean_object*)(l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__1));
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
lean_inc_ref(x_7);
x_8 = l_Lean_mkConst(x_5, x_7);
x_9 = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__2));
lean_inc_ref(x_7);
x_10 = l_Lean_mkConst(x_9, x_7);
lean_inc_ref(x_2);
x_11 = l_Lean_Expr_app___override(x_10, x_2);
x_12 = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__4));
x_13 = l_Lean_mkConst(x_12, x_7);
lean_inc_ref(x_2);
x_14 = l_Lean_Expr_app___override(x_13, x_2);
x_15 = lean_array_to_list(x_4);
x_16 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(x_3, x_11, x_14, x_15);
lean_dec_ref(x_11);
x_17 = l_Lean_mkAppB(x_8, x_2, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprArrayOfToLevel___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
lean_inc_ref(x_3);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_instToExprArrayOfToLevel___redArg___lam__0), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
lean_closure_set(x_4, 2, x_2);
x_5 = ((lean_object*)(l_Lean_instToExprArrayOfToLevel___redArg___closed__1));
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_mkConst(x_5, x_7);
x_9 = l_Lean_Expr_app___override(x_8, x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprArrayOfToLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instToExprArrayOfToLevel___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprProdOfToLevel___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = ((lean_object*)(l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__1));
x_12 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_7);
x_14 = l_Lean_mkConst(x_11, x_13);
x_15 = lean_apply_1(x_3, x_9);
x_16 = lean_apply_1(x_4, x_10);
x_17 = l_Lean_mkApp4(x_14, x_5, x_6, x_15, x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_7, 0);
x_19 = lean_ctor_get(x_7, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_7);
x_20 = ((lean_object*)(l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__1));
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_mkConst(x_20, x_23);
x_25 = lean_apply_1(x_3, x_18);
x_26 = lean_apply_1(x_4, x_19);
x_27 = l_Lean_mkApp4(x_24, x_5, x_6, x_25, x_26);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprProdOfToLevel___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_10);
lean_inc_ref(x_8);
lean_inc(x_1);
lean_inc(x_2);
x_11 = lean_alloc_closure((void*)(l_Lean_instToExprProdOfToLevel___redArg___lam__0), 7, 6);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_7);
lean_closure_set(x_11, 3, x_9);
lean_closure_set(x_11, 4, x_8);
lean_closure_set(x_11, 5, x_10);
x_12 = ((lean_object*)(l_Lean_instToExprProdOfToLevel___redArg___closed__0));
x_13 = lean_box(0);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_13);
lean_ctor_set(x_3, 0, x_2);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_3);
x_15 = l_Lean_mkConst(x_12, x_14);
x_16 = l_Lean_mkAppB(x_15, x_8, x_10);
lean_ctor_set(x_4, 1, x_16);
lean_ctor_set(x_4, 0, x_11);
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_17 = lean_ctor_get(x_3, 0);
x_18 = lean_ctor_get(x_3, 1);
x_19 = lean_ctor_get(x_4, 0);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_4);
lean_inc_ref(x_20);
lean_inc_ref(x_18);
lean_inc(x_1);
lean_inc(x_2);
x_21 = lean_alloc_closure((void*)(l_Lean_instToExprProdOfToLevel___redArg___lam__0), 7, 6);
lean_closure_set(x_21, 0, x_2);
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_17);
lean_closure_set(x_21, 3, x_19);
lean_closure_set(x_21, 4, x_18);
lean_closure_set(x_21, 5, x_20);
x_22 = ((lean_object*)(l_Lean_instToExprProdOfToLevel___redArg___closed__0));
x_23 = lean_box(0);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_23);
lean_ctor_set(x_3, 0, x_2);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_3);
x_25 = l_Lean_mkConst(x_22, x_24);
x_26 = l_Lean_mkAppB(x_25, x_18, x_20);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_28 = lean_ctor_get(x_3, 0);
x_29 = lean_ctor_get(x_3, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_3);
x_30 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_30);
x_31 = lean_ctor_get(x_4, 1);
lean_inc_ref(x_31);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_32 = x_4;
} else {
 lean_dec_ref(x_4);
 x_32 = lean_box(0);
}
lean_inc_ref(x_31);
lean_inc_ref(x_29);
lean_inc(x_1);
lean_inc(x_2);
x_33 = lean_alloc_closure((void*)(l_Lean_instToExprProdOfToLevel___redArg___lam__0), 7, 6);
lean_closure_set(x_33, 0, x_2);
lean_closure_set(x_33, 1, x_1);
lean_closure_set(x_33, 2, x_28);
lean_closure_set(x_33, 3, x_30);
lean_closure_set(x_33, 4, x_29);
lean_closure_set(x_33, 5, x_31);
x_34 = ((lean_object*)(l_Lean_instToExprProdOfToLevel___redArg___closed__0));
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_mkConst(x_34, x_37);
x_39 = l_Lean_mkAppB(x_38, x_29, x_31);
if (lean_is_scalar(x_32)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_32;
}
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprProdOfToLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instToExprProdOfToLevel___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_instToExprLiteral___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprLiteral___lam__0___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprLiteral___lam__0___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprLiteral___lam__0___closed__5));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprLiteral___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_obj_once(&l_Lean_instToExprLiteral___lam__0___closed__3, &l_Lean_instToExprLiteral___lam__0___closed__3_once, _init_l_Lean_instToExprLiteral___lam__0___closed__3);
x_3 = l_Lean_Expr_lit___override(x_1);
x_4 = l_Lean_Expr_app___override(x_2, x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_obj_once(&l_Lean_instToExprLiteral___lam__0___closed__6, &l_Lean_instToExprLiteral___lam__0___closed__6_once, _init_l_Lean_instToExprLiteral___lam__0___closed__6);
x_6 = l_Lean_Expr_lit___override(x_1);
x_7 = l_Lean_Expr_app___override(x_5, x_6);
return x_7;
}
}
}
static lean_object* _init_l_Lean_instToExprLiteral___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprLiteral___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprLiteral___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprLiteral___closed__2, &l_Lean_instToExprLiteral___closed__2_once, _init_l_Lean_instToExprLiteral___closed__2);
x_2 = ((lean_object*)(l_Lean_instToExprLiteral___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprLiteral(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprLiteral___closed__3, &l_Lean_instToExprLiteral___closed__3_once, _init_l_Lean_instToExprLiteral___closed__3);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprFVarId___lam__0___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprFVarId___lam__0___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprFVarId___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_obj_once(&l_Lean_instToExprFVarId___lam__0___closed__2, &l_Lean_instToExprFVarId___lam__0___closed__2_once, _init_l_Lean_instToExprFVarId___lam__0___closed__2);
x_3 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_1);
x_4 = l_Lean_Expr_app___override(x_2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instToExprFVarId___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprFVarId___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprFVarId___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprFVarId___closed__2, &l_Lean_instToExprFVarId___closed__2_once, _init_l_Lean_instToExprFVarId___closed__2);
x_2 = ((lean_object*)(l_Lean_instToExprFVarId___closed__0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprFVarId(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprFVarId___closed__3, &l_Lean_instToExprFVarId___closed__3_once, _init_l_Lean_instToExprFVarId___closed__3);
return x_1;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___lam__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprPreresolved___lam__0___closed__3));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___lam__0___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprPreresolved___lam__0___closed__6));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___lam__0___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instToExprPreresolved___lam__0___closed__8));
x_2 = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__2));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___lam__0___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprString___closed__3, &l_Lean_instToExprString___closed__3_once, _init_l_Lean_instToExprString___closed__3);
x_2 = lean_obj_once(&l_Lean_instToExprPreresolved___lam__0___closed__9, &l_Lean_instToExprPreresolved___lam__0___closed__9_once, _init_l_Lean_instToExprPreresolved___lam__0___closed__9);
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___lam__0___closed__11(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_instToExprPreresolved___lam__0___closed__8));
x_2 = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__4));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___lam__0___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprString___closed__3, &l_Lean_instToExprString___closed__3_once, _init_l_Lean_instToExprString___closed__3);
x_2 = lean_obj_once(&l_Lean_instToExprPreresolved___lam__0___closed__11, &l_Lean_instToExprPreresolved___lam__0___closed__11_once, _init_l_Lean_instToExprPreresolved___lam__0___closed__11);
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprPreresolved___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec_ref(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec_ref(x_2);
x_4 = lean_obj_once(&l_Lean_instToExprPreresolved___lam__0___closed__4, &l_Lean_instToExprPreresolved___lam__0___closed__4_once, _init_l_Lean_instToExprPreresolved___lam__0___closed__4);
x_5 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_3);
x_6 = l_Lean_Expr_app___override(x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = lean_obj_once(&l_Lean_instToExprPreresolved___lam__0___closed__7, &l_Lean_instToExprPreresolved___lam__0___closed__7_once, _init_l_Lean_instToExprPreresolved___lam__0___closed__7);
x_10 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_7);
x_11 = lean_obj_once(&l_Lean_instToExprPreresolved___lam__0___closed__10, &l_Lean_instToExprPreresolved___lam__0___closed__10_once, _init_l_Lean_instToExprPreresolved___lam__0___closed__10);
x_12 = lean_obj_once(&l_Lean_instToExprPreresolved___lam__0___closed__12, &l_Lean_instToExprPreresolved___lam__0___closed__12_once, _init_l_Lean_instToExprPreresolved___lam__0___closed__12);
x_13 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(x_1, x_11, x_12, x_8);
x_14 = l_Lean_mkAppB(x_9, x_10, x_13);
return x_14;
}
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_instToExprString;
x_2 = lean_alloc_closure((void*)(l_Lean_instToExprPreresolved___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_instToExprPreresolved___closed__1));
x_3 = l_Lean_Expr_const___override(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_instToExprPreresolved___closed__2, &l_Lean_instToExprPreresolved___closed__2_once, _init_l_Lean_instToExprPreresolved___closed__2);
x_2 = lean_obj_once(&l_Lean_instToExprPreresolved___closed__0, &l_Lean_instToExprPreresolved___closed__0_once, _init_l_Lean_instToExprPreresolved___closed__0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_instToExprPreresolved___closed__3, &l_Lean_instToExprPreresolved___closed__3_once, _init_l_Lean_instToExprPreresolved___closed__3);
return x_1;
}
}
lean_object* initialize_Lean_ToLevel(uint8_t builtin);
lean_object* initialize_Init_Data_Rat_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ToExpr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ToLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Rat_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instToExprNat = _init_l_Lean_instToExprNat();
lean_mark_persistent(l_Lean_instToExprNat);
l_Lean_instToExprInt = _init_l_Lean_instToExprInt();
lean_mark_persistent(l_Lean_instToExprInt);
l_Lean_instToExprRat = _init_l_Lean_instToExprRat();
lean_mark_persistent(l_Lean_instToExprRat);
l_Lean_instToExprUInt8 = _init_l_Lean_instToExprUInt8();
lean_mark_persistent(l_Lean_instToExprUInt8);
l_Lean_instToExprUInt16 = _init_l_Lean_instToExprUInt16();
lean_mark_persistent(l_Lean_instToExprUInt16);
l_Lean_instToExprUInt32 = _init_l_Lean_instToExprUInt32();
lean_mark_persistent(l_Lean_instToExprUInt32);
l_Lean_instToExprUInt64 = _init_l_Lean_instToExprUInt64();
lean_mark_persistent(l_Lean_instToExprUInt64);
l_Lean_instToExprUSize = _init_l_Lean_instToExprUSize();
lean_mark_persistent(l_Lean_instToExprUSize);
l_Lean_instToExprInt8 = _init_l_Lean_instToExprInt8();
lean_mark_persistent(l_Lean_instToExprInt8);
l_Lean_instToExprInt16 = _init_l_Lean_instToExprInt16();
lean_mark_persistent(l_Lean_instToExprInt16);
l_Lean_instToExprInt32 = _init_l_Lean_instToExprInt32();
lean_mark_persistent(l_Lean_instToExprInt32);
l_Lean_instToExprInt64 = _init_l_Lean_instToExprInt64();
lean_mark_persistent(l_Lean_instToExprInt64);
l_Lean_instToExprISize = _init_l_Lean_instToExprISize();
lean_mark_persistent(l_Lean_instToExprISize);
l_Lean_instToExprBool = _init_l_Lean_instToExprBool();
lean_mark_persistent(l_Lean_instToExprBool);
l_Lean_instToExprChar = _init_l_Lean_instToExprChar();
lean_mark_persistent(l_Lean_instToExprChar);
l_Lean_instToExprString = _init_l_Lean_instToExprString();
lean_mark_persistent(l_Lean_instToExprString);
l_Lean_instToExprUnit = _init_l_Lean_instToExprUnit();
lean_mark_persistent(l_Lean_instToExprUnit);
l_Lean_instToExprFilePath = _init_l_Lean_instToExprFilePath();
lean_mark_persistent(l_Lean_instToExprFilePath);
l_Lean_instToExprName = _init_l_Lean_instToExprName();
lean_mark_persistent(l_Lean_instToExprName);
l_Lean_instToExprLiteral = _init_l_Lean_instToExprLiteral();
lean_mark_persistent(l_Lean_instToExprLiteral);
l_Lean_instToExprFVarId = _init_l_Lean_instToExprFVarId();
lean_mark_persistent(l_Lean_instToExprFVarId);
l_Lean_instToExprPreresolved = _init_l_Lean_instToExprPreresolved();
lean_mark_persistent(l_Lean_instToExprPreresolved);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
