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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
lean_object* l_Lean_mkNatLit(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_isize_of_nat(lean_object*);
uint8_t lean_isize_dec_le(size_t, size_t);
lean_object* lean_isize_to_int(size_t);
uint8_t lean_int8_of_nat(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_int64_of_nat(lean_object*);
uint8_t lean_int64_dec_le(uint64_t, uint64_t);
lean_object* lean_int64_to_int_sint(uint64_t);
uint32_t lean_int32_of_nat(lean_object*);
uint16_t lean_int16_of_nat(lean_object*);
uint8_t lean_int16_dec_le(uint16_t, uint16_t);
lean_object* lean_int16_to_int(uint16_t);
lean_object* lean_uint32_to_nat(uint32_t);
uint8_t lean_int8_dec_le(uint8_t, uint8_t);
lean_object* lean_int8_to_int(uint8_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_int32_dec_le(uint32_t, uint32_t);
lean_object* lean_int32_to_int(uint32_t);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
lean_object* lean_array_to_list(lean_object*);
static const lean_closure_object l_Lean_instToExprNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkNatLit, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instToExprNat___closed__0 = (const lean_object*)&l_Lean_instToExprNat___closed__0_value;
static const lean_string_object l_Lean_instToExprNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_instToExprNat___closed__1 = (const lean_object*)&l_Lean_instToExprNat___closed__1_value;
static const lean_ctor_object l_Lean_instToExprNat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprNat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_instToExprNat___closed__2 = (const lean_object*)&l_Lean_instToExprNat___closed__2_value;
static lean_once_cell_t l_Lean_instToExprNat___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprNat___closed__3;
static lean_once_cell_t l_Lean_instToExprNat___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprNat___closed__4;
LEAN_EXPORT lean_object* l_Lean_instToExprNat;
static const lean_string_object l_Lean_instToExprInt_mkNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l_Lean_instToExprInt_mkNat___closed__0 = (const lean_object*)&l_Lean_instToExprInt_mkNat___closed__0_value;
static const lean_string_object l_Lean_instToExprInt_mkNat___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l_Lean_instToExprInt_mkNat___closed__1 = (const lean_object*)&l_Lean_instToExprInt_mkNat___closed__1_value;
static const lean_ctor_object l_Lean_instToExprInt_mkNat___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l_Lean_instToExprInt_mkNat___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprInt_mkNat___closed__2_value_aux_0),((lean_object*)&l_Lean_instToExprInt_mkNat___closed__1_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l_Lean_instToExprInt_mkNat___closed__2 = (const lean_object*)&l_Lean_instToExprInt_mkNat___closed__2_value;
static lean_once_cell_t l_Lean_instToExprInt_mkNat___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt_mkNat___closed__3;
static lean_once_cell_t l_Lean_instToExprInt_mkNat___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt_mkNat___closed__4;
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
LEAN_EXPORT lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
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
static lean_once_cell_t l_Lean_instToExprRat___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprRat___lam__0___closed__12;
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
static lean_once_cell_t l_Lean_instToExprInt8___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint8_t l_Lean_instToExprInt8___lam__0___closed__0;
static const lean_ctor_object l_Lean_instToExprInt8___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt8_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(17, 171, 155, 218, 43, 77, 1, 67)}};
static const lean_ctor_object l_Lean_instToExprInt8___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprInt8___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprRat_mkInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 136, 113, 74, 244, 2, 252, 64)}};
static const lean_object* l_Lean_instToExprInt8___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprInt8___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprInt8___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt8___lam__0___closed__2;
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
static lean_once_cell_t l_Lean_instToExprInt16___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint16_t l_Lean_instToExprInt16___lam__0___closed__0;
static const lean_ctor_object l_Lean_instToExprInt16___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt16_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 121, 89, 120, 57, 100, 28, 22)}};
static const lean_ctor_object l_Lean_instToExprInt16___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprInt16___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprRat_mkInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(62, 21, 130, 152, 152, 188, 226, 171)}};
static const lean_object* l_Lean_instToExprInt16___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprInt16___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprInt16___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt16___lam__0___closed__2;
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
static lean_once_cell_t l_Lean_instToExprInt32___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint32_t l_Lean_instToExprInt32___lam__0___closed__0;
static const lean_ctor_object l_Lean_instToExprInt32___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt32_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(202, 24, 245, 188, 10, 96, 206, 241)}};
static const lean_ctor_object l_Lean_instToExprInt32___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprInt32___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprRat_mkInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(133, 86, 165, 75, 15, 11, 161, 233)}};
static const lean_object* l_Lean_instToExprInt32___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprInt32___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprInt32___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt32___lam__0___closed__2;
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
static lean_once_cell_t l_Lean_instToExprInt64___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_instToExprInt64___lam__0___closed__0;
static const lean_ctor_object l_Lean_instToExprInt64___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprInt64_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 100, 38, 50, 157, 43, 83, 90)}};
static const lean_ctor_object l_Lean_instToExprInt64___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprInt64___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprRat_mkInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 152, 19, 102, 101, 167, 71, 92)}};
static const lean_object* l_Lean_instToExprInt64___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprInt64___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprInt64___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprInt64___lam__0___closed__2;
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
static lean_once_cell_t l_Lean_instToExprISize___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_instToExprISize___lam__0___closed__0;
static const lean_ctor_object l_Lean_instToExprISize___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instToExprISize_mkNat___closed__0_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_ctor_object l_Lean_instToExprISize___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_instToExprISize___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_instToExprRat_mkInt___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 56, 140, 35, 97, 137, 251, 184)}};
static const lean_object* l_Lean_instToExprISize___lam__0___closed__1 = (const lean_object*)&l_Lean_instToExprISize___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_instToExprISize___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instToExprISize___lam__0___closed__2;
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
LEAN_EXPORT uint8_t l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple___boxed(lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7;
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
static const lean_array_object l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__0 = (const lean_object*)&l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__0_value;
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
static lean_object* _init_l_Lean_instToExprNat___closed__3(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_5_ = lean_box(0);
v___x_6_ = ((lean_object*)(l_Lean_instToExprNat___closed__2));
v___x_7_ = l_Lean_mkConst(v___x_6_, v___x_5_);
return v___x_7_;
}
}
static lean_object* _init_l_Lean_instToExprNat___closed__4(void){
_start:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; 
v___x_8_ = lean_obj_once(&l_Lean_instToExprNat___closed__3, &l_Lean_instToExprNat___closed__3_once, _init_l_Lean_instToExprNat___closed__3);
v___x_9_ = ((lean_object*)(l_Lean_instToExprNat___closed__0));
v___x_10_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_10_, 0, v___x_9_);
lean_ctor_set(v___x_10_, 1, v___x_8_);
return v___x_10_;
}
}
static lean_object* _init_l_Lean_instToExprNat(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = lean_obj_once(&l_Lean_instToExprNat___closed__4, &l_Lean_instToExprNat___closed__4_once, _init_l_Lean_instToExprNat___closed__4);
return v___x_11_;
}
}
static lean_object* _init_l_Lean_instToExprInt_mkNat___closed__3(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = l_Lean_Level_ofNat(v___x_17_);
return v___x_18_;
}
}
static lean_object* _init_l_Lean_instToExprInt_mkNat___closed__4(void){
_start:
{
lean_object* v___x_19_; lean_object* v___x_20_; lean_object* v___x_21_; 
v___x_19_ = lean_box(0);
v___x_20_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__3, &l_Lean_instToExprInt_mkNat___closed__3_once, _init_l_Lean_instToExprInt_mkNat___closed__3);
v___x_21_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_21_, 0, v___x_20_);
lean_ctor_set(v___x_21_, 1, v___x_19_);
return v___x_21_;
}
}
static lean_object* _init_l_Lean_instToExprInt_mkNat___closed__5(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_22_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__4, &l_Lean_instToExprInt_mkNat___closed__4_once, _init_l_Lean_instToExprInt_mkNat___closed__4);
v___x_23_ = ((lean_object*)(l_Lean_instToExprInt_mkNat___closed__2));
v___x_24_ = l_Lean_Expr_const___override(v___x_23_, v___x_22_);
return v___x_24_;
}
}
static lean_object* _init_l_Lean_instToExprInt_mkNat___closed__8(void){
_start:
{
lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_28_ = lean_box(0);
v___x_29_ = ((lean_object*)(l_Lean_instToExprInt_mkNat___closed__7));
v___x_30_ = l_Lean_Expr_const___override(v___x_29_, v___x_28_);
return v___x_30_;
}
}
static lean_object* _init_l_Lean_instToExprInt_mkNat___closed__11(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_box(0);
v___x_35_ = ((lean_object*)(l_Lean_instToExprInt_mkNat___closed__10));
v___x_36_ = l_Lean_Expr_const___override(v___x_35_, v___x_34_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt_mkNat(lean_object* v_n_37_){
_start:
{
lean_object* v_r_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v_r_38_ = l_Lean_mkRawNatLit(v_n_37_);
v___x_39_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_40_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__8, &l_Lean_instToExprInt_mkNat___closed__8_once, _init_l_Lean_instToExprInt_mkNat___closed__8);
v___x_41_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__11, &l_Lean_instToExprInt_mkNat___closed__11_once, _init_l_Lean_instToExprInt_mkNat___closed__11);
lean_inc_ref(v_r_38_);
v___x_42_ = l_Lean_Expr_app___override(v___x_41_, v_r_38_);
v___x_43_ = l_Lean_mkApp3(v___x_39_, v___x_40_, v_r_38_, v___x_42_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_instToExprInt___lam__0___closed__0(void){
_start:
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_unsigned_to_nat(0u);
v___x_45_ = lean_nat_to_int(v___x_44_);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_instToExprInt___lam__0___closed__4(void){
_start:
{
lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_51_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__4, &l_Lean_instToExprInt_mkNat___closed__4_once, _init_l_Lean_instToExprInt_mkNat___closed__4);
v___x_52_ = ((lean_object*)(l_Lean_instToExprInt___lam__0___closed__3));
v___x_53_ = l_Lean_Expr_const___override(v___x_52_, v___x_51_);
return v___x_53_;
}
}
static lean_object* _init_l_Lean_instToExprInt___lam__0___closed__7(void){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_58_ = lean_box(0);
v___x_59_ = ((lean_object*)(l_Lean_instToExprInt___lam__0___closed__6));
v___x_60_ = l_Lean_Expr_const___override(v___x_59_, v___x_58_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt___lam__0(lean_object* v_i_61_){
_start:
{
lean_object* v___x_62_; uint8_t v___x_63_; 
v___x_62_ = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__0, &l_Lean_instToExprInt___lam__0___closed__0_once, _init_l_Lean_instToExprInt___lam__0___closed__0);
v___x_63_ = lean_int_dec_le(v___x_62_, v_i_61_);
if (v___x_63_ == 0)
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_64_ = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__4, &l_Lean_instToExprInt___lam__0___closed__4_once, _init_l_Lean_instToExprInt___lam__0___closed__4);
v___x_65_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__8, &l_Lean_instToExprInt_mkNat___closed__8_once, _init_l_Lean_instToExprInt_mkNat___closed__8);
v___x_66_ = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__7, &l_Lean_instToExprInt___lam__0___closed__7_once, _init_l_Lean_instToExprInt___lam__0___closed__7);
v___x_67_ = lean_int_neg(v_i_61_);
v___x_68_ = l_Int_toNat(v___x_67_);
lean_dec(v___x_67_);
v___x_69_ = l_Lean_instToExprInt_mkNat(v___x_68_);
v___x_70_ = l_Lean_mkApp3(v___x_64_, v___x_65_, v___x_66_, v___x_69_);
return v___x_70_;
}
else
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = l_Int_toNat(v_i_61_);
v___x_72_ = l_Lean_instToExprInt_mkNat(v___x_71_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt___lam__0___boxed(lean_object* v_i_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lean_instToExprInt___lam__0(v_i_73_);
lean_dec(v_i_73_);
return v_res_74_;
}
}
static lean_object* _init_l_Lean_instToExprInt___closed__1(void){
_start:
{
lean_object* v___x_76_; lean_object* v___f_77_; lean_object* v___x_78_; 
v___x_76_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__8, &l_Lean_instToExprInt_mkNat___closed__8_once, _init_l_Lean_instToExprInt_mkNat___closed__8);
v___f_77_ = ((lean_object*)(l_Lean_instToExprInt___closed__0));
v___x_78_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_78_, 0, v___f_77_);
lean_ctor_set(v___x_78_, 1, v___x_76_);
return v___x_78_;
}
}
static lean_object* _init_l_Lean_instToExprInt(void){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = lean_obj_once(&l_Lean_instToExprInt___closed__1, &l_Lean_instToExprInt___closed__1_once, _init_l_Lean_instToExprInt___closed__1);
return v___x_79_;
}
}
static lean_object* _init_l_Lean_instToExprRat_mkNat___closed__2(void){
_start:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = lean_box(0);
v___x_84_ = ((lean_object*)(l_Lean_instToExprRat_mkNat___closed__1));
v___x_85_ = l_Lean_Expr_const___override(v___x_84_, v___x_83_);
return v___x_85_;
}
}
static lean_object* _init_l_Lean_instToExprRat_mkNat___closed__4(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_89_ = lean_box(0);
v___x_90_ = ((lean_object*)(l_Lean_instToExprRat_mkNat___closed__3));
v___x_91_ = l_Lean_Expr_const___override(v___x_90_, v___x_89_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprRat_mkNat(lean_object* v_n_92_){
_start:
{
lean_object* v_r_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v_r_93_ = l_Lean_mkRawNatLit(v_n_92_);
v___x_94_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_95_ = lean_obj_once(&l_Lean_instToExprRat_mkNat___closed__2, &l_Lean_instToExprRat_mkNat___closed__2_once, _init_l_Lean_instToExprRat_mkNat___closed__2);
v___x_96_ = lean_obj_once(&l_Lean_instToExprRat_mkNat___closed__4, &l_Lean_instToExprRat_mkNat___closed__4_once, _init_l_Lean_instToExprRat_mkNat___closed__4);
lean_inc_ref(v_r_93_);
v___x_97_ = l_Lean_Expr_app___override(v___x_96_, v_r_93_);
v___x_98_ = l_Lean_mkApp3(v___x_94_, v___x_95_, v_r_93_, v___x_97_);
return v___x_98_;
}
}
static lean_object* _init_l_Lean_instToExprRat_mkInt___closed__2(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_box(0);
v___x_104_ = ((lean_object*)(l_Lean_instToExprRat_mkInt___closed__1));
v___x_105_ = l_Lean_Expr_const___override(v___x_104_, v___x_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprRat_mkInt(lean_object* v_i_106_){
_start:
{
lean_object* v___x_107_; uint8_t v___x_108_; 
v___x_107_ = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__0, &l_Lean_instToExprInt___lam__0___closed__0_once, _init_l_Lean_instToExprInt___lam__0___closed__0);
v___x_108_ = lean_int_dec_le(v___x_107_, v_i_106_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v___x_109_ = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__4, &l_Lean_instToExprInt___lam__0___closed__4_once, _init_l_Lean_instToExprInt___lam__0___closed__4);
v___x_110_ = lean_obj_once(&l_Lean_instToExprRat_mkNat___closed__2, &l_Lean_instToExprRat_mkNat___closed__2_once, _init_l_Lean_instToExprRat_mkNat___closed__2);
v___x_111_ = lean_obj_once(&l_Lean_instToExprRat_mkInt___closed__2, &l_Lean_instToExprRat_mkInt___closed__2_once, _init_l_Lean_instToExprRat_mkInt___closed__2);
v___x_112_ = lean_int_neg(v_i_106_);
v___x_113_ = l_Int_toNat(v___x_112_);
lean_dec(v___x_112_);
v___x_114_ = l_Lean_instToExprRat_mkNat(v___x_113_);
v___x_115_ = l_Lean_mkApp3(v___x_109_, v___x_110_, v___x_111_, v___x_114_);
return v___x_115_;
}
else
{
lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_116_ = l_Int_toNat(v_i_106_);
v___x_117_ = l_Lean_instToExprRat_mkNat(v___x_116_);
return v___x_117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprRat_mkInt___boxed(lean_object* v_i_118_){
_start:
{
lean_object* v_res_119_; 
v_res_119_ = l_Lean_instToExprRat_mkInt(v_i_118_);
lean_dec(v_i_118_);
return v_res_119_;
}
}
static lean_object* _init_l_Lean_instToExprRat___lam__0___closed__3(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__4, &l_Lean_instToExprInt_mkNat___closed__4_once, _init_l_Lean_instToExprInt_mkNat___closed__4);
v___x_126_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__3, &l_Lean_instToExprInt_mkNat___closed__3_once, _init_l_Lean_instToExprInt_mkNat___closed__3);
v___x_127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_127_, 0, v___x_126_);
lean_ctor_set(v___x_127_, 1, v___x_125_);
return v___x_127_;
}
}
static lean_object* _init_l_Lean_instToExprRat___lam__0___closed__4(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_128_ = lean_obj_once(&l_Lean_instToExprRat___lam__0___closed__3, &l_Lean_instToExprRat___lam__0___closed__3_once, _init_l_Lean_instToExprRat___lam__0___closed__3);
v___x_129_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__3, &l_Lean_instToExprInt_mkNat___closed__3_once, _init_l_Lean_instToExprInt_mkNat___closed__3);
v___x_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___x_128_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_instToExprRat___lam__0___closed__5(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = lean_obj_once(&l_Lean_instToExprRat___lam__0___closed__4, &l_Lean_instToExprRat___lam__0___closed__4_once, _init_l_Lean_instToExprRat___lam__0___closed__4);
v___x_132_ = ((lean_object*)(l_Lean_instToExprRat___lam__0___closed__2));
v___x_133_ = l_Lean_Expr_const___override(v___x_132_, v___x_131_);
return v___x_133_;
}
}
static lean_object* _init_l_Lean_instToExprRat___lam__0___closed__8(void){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v___x_137_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__4, &l_Lean_instToExprInt_mkNat___closed__4_once, _init_l_Lean_instToExprInt_mkNat___closed__4);
v___x_138_ = ((lean_object*)(l_Lean_instToExprRat___lam__0___closed__7));
v___x_139_ = l_Lean_Expr_const___override(v___x_138_, v___x_137_);
return v___x_139_;
}
}
static lean_object* _init_l_Lean_instToExprRat___lam__0___closed__11(void){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_144_ = lean_box(0);
v___x_145_ = ((lean_object*)(l_Lean_instToExprRat___lam__0___closed__10));
v___x_146_ = l_Lean_Expr_const___override(v___x_145_, v___x_144_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_instToExprRat___lam__0___closed__12(void){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_147_ = lean_obj_once(&l_Lean_instToExprRat___lam__0___closed__11, &l_Lean_instToExprRat___lam__0___closed__11_once, _init_l_Lean_instToExprRat___lam__0___closed__11);
v___x_148_ = lean_obj_once(&l_Lean_instToExprRat_mkNat___closed__2, &l_Lean_instToExprRat_mkNat___closed__2_once, _init_l_Lean_instToExprRat_mkNat___closed__2);
v___x_149_ = lean_obj_once(&l_Lean_instToExprRat___lam__0___closed__8, &l_Lean_instToExprRat___lam__0___closed__8_once, _init_l_Lean_instToExprRat___lam__0___closed__8);
v___x_150_ = l_Lean_mkAppB(v___x_149_, v___x_148_, v___x_147_);
return v___x_150_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprRat___lam__0(lean_object* v_i_151_){
_start:
{
lean_object* v_num_152_; lean_object* v_den_153_; lean_object* v___x_154_; uint8_t v___x_155_; 
v_num_152_ = lean_ctor_get(v_i_151_, 0);
lean_inc(v_num_152_);
v_den_153_ = lean_ctor_get(v_i_151_, 1);
lean_inc(v_den_153_);
lean_dec_ref(v_i_151_);
v___x_154_ = lean_unsigned_to_nat(1u);
v___x_155_ = lean_nat_dec_eq(v_den_153_, v___x_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_156_ = lean_obj_once(&l_Lean_instToExprRat___lam__0___closed__5, &l_Lean_instToExprRat___lam__0___closed__5_once, _init_l_Lean_instToExprRat___lam__0___closed__5);
v___x_157_ = lean_obj_once(&l_Lean_instToExprRat_mkNat___closed__2, &l_Lean_instToExprRat_mkNat___closed__2_once, _init_l_Lean_instToExprRat_mkNat___closed__2);
v___x_158_ = lean_obj_once(&l_Lean_instToExprRat___lam__0___closed__12, &l_Lean_instToExprRat___lam__0___closed__12_once, _init_l_Lean_instToExprRat___lam__0___closed__12);
v___x_159_ = l_Lean_instToExprRat_mkInt(v_num_152_);
lean_dec(v_num_152_);
v___x_160_ = lean_nat_to_int(v_den_153_);
v___x_161_ = l_Lean_instToExprRat_mkInt(v___x_160_);
lean_dec(v___x_160_);
v___x_162_ = l_Lean_mkApp6(v___x_156_, v___x_157_, v___x_157_, v___x_157_, v___x_158_, v___x_159_, v___x_161_);
return v___x_162_;
}
else
{
lean_object* v___x_163_; 
lean_dec(v_den_153_);
v___x_163_ = l_Lean_instToExprRat_mkInt(v_num_152_);
lean_dec(v_num_152_);
return v___x_163_;
}
}
}
static lean_object* _init_l_Lean_instToExprRat___closed__1(void){
_start:
{
lean_object* v___x_165_; lean_object* v___f_166_; lean_object* v___x_167_; 
v___x_165_ = lean_obj_once(&l_Lean_instToExprRat_mkNat___closed__2, &l_Lean_instToExprRat_mkNat___closed__2_once, _init_l_Lean_instToExprRat_mkNat___closed__2);
v___f_166_ = ((lean_object*)(l_Lean_instToExprRat___closed__0));
v___x_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_167_, 0, v___f_166_);
lean_ctor_set(v___x_167_, 1, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_instToExprRat(void){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = lean_obj_once(&l_Lean_instToExprRat___closed__1, &l_Lean_instToExprRat___closed__1_once, _init_l_Lean_instToExprRat___closed__1);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_instToExprFin___lam__0___closed__2(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_172_ = lean_box(0);
v___x_173_ = ((lean_object*)(l_Lean_instToExprFin___lam__0___closed__1));
v___x_174_ = l_Lean_mkConst(v___x_173_, v___x_172_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_instToExprFin___lam__0___closed__4(void){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_178_ = lean_box(0);
v___x_179_ = ((lean_object*)(l_Lean_instToExprFin___lam__0___closed__3));
v___x_180_ = l_Lean_Expr_const___override(v___x_179_, v___x_178_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_instToExprFin___lam__0___closed__7(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_box(0);
v___x_186_ = ((lean_object*)(l_Lean_instToExprFin___lam__0___closed__6));
v___x_187_ = l_Lean_Expr_const___override(v___x_186_, v___x_185_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprFin___lam__0(lean_object* v_n_188_, lean_object* v_a_189_){
_start:
{
lean_object* v_r_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v_r_190_ = l_Lean_mkRawNatLit(v_a_189_);
v___x_191_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_192_ = lean_obj_once(&l_Lean_instToExprFin___lam__0___closed__2, &l_Lean_instToExprFin___lam__0___closed__2_once, _init_l_Lean_instToExprFin___lam__0___closed__2);
lean_inc(v_n_188_);
v___x_193_ = l_Lean_mkNatLit(v_n_188_);
lean_inc_ref(v___x_193_);
v___x_194_ = l_Lean_Expr_app___override(v___x_192_, v___x_193_);
v___x_195_ = lean_obj_once(&l_Lean_instToExprFin___lam__0___closed__4, &l_Lean_instToExprFin___lam__0___closed__4_once, _init_l_Lean_instToExprFin___lam__0___closed__4);
v___x_196_ = lean_obj_once(&l_Lean_instToExprFin___lam__0___closed__7, &l_Lean_instToExprFin___lam__0___closed__7_once, _init_l_Lean_instToExprFin___lam__0___closed__7);
v___x_197_ = lean_unsigned_to_nat(1u);
v___x_198_ = lean_nat_sub(v_n_188_, v___x_197_);
lean_dec(v_n_188_);
v___x_199_ = l_Lean_mkNatLit(v___x_198_);
v___x_200_ = l_Lean_Expr_app___override(v___x_196_, v___x_199_);
lean_inc_ref(v_r_190_);
v___x_201_ = l_Lean_mkApp3(v___x_195_, v___x_193_, v___x_200_, v_r_190_);
v___x_202_ = l_Lean_mkApp3(v___x_191_, v___x_194_, v_r_190_, v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprFin(lean_object* v_n_203_){
_start:
{
lean_object* v___f_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
lean_inc(v_n_203_);
v___f_204_ = lean_alloc_closure((void*)(l_Lean_instToExprFin___lam__0), 2, 1);
lean_closure_set(v___f_204_, 0, v_n_203_);
v___x_205_ = lean_obj_once(&l_Lean_instToExprFin___lam__0___closed__2, &l_Lean_instToExprFin___lam__0___closed__2_once, _init_l_Lean_instToExprFin___lam__0___closed__2);
v___x_206_ = l_Lean_mkNatLit(v_n_203_);
v___x_207_ = l_Lean_Expr_app___override(v___x_205_, v___x_206_);
v___x_208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_208_, 0, v___f_204_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_instToExprBitVec___lam__0___closed__2(void){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_213_ = lean_box(0);
v___x_214_ = ((lean_object*)(l_Lean_instToExprBitVec___lam__0___closed__1));
v___x_215_ = l_Lean_Expr_const___override(v___x_214_, v___x_213_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprBitVec___lam__0(lean_object* v_n_216_, lean_object* v_a_217_){
_start:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v___x_218_ = lean_obj_once(&l_Lean_instToExprBitVec___lam__0___closed__2, &l_Lean_instToExprBitVec___lam__0___closed__2_once, _init_l_Lean_instToExprBitVec___lam__0___closed__2);
v___x_219_ = l_Lean_mkNatLit(v_n_216_);
v___x_220_ = l_Lean_mkNatLit(v_a_217_);
v___x_221_ = l_Lean_mkAppB(v___x_218_, v___x_219_, v___x_220_);
return v___x_221_;
}
}
static lean_object* _init_l_Lean_instToExprBitVec___closed__1(void){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_224_ = lean_box(0);
v___x_225_ = ((lean_object*)(l_Lean_instToExprBitVec___closed__0));
v___x_226_ = l_Lean_mkConst(v___x_225_, v___x_224_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprBitVec(lean_object* v_n_227_){
_start:
{
lean_object* v___f_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
lean_inc(v_n_227_);
v___f_228_ = lean_alloc_closure((void*)(l_Lean_instToExprBitVec___lam__0), 2, 1);
lean_closure_set(v___f_228_, 0, v_n_227_);
v___x_229_ = lean_obj_once(&l_Lean_instToExprBitVec___closed__1, &l_Lean_instToExprBitVec___closed__1_once, _init_l_Lean_instToExprBitVec___closed__1);
v___x_230_ = l_Lean_mkNatLit(v_n_227_);
v___x_231_ = l_Lean_Expr_app___override(v___x_229_, v___x_230_);
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v___f_228_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
return v___x_232_;
}
}
static lean_object* _init_l_Lean_instToExprUInt8___lam__0___closed__2(void){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_236_ = lean_box(0);
v___x_237_ = ((lean_object*)(l_Lean_instToExprUInt8___lam__0___closed__1));
v___x_238_ = l_Lean_mkConst(v___x_237_, v___x_236_);
return v___x_238_;
}
}
static lean_object* _init_l_Lean_instToExprUInt8___lam__0___closed__4(void){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_242_ = lean_box(0);
v___x_243_ = ((lean_object*)(l_Lean_instToExprUInt8___lam__0___closed__3));
v___x_244_ = l_Lean_Expr_const___override(v___x_243_, v___x_242_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt8___lam__0(uint8_t v_a_245_){
_start:
{
lean_object* v___x_246_; lean_object* v_r_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___x_246_ = lean_uint8_to_nat(v_a_245_);
v_r_247_ = l_Lean_mkRawNatLit(v___x_246_);
v___x_248_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_249_ = lean_obj_once(&l_Lean_instToExprUInt8___lam__0___closed__2, &l_Lean_instToExprUInt8___lam__0___closed__2_once, _init_l_Lean_instToExprUInt8___lam__0___closed__2);
v___x_250_ = lean_obj_once(&l_Lean_instToExprUInt8___lam__0___closed__4, &l_Lean_instToExprUInt8___lam__0___closed__4_once, _init_l_Lean_instToExprUInt8___lam__0___closed__4);
lean_inc_ref(v_r_247_);
v___x_251_ = l_Lean_Expr_app___override(v___x_250_, v_r_247_);
v___x_252_ = l_Lean_mkApp3(v___x_248_, v___x_249_, v_r_247_, v___x_251_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt8___lam__0___boxed(lean_object* v_a_253_){
_start:
{
uint8_t v_a_boxed_254_; lean_object* v_res_255_; 
v_a_boxed_254_ = lean_unbox(v_a_253_);
v_res_255_ = l_Lean_instToExprUInt8___lam__0(v_a_boxed_254_);
return v_res_255_;
}
}
static lean_object* _init_l_Lean_instToExprUInt8___closed__1(void){
_start:
{
lean_object* v___x_257_; lean_object* v___f_258_; lean_object* v___x_259_; 
v___x_257_ = lean_obj_once(&l_Lean_instToExprUInt8___lam__0___closed__2, &l_Lean_instToExprUInt8___lam__0___closed__2_once, _init_l_Lean_instToExprUInt8___lam__0___closed__2);
v___f_258_ = ((lean_object*)(l_Lean_instToExprUInt8___closed__0));
v___x_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_259_, 0, v___f_258_);
lean_ctor_set(v___x_259_, 1, v___x_257_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_instToExprUInt8(void){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = lean_obj_once(&l_Lean_instToExprUInt8___closed__1, &l_Lean_instToExprUInt8___closed__1_once, _init_l_Lean_instToExprUInt8___closed__1);
return v___x_260_;
}
}
static lean_object* _init_l_Lean_instToExprUInt16___lam__0___closed__2(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_264_ = lean_box(0);
v___x_265_ = ((lean_object*)(l_Lean_instToExprUInt16___lam__0___closed__1));
v___x_266_ = l_Lean_mkConst(v___x_265_, v___x_264_);
return v___x_266_;
}
}
static lean_object* _init_l_Lean_instToExprUInt16___lam__0___closed__4(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_270_ = lean_box(0);
v___x_271_ = ((lean_object*)(l_Lean_instToExprUInt16___lam__0___closed__3));
v___x_272_ = l_Lean_Expr_const___override(v___x_271_, v___x_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt16___lam__0(uint16_t v_a_273_){
_start:
{
lean_object* v___x_274_; lean_object* v_r_275_; lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_274_ = lean_uint16_to_nat(v_a_273_);
v_r_275_ = l_Lean_mkRawNatLit(v___x_274_);
v___x_276_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_277_ = lean_obj_once(&l_Lean_instToExprUInt16___lam__0___closed__2, &l_Lean_instToExprUInt16___lam__0___closed__2_once, _init_l_Lean_instToExprUInt16___lam__0___closed__2);
v___x_278_ = lean_obj_once(&l_Lean_instToExprUInt16___lam__0___closed__4, &l_Lean_instToExprUInt16___lam__0___closed__4_once, _init_l_Lean_instToExprUInt16___lam__0___closed__4);
lean_inc_ref(v_r_275_);
v___x_279_ = l_Lean_Expr_app___override(v___x_278_, v_r_275_);
v___x_280_ = l_Lean_mkApp3(v___x_276_, v___x_277_, v_r_275_, v___x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt16___lam__0___boxed(lean_object* v_a_281_){
_start:
{
uint16_t v_a_boxed_282_; lean_object* v_res_283_; 
v_a_boxed_282_ = lean_unbox(v_a_281_);
v_res_283_ = l_Lean_instToExprUInt16___lam__0(v_a_boxed_282_);
return v_res_283_;
}
}
static lean_object* _init_l_Lean_instToExprUInt16___closed__1(void){
_start:
{
lean_object* v___x_285_; lean_object* v___f_286_; lean_object* v___x_287_; 
v___x_285_ = lean_obj_once(&l_Lean_instToExprUInt16___lam__0___closed__2, &l_Lean_instToExprUInt16___lam__0___closed__2_once, _init_l_Lean_instToExprUInt16___lam__0___closed__2);
v___f_286_ = ((lean_object*)(l_Lean_instToExprUInt16___closed__0));
v___x_287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_287_, 0, v___f_286_);
lean_ctor_set(v___x_287_, 1, v___x_285_);
return v___x_287_;
}
}
static lean_object* _init_l_Lean_instToExprUInt16(void){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_obj_once(&l_Lean_instToExprUInt16___closed__1, &l_Lean_instToExprUInt16___closed__1_once, _init_l_Lean_instToExprUInt16___closed__1);
return v___x_288_;
}
}
static lean_object* _init_l_Lean_instToExprUInt32___lam__0___closed__2(void){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_292_ = lean_box(0);
v___x_293_ = ((lean_object*)(l_Lean_instToExprUInt32___lam__0___closed__1));
v___x_294_ = l_Lean_mkConst(v___x_293_, v___x_292_);
return v___x_294_;
}
}
static lean_object* _init_l_Lean_instToExprUInt32___lam__0___closed__4(void){
_start:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_298_ = lean_box(0);
v___x_299_ = ((lean_object*)(l_Lean_instToExprUInt32___lam__0___closed__3));
v___x_300_ = l_Lean_Expr_const___override(v___x_299_, v___x_298_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt32___lam__0(uint32_t v_a_301_){
_start:
{
lean_object* v___x_302_; lean_object* v_r_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_302_ = lean_uint32_to_nat(v_a_301_);
v_r_303_ = l_Lean_mkRawNatLit(v___x_302_);
v___x_304_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_305_ = lean_obj_once(&l_Lean_instToExprUInt32___lam__0___closed__2, &l_Lean_instToExprUInt32___lam__0___closed__2_once, _init_l_Lean_instToExprUInt32___lam__0___closed__2);
v___x_306_ = lean_obj_once(&l_Lean_instToExprUInt32___lam__0___closed__4, &l_Lean_instToExprUInt32___lam__0___closed__4_once, _init_l_Lean_instToExprUInt32___lam__0___closed__4);
lean_inc_ref(v_r_303_);
v___x_307_ = l_Lean_Expr_app___override(v___x_306_, v_r_303_);
v___x_308_ = l_Lean_mkApp3(v___x_304_, v___x_305_, v_r_303_, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt32___lam__0___boxed(lean_object* v_a_309_){
_start:
{
uint32_t v_a_boxed_310_; lean_object* v_res_311_; 
v_a_boxed_310_ = lean_unbox_uint32(v_a_309_);
lean_dec(v_a_309_);
v_res_311_ = l_Lean_instToExprUInt32___lam__0(v_a_boxed_310_);
return v_res_311_;
}
}
static lean_object* _init_l_Lean_instToExprUInt32___closed__1(void){
_start:
{
lean_object* v___x_313_; lean_object* v___f_314_; lean_object* v___x_315_; 
v___x_313_ = lean_obj_once(&l_Lean_instToExprUInt32___lam__0___closed__2, &l_Lean_instToExprUInt32___lam__0___closed__2_once, _init_l_Lean_instToExprUInt32___lam__0___closed__2);
v___f_314_ = ((lean_object*)(l_Lean_instToExprUInt32___closed__0));
v___x_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_315_, 0, v___f_314_);
lean_ctor_set(v___x_315_, 1, v___x_313_);
return v___x_315_;
}
}
static lean_object* _init_l_Lean_instToExprUInt32(void){
_start:
{
lean_object* v___x_316_; 
v___x_316_ = lean_obj_once(&l_Lean_instToExprUInt32___closed__1, &l_Lean_instToExprUInt32___closed__1_once, _init_l_Lean_instToExprUInt32___closed__1);
return v___x_316_;
}
}
static lean_object* _init_l_Lean_instToExprUInt64___lam__0___closed__2(void){
_start:
{
lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; 
v___x_320_ = lean_box(0);
v___x_321_ = ((lean_object*)(l_Lean_instToExprUInt64___lam__0___closed__1));
v___x_322_ = l_Lean_mkConst(v___x_321_, v___x_320_);
return v___x_322_;
}
}
static lean_object* _init_l_Lean_instToExprUInt64___lam__0___closed__4(void){
_start:
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v___x_326_ = lean_box(0);
v___x_327_ = ((lean_object*)(l_Lean_instToExprUInt64___lam__0___closed__3));
v___x_328_ = l_Lean_Expr_const___override(v___x_327_, v___x_326_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt64___lam__0(uint64_t v_a_329_){
_start:
{
lean_object* v___x_330_; lean_object* v_r_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_330_ = lean_uint64_to_nat(v_a_329_);
v_r_331_ = l_Lean_mkRawNatLit(v___x_330_);
v___x_332_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_333_ = lean_obj_once(&l_Lean_instToExprUInt64___lam__0___closed__2, &l_Lean_instToExprUInt64___lam__0___closed__2_once, _init_l_Lean_instToExprUInt64___lam__0___closed__2);
v___x_334_ = lean_obj_once(&l_Lean_instToExprUInt64___lam__0___closed__4, &l_Lean_instToExprUInt64___lam__0___closed__4_once, _init_l_Lean_instToExprUInt64___lam__0___closed__4);
lean_inc_ref(v_r_331_);
v___x_335_ = l_Lean_Expr_app___override(v___x_334_, v_r_331_);
v___x_336_ = l_Lean_mkApp3(v___x_332_, v___x_333_, v_r_331_, v___x_335_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt64___lam__0___boxed(lean_object* v_a_337_){
_start:
{
uint64_t v_a_boxed_338_; lean_object* v_res_339_; 
v_a_boxed_338_ = lean_unbox_uint64(v_a_337_);
lean_dec_ref(v_a_337_);
v_res_339_ = l_Lean_instToExprUInt64___lam__0(v_a_boxed_338_);
return v_res_339_;
}
}
static lean_object* _init_l_Lean_instToExprUInt64___closed__1(void){
_start:
{
lean_object* v___x_341_; lean_object* v___f_342_; lean_object* v___x_343_; 
v___x_341_ = lean_obj_once(&l_Lean_instToExprUInt64___lam__0___closed__2, &l_Lean_instToExprUInt64___lam__0___closed__2_once, _init_l_Lean_instToExprUInt64___lam__0___closed__2);
v___f_342_ = ((lean_object*)(l_Lean_instToExprUInt64___closed__0));
v___x_343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_343_, 0, v___f_342_);
lean_ctor_set(v___x_343_, 1, v___x_341_);
return v___x_343_;
}
}
static lean_object* _init_l_Lean_instToExprUInt64(void){
_start:
{
lean_object* v___x_344_; 
v___x_344_ = lean_obj_once(&l_Lean_instToExprUInt64___closed__1, &l_Lean_instToExprUInt64___closed__1_once, _init_l_Lean_instToExprUInt64___closed__1);
return v___x_344_;
}
}
static lean_object* _init_l_Lean_instToExprUSize___lam__0___closed__2(void){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_348_ = lean_box(0);
v___x_349_ = ((lean_object*)(l_Lean_instToExprUSize___lam__0___closed__1));
v___x_350_ = l_Lean_mkConst(v___x_349_, v___x_348_);
return v___x_350_;
}
}
static lean_object* _init_l_Lean_instToExprUSize___lam__0___closed__4(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v___x_354_ = lean_box(0);
v___x_355_ = ((lean_object*)(l_Lean_instToExprUSize___lam__0___closed__3));
v___x_356_ = l_Lean_Expr_const___override(v___x_355_, v___x_354_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUSize___lam__0(size_t v_a_357_){
_start:
{
lean_object* v___x_358_; lean_object* v_r_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_358_ = lean_usize_to_nat(v_a_357_);
v_r_359_ = l_Lean_mkRawNatLit(v___x_358_);
v___x_360_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_361_ = lean_obj_once(&l_Lean_instToExprUSize___lam__0___closed__2, &l_Lean_instToExprUSize___lam__0___closed__2_once, _init_l_Lean_instToExprUSize___lam__0___closed__2);
v___x_362_ = lean_obj_once(&l_Lean_instToExprUSize___lam__0___closed__4, &l_Lean_instToExprUSize___lam__0___closed__4_once, _init_l_Lean_instToExprUSize___lam__0___closed__4);
lean_inc_ref(v_r_359_);
v___x_363_ = l_Lean_Expr_app___override(v___x_362_, v_r_359_);
v___x_364_ = l_Lean_mkApp3(v___x_360_, v___x_361_, v_r_359_, v___x_363_);
return v___x_364_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUSize___lam__0___boxed(lean_object* v_a_365_){
_start:
{
size_t v_a_boxed_366_; lean_object* v_res_367_; 
v_a_boxed_366_ = lean_unbox_usize(v_a_365_);
lean_dec(v_a_365_);
v_res_367_ = l_Lean_instToExprUSize___lam__0(v_a_boxed_366_);
return v_res_367_;
}
}
static lean_object* _init_l_Lean_instToExprUSize___closed__1(void){
_start:
{
lean_object* v___x_369_; lean_object* v___f_370_; lean_object* v___x_371_; 
v___x_369_ = lean_obj_once(&l_Lean_instToExprUSize___lam__0___closed__2, &l_Lean_instToExprUSize___lam__0___closed__2_once, _init_l_Lean_instToExprUSize___lam__0___closed__2);
v___f_370_ = ((lean_object*)(l_Lean_instToExprUSize___closed__0));
v___x_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_371_, 0, v___f_370_);
lean_ctor_set(v___x_371_, 1, v___x_369_);
return v___x_371_;
}
}
static lean_object* _init_l_Lean_instToExprUSize(void){
_start:
{
lean_object* v___x_372_; 
v___x_372_ = lean_obj_once(&l_Lean_instToExprUSize___closed__1, &l_Lean_instToExprUSize___closed__1_once, _init_l_Lean_instToExprUSize___closed__1);
return v___x_372_;
}
}
static lean_object* _init_l_Lean_instToExprInt8_mkNat___closed__2(void){
_start:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; 
v___x_376_ = lean_box(0);
v___x_377_ = ((lean_object*)(l_Lean_instToExprInt8_mkNat___closed__1));
v___x_378_ = l_Lean_Expr_const___override(v___x_377_, v___x_376_);
return v___x_378_;
}
}
static lean_object* _init_l_Lean_instToExprInt8_mkNat___closed__4(void){
_start:
{
lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; 
v___x_382_ = lean_box(0);
v___x_383_ = ((lean_object*)(l_Lean_instToExprInt8_mkNat___closed__3));
v___x_384_ = l_Lean_Expr_const___override(v___x_383_, v___x_382_);
return v___x_384_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt8_mkNat(lean_object* v_n_385_){
_start:
{
lean_object* v_r_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v_r_386_ = l_Lean_mkRawNatLit(v_n_385_);
v___x_387_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_388_ = lean_obj_once(&l_Lean_instToExprInt8_mkNat___closed__2, &l_Lean_instToExprInt8_mkNat___closed__2_once, _init_l_Lean_instToExprInt8_mkNat___closed__2);
v___x_389_ = lean_obj_once(&l_Lean_instToExprInt8_mkNat___closed__4, &l_Lean_instToExprInt8_mkNat___closed__4_once, _init_l_Lean_instToExprInt8_mkNat___closed__4);
lean_inc_ref(v_r_386_);
v___x_390_ = l_Lean_Expr_app___override(v___x_389_, v_r_386_);
v___x_391_ = l_Lean_mkApp3(v___x_387_, v___x_388_, v_r_386_, v___x_390_);
return v___x_391_;
}
}
static uint8_t _init_l_Lean_instToExprInt8___lam__0___closed__0(void){
_start:
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = lean_unsigned_to_nat(0u);
v___x_393_ = lean_int8_of_nat(v___x_392_);
return v___x_393_;
}
}
static lean_object* _init_l_Lean_instToExprInt8___lam__0___closed__2(void){
_start:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
v___x_397_ = lean_box(0);
v___x_398_ = ((lean_object*)(l_Lean_instToExprInt8___lam__0___closed__1));
v___x_399_ = l_Lean_Expr_const___override(v___x_398_, v___x_397_);
return v___x_399_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt8___lam__0(uint8_t v_i_400_){
_start:
{
uint8_t v___x_401_; uint8_t v___x_402_; 
v___x_401_ = lean_uint8_once(&l_Lean_instToExprInt8___lam__0___closed__0, &l_Lean_instToExprInt8___lam__0___closed__0_once, _init_l_Lean_instToExprInt8___lam__0___closed__0);
v___x_402_ = lean_int8_dec_le(v___x_401_, v_i_400_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; 
v___x_403_ = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__4, &l_Lean_instToExprInt___lam__0___closed__4_once, _init_l_Lean_instToExprInt___lam__0___closed__4);
v___x_404_ = lean_obj_once(&l_Lean_instToExprInt8_mkNat___closed__2, &l_Lean_instToExprInt8_mkNat___closed__2_once, _init_l_Lean_instToExprInt8_mkNat___closed__2);
v___x_405_ = lean_obj_once(&l_Lean_instToExprInt8___lam__0___closed__2, &l_Lean_instToExprInt8___lam__0___closed__2_once, _init_l_Lean_instToExprInt8___lam__0___closed__2);
v___x_406_ = lean_int8_to_int(v_i_400_);
v___x_407_ = lean_int_neg(v___x_406_);
v___x_408_ = l_Int_toNat(v___x_407_);
lean_dec(v___x_407_);
v___x_409_ = l_Lean_instToExprInt8_mkNat(v___x_408_);
v___x_410_ = l_Lean_mkApp3(v___x_403_, v___x_404_, v___x_405_, v___x_409_);
return v___x_410_;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_411_ = lean_int8_to_int(v_i_400_);
v___x_412_ = l_Int_toNat(v___x_411_);
v___x_413_ = l_Lean_instToExprInt8_mkNat(v___x_412_);
return v___x_413_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt8___lam__0___boxed(lean_object* v_i_414_){
_start:
{
uint8_t v_i_boxed_415_; lean_object* v_res_416_; 
v_i_boxed_415_ = lean_unbox(v_i_414_);
v_res_416_ = l_Lean_instToExprInt8___lam__0(v_i_boxed_415_);
return v_res_416_;
}
}
static lean_object* _init_l_Lean_instToExprInt8___closed__1(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = lean_box(0);
v___x_419_ = ((lean_object*)(l_Lean_instToExprInt8_mkNat___closed__1));
v___x_420_ = l_Lean_mkConst(v___x_419_, v___x_418_);
return v___x_420_;
}
}
static lean_object* _init_l_Lean_instToExprInt8___closed__2(void){
_start:
{
lean_object* v___x_421_; lean_object* v___f_422_; lean_object* v___x_423_; 
v___x_421_ = lean_obj_once(&l_Lean_instToExprInt8___closed__1, &l_Lean_instToExprInt8___closed__1_once, _init_l_Lean_instToExprInt8___closed__1);
v___f_422_ = ((lean_object*)(l_Lean_instToExprInt8___closed__0));
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v___f_422_);
lean_ctor_set(v___x_423_, 1, v___x_421_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_instToExprInt8(void){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = lean_obj_once(&l_Lean_instToExprInt8___closed__2, &l_Lean_instToExprInt8___closed__2_once, _init_l_Lean_instToExprInt8___closed__2);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_instToExprInt16_mkNat___closed__2(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = lean_box(0);
v___x_429_ = ((lean_object*)(l_Lean_instToExprInt16_mkNat___closed__1));
v___x_430_ = l_Lean_Expr_const___override(v___x_429_, v___x_428_);
return v___x_430_;
}
}
static lean_object* _init_l_Lean_instToExprInt16_mkNat___closed__4(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = lean_box(0);
v___x_435_ = ((lean_object*)(l_Lean_instToExprInt16_mkNat___closed__3));
v___x_436_ = l_Lean_Expr_const___override(v___x_435_, v___x_434_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt16_mkNat(lean_object* v_n_437_){
_start:
{
lean_object* v_r_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v_r_438_ = l_Lean_mkRawNatLit(v_n_437_);
v___x_439_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_440_ = lean_obj_once(&l_Lean_instToExprInt16_mkNat___closed__2, &l_Lean_instToExprInt16_mkNat___closed__2_once, _init_l_Lean_instToExprInt16_mkNat___closed__2);
v___x_441_ = lean_obj_once(&l_Lean_instToExprInt16_mkNat___closed__4, &l_Lean_instToExprInt16_mkNat___closed__4_once, _init_l_Lean_instToExprInt16_mkNat___closed__4);
lean_inc_ref(v_r_438_);
v___x_442_ = l_Lean_Expr_app___override(v___x_441_, v_r_438_);
v___x_443_ = l_Lean_mkApp3(v___x_439_, v___x_440_, v_r_438_, v___x_442_);
return v___x_443_;
}
}
static uint16_t _init_l_Lean_instToExprInt16___lam__0___closed__0(void){
_start:
{
lean_object* v___x_444_; uint16_t v___x_445_; 
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = lean_int16_of_nat(v___x_444_);
return v___x_445_;
}
}
static lean_object* _init_l_Lean_instToExprInt16___lam__0___closed__2(void){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_449_ = lean_box(0);
v___x_450_ = ((lean_object*)(l_Lean_instToExprInt16___lam__0___closed__1));
v___x_451_ = l_Lean_Expr_const___override(v___x_450_, v___x_449_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt16___lam__0(uint16_t v_i_452_){
_start:
{
uint16_t v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_uint16_once(&l_Lean_instToExprInt16___lam__0___closed__0, &l_Lean_instToExprInt16___lam__0___closed__0_once, _init_l_Lean_instToExprInt16___lam__0___closed__0);
v___x_454_ = lean_int16_dec_le(v___x_453_, v_i_452_);
if (v___x_454_ == 0)
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v___x_455_ = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__4, &l_Lean_instToExprInt___lam__0___closed__4_once, _init_l_Lean_instToExprInt___lam__0___closed__4);
v___x_456_ = lean_obj_once(&l_Lean_instToExprInt16_mkNat___closed__2, &l_Lean_instToExprInt16_mkNat___closed__2_once, _init_l_Lean_instToExprInt16_mkNat___closed__2);
v___x_457_ = lean_obj_once(&l_Lean_instToExprInt16___lam__0___closed__2, &l_Lean_instToExprInt16___lam__0___closed__2_once, _init_l_Lean_instToExprInt16___lam__0___closed__2);
v___x_458_ = lean_int16_to_int(v_i_452_);
v___x_459_ = lean_int_neg(v___x_458_);
v___x_460_ = l_Int_toNat(v___x_459_);
lean_dec(v___x_459_);
v___x_461_ = l_Lean_instToExprInt16_mkNat(v___x_460_);
v___x_462_ = l_Lean_mkApp3(v___x_455_, v___x_456_, v___x_457_, v___x_461_);
return v___x_462_;
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v___x_463_ = lean_int16_to_int(v_i_452_);
v___x_464_ = l_Int_toNat(v___x_463_);
v___x_465_ = l_Lean_instToExprInt16_mkNat(v___x_464_);
return v___x_465_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt16___lam__0___boxed(lean_object* v_i_466_){
_start:
{
uint16_t v_i_boxed_467_; lean_object* v_res_468_; 
v_i_boxed_467_ = lean_unbox(v_i_466_);
v_res_468_ = l_Lean_instToExprInt16___lam__0(v_i_boxed_467_);
return v_res_468_;
}
}
static lean_object* _init_l_Lean_instToExprInt16___closed__1(void){
_start:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_470_ = lean_box(0);
v___x_471_ = ((lean_object*)(l_Lean_instToExprInt16_mkNat___closed__1));
v___x_472_ = l_Lean_mkConst(v___x_471_, v___x_470_);
return v___x_472_;
}
}
static lean_object* _init_l_Lean_instToExprInt16___closed__2(void){
_start:
{
lean_object* v___x_473_; lean_object* v___f_474_; lean_object* v___x_475_; 
v___x_473_ = lean_obj_once(&l_Lean_instToExprInt16___closed__1, &l_Lean_instToExprInt16___closed__1_once, _init_l_Lean_instToExprInt16___closed__1);
v___f_474_ = ((lean_object*)(l_Lean_instToExprInt16___closed__0));
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v___f_474_);
lean_ctor_set(v___x_475_, 1, v___x_473_);
return v___x_475_;
}
}
static lean_object* _init_l_Lean_instToExprInt16(void){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = lean_obj_once(&l_Lean_instToExprInt16___closed__2, &l_Lean_instToExprInt16___closed__2_once, _init_l_Lean_instToExprInt16___closed__2);
return v___x_476_;
}
}
static lean_object* _init_l_Lean_instToExprInt32_mkNat___closed__2(void){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = lean_box(0);
v___x_481_ = ((lean_object*)(l_Lean_instToExprInt32_mkNat___closed__1));
v___x_482_ = l_Lean_Expr_const___override(v___x_481_, v___x_480_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_instToExprInt32_mkNat___closed__4(void){
_start:
{
lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_486_ = lean_box(0);
v___x_487_ = ((lean_object*)(l_Lean_instToExprInt32_mkNat___closed__3));
v___x_488_ = l_Lean_Expr_const___override(v___x_487_, v___x_486_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt32_mkNat(lean_object* v_n_489_){
_start:
{
lean_object* v_r_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v_r_490_ = l_Lean_mkRawNatLit(v_n_489_);
v___x_491_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_492_ = lean_obj_once(&l_Lean_instToExprInt32_mkNat___closed__2, &l_Lean_instToExprInt32_mkNat___closed__2_once, _init_l_Lean_instToExprInt32_mkNat___closed__2);
v___x_493_ = lean_obj_once(&l_Lean_instToExprInt32_mkNat___closed__4, &l_Lean_instToExprInt32_mkNat___closed__4_once, _init_l_Lean_instToExprInt32_mkNat___closed__4);
lean_inc_ref(v_r_490_);
v___x_494_ = l_Lean_Expr_app___override(v___x_493_, v_r_490_);
v___x_495_ = l_Lean_mkApp3(v___x_491_, v___x_492_, v_r_490_, v___x_494_);
return v___x_495_;
}
}
static uint32_t _init_l_Lean_instToExprInt32___lam__0___closed__0(void){
_start:
{
lean_object* v___x_496_; uint32_t v___x_497_; 
v___x_496_ = lean_unsigned_to_nat(0u);
v___x_497_ = lean_int32_of_nat(v___x_496_);
return v___x_497_;
}
}
static lean_object* _init_l_Lean_instToExprInt32___lam__0___closed__2(void){
_start:
{
lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; 
v___x_501_ = lean_box(0);
v___x_502_ = ((lean_object*)(l_Lean_instToExprInt32___lam__0___closed__1));
v___x_503_ = l_Lean_Expr_const___override(v___x_502_, v___x_501_);
return v___x_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt32___lam__0(uint32_t v_i_504_){
_start:
{
uint32_t v___x_505_; uint8_t v___x_506_; 
v___x_505_ = lean_uint32_once(&l_Lean_instToExprInt32___lam__0___closed__0, &l_Lean_instToExprInt32___lam__0___closed__0_once, _init_l_Lean_instToExprInt32___lam__0___closed__0);
v___x_506_ = lean_int32_dec_le(v___x_505_, v_i_504_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_507_ = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__4, &l_Lean_instToExprInt___lam__0___closed__4_once, _init_l_Lean_instToExprInt___lam__0___closed__4);
v___x_508_ = lean_obj_once(&l_Lean_instToExprInt32_mkNat___closed__2, &l_Lean_instToExprInt32_mkNat___closed__2_once, _init_l_Lean_instToExprInt32_mkNat___closed__2);
v___x_509_ = lean_obj_once(&l_Lean_instToExprInt32___lam__0___closed__2, &l_Lean_instToExprInt32___lam__0___closed__2_once, _init_l_Lean_instToExprInt32___lam__0___closed__2);
v___x_510_ = lean_int32_to_int(v_i_504_);
v___x_511_ = lean_int_neg(v___x_510_);
lean_dec(v___x_510_);
v___x_512_ = l_Int_toNat(v___x_511_);
lean_dec(v___x_511_);
v___x_513_ = l_Lean_instToExprInt32_mkNat(v___x_512_);
v___x_514_ = l_Lean_mkApp3(v___x_507_, v___x_508_, v___x_509_, v___x_513_);
return v___x_514_;
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v___x_515_ = lean_int32_to_int(v_i_504_);
v___x_516_ = l_Int_toNat(v___x_515_);
lean_dec(v___x_515_);
v___x_517_ = l_Lean_instToExprInt32_mkNat(v___x_516_);
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt32___lam__0___boxed(lean_object* v_i_518_){
_start:
{
uint32_t v_i_boxed_519_; lean_object* v_res_520_; 
v_i_boxed_519_ = lean_unbox_uint32(v_i_518_);
lean_dec(v_i_518_);
v_res_520_ = l_Lean_instToExprInt32___lam__0(v_i_boxed_519_);
return v_res_520_;
}
}
static lean_object* _init_l_Lean_instToExprInt32___closed__1(void){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_522_ = lean_box(0);
v___x_523_ = ((lean_object*)(l_Lean_instToExprInt32_mkNat___closed__1));
v___x_524_ = l_Lean_mkConst(v___x_523_, v___x_522_);
return v___x_524_;
}
}
static lean_object* _init_l_Lean_instToExprInt32___closed__2(void){
_start:
{
lean_object* v___x_525_; lean_object* v___f_526_; lean_object* v___x_527_; 
v___x_525_ = lean_obj_once(&l_Lean_instToExprInt32___closed__1, &l_Lean_instToExprInt32___closed__1_once, _init_l_Lean_instToExprInt32___closed__1);
v___f_526_ = ((lean_object*)(l_Lean_instToExprInt32___closed__0));
v___x_527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_527_, 0, v___f_526_);
lean_ctor_set(v___x_527_, 1, v___x_525_);
return v___x_527_;
}
}
static lean_object* _init_l_Lean_instToExprInt32(void){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = lean_obj_once(&l_Lean_instToExprInt32___closed__2, &l_Lean_instToExprInt32___closed__2_once, _init_l_Lean_instToExprInt32___closed__2);
return v___x_528_;
}
}
static lean_object* _init_l_Lean_instToExprInt64_mkNat___closed__2(void){
_start:
{
lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; 
v___x_532_ = lean_box(0);
v___x_533_ = ((lean_object*)(l_Lean_instToExprInt64_mkNat___closed__1));
v___x_534_ = l_Lean_Expr_const___override(v___x_533_, v___x_532_);
return v___x_534_;
}
}
static lean_object* _init_l_Lean_instToExprInt64_mkNat___closed__4(void){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = lean_box(0);
v___x_539_ = ((lean_object*)(l_Lean_instToExprInt64_mkNat___closed__3));
v___x_540_ = l_Lean_Expr_const___override(v___x_539_, v___x_538_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt64_mkNat(lean_object* v_n_541_){
_start:
{
lean_object* v_r_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_r_542_ = l_Lean_mkRawNatLit(v_n_541_);
v___x_543_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_544_ = lean_obj_once(&l_Lean_instToExprInt64_mkNat___closed__2, &l_Lean_instToExprInt64_mkNat___closed__2_once, _init_l_Lean_instToExprInt64_mkNat___closed__2);
v___x_545_ = lean_obj_once(&l_Lean_instToExprInt64_mkNat___closed__4, &l_Lean_instToExprInt64_mkNat___closed__4_once, _init_l_Lean_instToExprInt64_mkNat___closed__4);
lean_inc_ref(v_r_542_);
v___x_546_ = l_Lean_Expr_app___override(v___x_545_, v_r_542_);
v___x_547_ = l_Lean_mkApp3(v___x_543_, v___x_544_, v_r_542_, v___x_546_);
return v___x_547_;
}
}
static uint64_t _init_l_Lean_instToExprInt64___lam__0___closed__0(void){
_start:
{
lean_object* v___x_548_; uint64_t v___x_549_; 
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = lean_int64_of_nat(v___x_548_);
return v___x_549_;
}
}
static lean_object* _init_l_Lean_instToExprInt64___lam__0___closed__2(void){
_start:
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_553_ = lean_box(0);
v___x_554_ = ((lean_object*)(l_Lean_instToExprInt64___lam__0___closed__1));
v___x_555_ = l_Lean_Expr_const___override(v___x_554_, v___x_553_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt64___lam__0(uint64_t v_i_556_){
_start:
{
uint64_t v___x_557_; uint8_t v___x_558_; 
v___x_557_ = lean_uint64_once(&l_Lean_instToExprInt64___lam__0___closed__0, &l_Lean_instToExprInt64___lam__0___closed__0_once, _init_l_Lean_instToExprInt64___lam__0___closed__0);
v___x_558_ = lean_int64_dec_le(v___x_557_, v_i_556_);
if (v___x_558_ == 0)
{
lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_559_ = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__4, &l_Lean_instToExprInt___lam__0___closed__4_once, _init_l_Lean_instToExprInt___lam__0___closed__4);
v___x_560_ = lean_obj_once(&l_Lean_instToExprInt64_mkNat___closed__2, &l_Lean_instToExprInt64_mkNat___closed__2_once, _init_l_Lean_instToExprInt64_mkNat___closed__2);
v___x_561_ = lean_obj_once(&l_Lean_instToExprInt64___lam__0___closed__2, &l_Lean_instToExprInt64___lam__0___closed__2_once, _init_l_Lean_instToExprInt64___lam__0___closed__2);
v___x_562_ = lean_int64_to_int_sint(v_i_556_);
v___x_563_ = lean_int_neg(v___x_562_);
lean_dec(v___x_562_);
v___x_564_ = l_Int_toNat(v___x_563_);
lean_dec(v___x_563_);
v___x_565_ = l_Lean_instToExprInt64_mkNat(v___x_564_);
v___x_566_ = l_Lean_mkApp3(v___x_559_, v___x_560_, v___x_561_, v___x_565_);
return v___x_566_;
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_567_ = lean_int64_to_int_sint(v_i_556_);
v___x_568_ = l_Int_toNat(v___x_567_);
lean_dec(v___x_567_);
v___x_569_ = l_Lean_instToExprInt64_mkNat(v___x_568_);
return v___x_569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt64___lam__0___boxed(lean_object* v_i_570_){
_start:
{
uint64_t v_i_boxed_571_; lean_object* v_res_572_; 
v_i_boxed_571_ = lean_unbox_uint64(v_i_570_);
lean_dec_ref(v_i_570_);
v_res_572_ = l_Lean_instToExprInt64___lam__0(v_i_boxed_571_);
return v_res_572_;
}
}
static lean_object* _init_l_Lean_instToExprInt64___closed__1(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = lean_box(0);
v___x_575_ = ((lean_object*)(l_Lean_instToExprInt64_mkNat___closed__1));
v___x_576_ = l_Lean_mkConst(v___x_575_, v___x_574_);
return v___x_576_;
}
}
static lean_object* _init_l_Lean_instToExprInt64___closed__2(void){
_start:
{
lean_object* v___x_577_; lean_object* v___f_578_; lean_object* v___x_579_; 
v___x_577_ = lean_obj_once(&l_Lean_instToExprInt64___closed__1, &l_Lean_instToExprInt64___closed__1_once, _init_l_Lean_instToExprInt64___closed__1);
v___f_578_ = ((lean_object*)(l_Lean_instToExprInt64___closed__0));
v___x_579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_579_, 0, v___f_578_);
lean_ctor_set(v___x_579_, 1, v___x_577_);
return v___x_579_;
}
}
static lean_object* _init_l_Lean_instToExprInt64(void){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = lean_obj_once(&l_Lean_instToExprInt64___closed__2, &l_Lean_instToExprInt64___closed__2_once, _init_l_Lean_instToExprInt64___closed__2);
return v___x_580_;
}
}
static lean_object* _init_l_Lean_instToExprISize_mkNat___closed__2(void){
_start:
{
lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v___x_584_ = lean_box(0);
v___x_585_ = ((lean_object*)(l_Lean_instToExprISize_mkNat___closed__1));
v___x_586_ = l_Lean_Expr_const___override(v___x_585_, v___x_584_);
return v___x_586_;
}
}
static lean_object* _init_l_Lean_instToExprISize_mkNat___closed__4(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_590_ = lean_box(0);
v___x_591_ = ((lean_object*)(l_Lean_instToExprISize_mkNat___closed__3));
v___x_592_ = l_Lean_Expr_const___override(v___x_591_, v___x_590_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprISize_mkNat(lean_object* v_n_593_){
_start:
{
lean_object* v_r_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_r_594_ = l_Lean_mkRawNatLit(v_n_593_);
v___x_595_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_596_ = lean_obj_once(&l_Lean_instToExprISize_mkNat___closed__2, &l_Lean_instToExprISize_mkNat___closed__2_once, _init_l_Lean_instToExprISize_mkNat___closed__2);
v___x_597_ = lean_obj_once(&l_Lean_instToExprISize_mkNat___closed__4, &l_Lean_instToExprISize_mkNat___closed__4_once, _init_l_Lean_instToExprISize_mkNat___closed__4);
lean_inc_ref(v_r_594_);
v___x_598_ = l_Lean_Expr_app___override(v___x_597_, v_r_594_);
v___x_599_ = l_Lean_mkApp3(v___x_595_, v___x_596_, v_r_594_, v___x_598_);
return v___x_599_;
}
}
static size_t _init_l_Lean_instToExprISize___lam__0___closed__0(void){
_start:
{
lean_object* v___x_600_; size_t v___x_601_; 
v___x_600_ = lean_unsigned_to_nat(0u);
v___x_601_ = lean_isize_of_nat(v___x_600_);
return v___x_601_;
}
}
static lean_object* _init_l_Lean_instToExprISize___lam__0___closed__2(void){
_start:
{
lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; 
v___x_605_ = lean_box(0);
v___x_606_ = ((lean_object*)(l_Lean_instToExprISize___lam__0___closed__1));
v___x_607_ = l_Lean_Expr_const___override(v___x_606_, v___x_605_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprISize___lam__0(size_t v_i_608_){
_start:
{
size_t v___x_609_; uint8_t v___x_610_; 
v___x_609_ = lean_usize_once(&l_Lean_instToExprISize___lam__0___closed__0, &l_Lean_instToExprISize___lam__0___closed__0_once, _init_l_Lean_instToExprISize___lam__0___closed__0);
v___x_610_ = lean_isize_dec_le(v___x_609_, v_i_608_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_611_ = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__4, &l_Lean_instToExprInt___lam__0___closed__4_once, _init_l_Lean_instToExprInt___lam__0___closed__4);
v___x_612_ = lean_obj_once(&l_Lean_instToExprISize_mkNat___closed__2, &l_Lean_instToExprISize_mkNat___closed__2_once, _init_l_Lean_instToExprISize_mkNat___closed__2);
v___x_613_ = lean_obj_once(&l_Lean_instToExprISize___lam__0___closed__2, &l_Lean_instToExprISize___lam__0___closed__2_once, _init_l_Lean_instToExprISize___lam__0___closed__2);
v___x_614_ = lean_isize_to_int(v_i_608_);
v___x_615_ = lean_int_neg(v___x_614_);
lean_dec(v___x_614_);
v___x_616_ = l_Int_toNat(v___x_615_);
lean_dec(v___x_615_);
v___x_617_ = l_Lean_instToExprISize_mkNat(v___x_616_);
v___x_618_ = l_Lean_mkApp3(v___x_611_, v___x_612_, v___x_613_, v___x_617_);
return v___x_618_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_619_ = lean_isize_to_int(v_i_608_);
v___x_620_ = l_Int_toNat(v___x_619_);
lean_dec(v___x_619_);
v___x_621_ = l_Lean_instToExprISize_mkNat(v___x_620_);
return v___x_621_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprISize___lam__0___boxed(lean_object* v_i_622_){
_start:
{
size_t v_i_boxed_623_; lean_object* v_res_624_; 
v_i_boxed_623_ = lean_unbox_usize(v_i_622_);
lean_dec(v_i_622_);
v_res_624_ = l_Lean_instToExprISize___lam__0(v_i_boxed_623_);
return v_res_624_;
}
}
static lean_object* _init_l_Lean_instToExprISize___closed__1(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_box(0);
v___x_627_ = ((lean_object*)(l_Lean_instToExprISize_mkNat___closed__1));
v___x_628_ = l_Lean_mkConst(v___x_627_, v___x_626_);
return v___x_628_;
}
}
static lean_object* _init_l_Lean_instToExprISize___closed__2(void){
_start:
{
lean_object* v___x_629_; lean_object* v___f_630_; lean_object* v___x_631_; 
v___x_629_ = lean_obj_once(&l_Lean_instToExprISize___closed__1, &l_Lean_instToExprISize___closed__1_once, _init_l_Lean_instToExprISize___closed__1);
v___f_630_ = ((lean_object*)(l_Lean_instToExprISize___closed__0));
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v___f_630_);
lean_ctor_set(v___x_631_, 1, v___x_629_);
return v___x_631_;
}
}
static lean_object* _init_l_Lean_instToExprISize(void){
_start:
{
lean_object* v___x_632_; 
v___x_632_ = lean_obj_once(&l_Lean_instToExprISize___closed__2, &l_Lean_instToExprISize___closed__2_once, _init_l_Lean_instToExprISize___closed__2);
return v___x_632_;
}
}
static lean_object* _init_l_Lean_instToExprBool___lam__0___closed__3(void){
_start:
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_box(0);
v___x_639_ = ((lean_object*)(l_Lean_instToExprBool___lam__0___closed__2));
v___x_640_ = l_Lean_mkConst(v___x_639_, v___x_638_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_instToExprBool___lam__0___closed__6(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_645_ = lean_box(0);
v___x_646_ = ((lean_object*)(l_Lean_instToExprBool___lam__0___closed__5));
v___x_647_ = l_Lean_mkConst(v___x_646_, v___x_645_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprBool___lam__0(uint8_t v_b_648_){
_start:
{
if (v_b_648_ == 0)
{
lean_object* v___x_649_; 
v___x_649_ = lean_obj_once(&l_Lean_instToExprBool___lam__0___closed__3, &l_Lean_instToExprBool___lam__0___closed__3_once, _init_l_Lean_instToExprBool___lam__0___closed__3);
return v___x_649_;
}
else
{
lean_object* v___x_650_; 
v___x_650_ = lean_obj_once(&l_Lean_instToExprBool___lam__0___closed__6, &l_Lean_instToExprBool___lam__0___closed__6_once, _init_l_Lean_instToExprBool___lam__0___closed__6);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprBool___lam__0___boxed(lean_object* v_b_651_){
_start:
{
uint8_t v_b_boxed_652_; lean_object* v_res_653_; 
v_b_boxed_652_ = lean_unbox(v_b_651_);
v_res_653_ = l_Lean_instToExprBool___lam__0(v_b_boxed_652_);
return v_res_653_;
}
}
static lean_object* _init_l_Lean_instToExprBool___closed__2(void){
_start:
{
lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v___x_657_ = lean_box(0);
v___x_658_ = ((lean_object*)(l_Lean_instToExprBool___closed__1));
v___x_659_ = l_Lean_mkConst(v___x_658_, v___x_657_);
return v___x_659_;
}
}
static lean_object* _init_l_Lean_instToExprBool___closed__3(void){
_start:
{
lean_object* v___x_660_; lean_object* v___f_661_; lean_object* v___x_662_; 
v___x_660_ = lean_obj_once(&l_Lean_instToExprBool___closed__2, &l_Lean_instToExprBool___closed__2_once, _init_l_Lean_instToExprBool___closed__2);
v___f_661_ = ((lean_object*)(l_Lean_instToExprBool___closed__0));
v___x_662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_662_, 0, v___f_661_);
lean_ctor_set(v___x_662_, 1, v___x_660_);
return v___x_662_;
}
}
static lean_object* _init_l_Lean_instToExprBool(void){
_start:
{
lean_object* v___x_663_; 
v___x_663_ = lean_obj_once(&l_Lean_instToExprBool___closed__3, &l_Lean_instToExprBool___closed__3_once, _init_l_Lean_instToExprBool___closed__3);
return v___x_663_;
}
}
static lean_object* _init_l_Lean_instToExprChar___lam__0___closed__2(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = lean_box(0);
v___x_669_ = ((lean_object*)(l_Lean_instToExprChar___lam__0___closed__1));
v___x_670_ = l_Lean_mkConst(v___x_669_, v___x_668_);
return v___x_670_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprChar___lam__0(uint32_t v_c_671_){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_672_ = lean_obj_once(&l_Lean_instToExprChar___lam__0___closed__2, &l_Lean_instToExprChar___lam__0___closed__2_once, _init_l_Lean_instToExprChar___lam__0___closed__2);
v___x_673_ = lean_uint32_to_nat(v_c_671_);
v___x_674_ = l_Lean_mkRawNatLit(v___x_673_);
v___x_675_ = l_Lean_Expr_app___override(v___x_672_, v___x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprChar___lam__0___boxed(lean_object* v_c_676_){
_start:
{
uint32_t v_c_boxed_677_; lean_object* v_res_678_; 
v_c_boxed_677_ = lean_unbox_uint32(v_c_676_);
lean_dec(v_c_676_);
v_res_678_ = l_Lean_instToExprChar___lam__0(v_c_boxed_677_);
return v_res_678_;
}
}
static lean_object* _init_l_Lean_instToExprChar___closed__2(void){
_start:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = lean_box(0);
v___x_683_ = ((lean_object*)(l_Lean_instToExprChar___closed__1));
v___x_684_ = l_Lean_mkConst(v___x_683_, v___x_682_);
return v___x_684_;
}
}
static lean_object* _init_l_Lean_instToExprChar___closed__3(void){
_start:
{
lean_object* v___x_685_; lean_object* v___f_686_; lean_object* v___x_687_; 
v___x_685_ = lean_obj_once(&l_Lean_instToExprChar___closed__2, &l_Lean_instToExprChar___closed__2_once, _init_l_Lean_instToExprChar___closed__2);
v___f_686_ = ((lean_object*)(l_Lean_instToExprChar___closed__0));
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v___f_686_);
lean_ctor_set(v___x_687_, 1, v___x_685_);
return v___x_687_;
}
}
static lean_object* _init_l_Lean_instToExprChar(void){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = lean_obj_once(&l_Lean_instToExprChar___closed__3, &l_Lean_instToExprChar___closed__3_once, _init_l_Lean_instToExprChar___closed__3);
return v___x_688_;
}
}
static lean_object* _init_l_Lean_instToExprString___closed__3(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_693_ = lean_box(0);
v___x_694_ = ((lean_object*)(l_Lean_instToExprString___closed__2));
v___x_695_ = l_Lean_mkConst(v___x_694_, v___x_693_);
return v___x_695_;
}
}
static lean_object* _init_l_Lean_instToExprString___closed__4(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_696_ = lean_obj_once(&l_Lean_instToExprString___closed__3, &l_Lean_instToExprString___closed__3_once, _init_l_Lean_instToExprString___closed__3);
v___x_697_ = ((lean_object*)(l_Lean_instToExprString___closed__0));
v___x_698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v___x_696_);
return v___x_698_;
}
}
static lean_object* _init_l_Lean_instToExprString(void){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = lean_obj_once(&l_Lean_instToExprString___closed__4, &l_Lean_instToExprString___closed__4_once, _init_l_Lean_instToExprString___closed__4);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_instToExprUnit___lam__0___closed__3(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = lean_box(0);
v___x_706_ = ((lean_object*)(l_Lean_instToExprUnit___lam__0___closed__2));
v___x_707_ = l_Lean_mkConst(v___x_706_, v___x_705_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUnit___lam__0(lean_object* v_x_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = lean_obj_once(&l_Lean_instToExprUnit___lam__0___closed__3, &l_Lean_instToExprUnit___lam__0___closed__3_once, _init_l_Lean_instToExprUnit___lam__0___closed__3);
return v___x_709_;
}
}
static lean_object* _init_l_Lean_instToExprUnit___closed__2(void){
_start:
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; 
v___x_713_ = lean_box(0);
v___x_714_ = ((lean_object*)(l_Lean_instToExprUnit___closed__1));
v___x_715_ = l_Lean_mkConst(v___x_714_, v___x_713_);
return v___x_715_;
}
}
static lean_object* _init_l_Lean_instToExprUnit___closed__3(void){
_start:
{
lean_object* v___x_716_; lean_object* v___f_717_; lean_object* v___x_718_; 
v___x_716_ = lean_obj_once(&l_Lean_instToExprUnit___closed__2, &l_Lean_instToExprUnit___closed__2_once, _init_l_Lean_instToExprUnit___closed__2);
v___f_717_ = ((lean_object*)(l_Lean_instToExprUnit___closed__0));
v___x_718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_718_, 0, v___f_717_);
lean_ctor_set(v___x_718_, 1, v___x_716_);
return v___x_718_;
}
}
static lean_object* _init_l_Lean_instToExprUnit(void){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = lean_obj_once(&l_Lean_instToExprUnit___closed__3, &l_Lean_instToExprUnit___closed__3_once, _init_l_Lean_instToExprUnit___closed__3);
return v___x_719_;
}
}
static lean_object* _init_l_Lean_instToExprFilePath___lam__0___closed__4(void){
_start:
{
lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; 
v___x_727_ = lean_box(0);
v___x_728_ = ((lean_object*)(l_Lean_instToExprFilePath___lam__0___closed__3));
v___x_729_ = l_Lean_mkConst(v___x_728_, v___x_727_);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprFilePath___lam__0(lean_object* v_p_730_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_731_ = lean_obj_once(&l_Lean_instToExprFilePath___lam__0___closed__4, &l_Lean_instToExprFilePath___lam__0___closed__4_once, _init_l_Lean_instToExprFilePath___lam__0___closed__4);
v___x_732_ = l_Lean_mkStrLit(v_p_730_);
v___x_733_ = l_Lean_Expr_app___override(v___x_731_, v___x_732_);
return v___x_733_;
}
}
static lean_object* _init_l_Lean_instToExprFilePath___closed__2(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_box(0);
v___x_739_ = ((lean_object*)(l_Lean_instToExprFilePath___closed__1));
v___x_740_ = l_Lean_mkConst(v___x_739_, v___x_738_);
return v___x_740_;
}
}
static lean_object* _init_l_Lean_instToExprFilePath___closed__3(void){
_start:
{
lean_object* v___x_741_; lean_object* v___f_742_; lean_object* v___x_743_; 
v___x_741_ = lean_obj_once(&l_Lean_instToExprFilePath___closed__2, &l_Lean_instToExprFilePath___closed__2_once, _init_l_Lean_instToExprFilePath___closed__2);
v___f_742_ = ((lean_object*)(l_Lean_instToExprFilePath___closed__0));
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v___f_742_);
lean_ctor_set(v___x_743_, 1, v___x_741_);
return v___x_743_;
}
}
static lean_object* _init_l_Lean_instToExprFilePath(void){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = lean_obj_once(&l_Lean_instToExprFilePath___closed__3, &l_Lean_instToExprFilePath___closed__3_once, _init_l_Lean_instToExprFilePath___closed__3);
return v___x_744_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(lean_object* v_n_745_, lean_object* v_sz_746_){
_start:
{
switch(lean_obj_tag(v_n_745_))
{
case 0:
{
lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_747_ = lean_unsigned_to_nat(0u);
v___x_748_ = lean_nat_dec_lt(v___x_747_, v_sz_746_);
if (v___x_748_ == 0)
{
lean_dec(v_sz_746_);
return v___x_748_;
}
else
{
lean_object* v___x_749_; uint8_t v___x_750_; 
v___x_749_ = lean_unsigned_to_nat(8u);
v___x_750_ = lean_nat_dec_le(v_sz_746_, v___x_749_);
lean_dec(v_sz_746_);
return v___x_750_;
}
}
case 1:
{
lean_object* v_pre_751_; lean_object* v___x_752_; lean_object* v___x_753_; 
v_pre_751_ = lean_ctor_get(v_n_745_, 0);
v___x_752_ = lean_unsigned_to_nat(1u);
v___x_753_ = lean_nat_add(v_sz_746_, v___x_752_);
lean_dec(v_sz_746_);
v_n_745_ = v_pre_751_;
v_sz_746_ = v___x_753_;
goto _start;
}
default: 
{
uint8_t v___x_755_; 
lean_dec(v_sz_746_);
v___x_755_ = 0;
return v___x_755_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple___boxed(lean_object* v_n_756_, lean_object* v_sz_757_){
_start:
{
uint8_t v_res_758_; lean_object* v_r_759_; 
v_res_758_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(v_n_756_, v_sz_757_);
lean_dec(v_n_756_);
v_r_759_ = lean_box(v_res_758_);
return v_r_759_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr_spec__0(lean_object* v_msg_760_){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = l_Lean_instInhabitedExpr;
v___x_762_ = lean_panic_fn(v___x_761_, v_msg_760_);
return v___x_762_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7(void){
_start:
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_772_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__6));
v___x_773_ = lean_unsigned_to_nat(11u);
v___x_774_ = lean_unsigned_to_nat(221u);
v___x_775_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__5));
v___x_776_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__4));
v___x_777_ = l_mkPanicMessageWithDecl(v___x_776_, v___x_775_, v___x_774_, v___x_773_, v___x_772_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr(lean_object* v_n_778_, lean_object* v_sz_779_, lean_object* v_args_780_){
_start:
{
switch(lean_obj_tag(v_n_778_))
{
case 0:
{
lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_781_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2));
v___x_782_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__3));
v___x_783_ = l_Nat_reprFast(v_sz_779_);
v___x_784_ = lean_string_append(v___x_782_, v___x_783_);
lean_dec_ref(v___x_783_);
v___x_785_ = l_Lean_Name_str___override(v___x_781_, v___x_784_);
v___x_786_ = lean_box(0);
v___x_787_ = l_Lean_mkConst(v___x_785_, v___x_786_);
v___x_788_ = l_Array_reverse___redArg(v_args_780_);
v___x_789_ = l_Lean_mkAppN(v___x_787_, v___x_788_);
lean_dec_ref(v___x_788_);
return v___x_789_;
}
case 1:
{
lean_object* v_pre_790_; lean_object* v_str_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v_pre_790_ = lean_ctor_get(v_n_778_, 0);
lean_inc(v_pre_790_);
v_str_791_ = lean_ctor_get(v_n_778_, 1);
lean_inc_ref(v_str_791_);
lean_dec_ref(v_n_778_);
v___x_792_ = lean_unsigned_to_nat(1u);
v___x_793_ = lean_nat_add(v_sz_779_, v___x_792_);
lean_dec(v_sz_779_);
v___x_794_ = l_Lean_mkStrLit(v_str_791_);
v___x_795_ = lean_array_push(v_args_780_, v___x_794_);
v_n_778_ = v_pre_790_;
v_sz_779_ = v___x_793_;
v_args_780_ = v___x_795_;
goto _start;
}
default: 
{
lean_object* v___x_797_; lean_object* v___x_798_; 
lean_dec_ref(v_args_780_);
lean_dec(v_sz_779_);
lean_dec(v_n_778_);
v___x_797_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7, &l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7_once, _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7);
v___x_798_ = l_panic___at___00__private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr_spec__0(v___x_797_);
return v___x_798_;
}
}
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2(void){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_804_ = lean_box(0);
v___x_805_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1));
v___x_806_ = l_Lean_mkConst(v___x_805_, v___x_804_);
return v___x_806_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5(void){
_start:
{
lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_812_ = lean_box(0);
v___x_813_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4));
v___x_814_ = l_Lean_mkConst(v___x_813_, v___x_812_);
return v___x_814_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = lean_box(0);
v___x_821_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7));
v___x_822_ = l_Lean_mkConst(v___x_821_, v___x_820_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(lean_object* v_a_823_){
_start:
{
switch(lean_obj_tag(v_a_823_))
{
case 0:
{
lean_object* v___x_824_; 
v___x_824_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2, &l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2_once, _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2);
return v___x_824_;
}
case 1:
{
lean_object* v_pre_825_; lean_object* v_str_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v_pre_825_ = lean_ctor_get(v_a_823_, 0);
lean_inc(v_pre_825_);
v_str_826_ = lean_ctor_get(v_a_823_, 1);
lean_inc_ref(v_str_826_);
lean_dec_ref(v_a_823_);
v___x_827_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5, &l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5_once, _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5);
v___x_828_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(v_pre_825_);
v___x_829_ = l_Lean_mkStrLit(v_str_826_);
v___x_830_ = l_Lean_mkAppB(v___x_827_, v___x_828_, v___x_829_);
return v___x_830_;
}
default: 
{
lean_object* v_pre_831_; lean_object* v_i_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v_pre_831_ = lean_ctor_get(v_a_823_, 0);
lean_inc(v_pre_831_);
v_i_832_ = lean_ctor_get(v_a_823_, 1);
lean_inc(v_i_832_);
lean_dec_ref(v_a_823_);
v___x_833_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8, &l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8_once, _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8);
v___x_834_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(v_pre_831_);
v___x_835_ = l_Lean_mkNatLit(v_i_832_);
v___x_836_ = l_Lean_mkAppB(v___x_833_, v___x_834_, v___x_835_);
return v___x_836_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object* v_n_839_){
_start:
{
lean_object* v___x_840_; uint8_t v___x_841_; 
v___x_840_ = lean_unsigned_to_nat(0u);
v___x_841_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(v_n_839_, v___x_840_);
if (v___x_841_ == 0)
{
lean_object* v___x_842_; 
v___x_842_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(v_n_839_);
return v___x_842_;
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_843_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__0));
v___x_844_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr(v_n_839_, v___x_840_, v___x_843_);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprName___private__1(lean_object* v_n_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_n_845_);
return v___x_846_;
}
}
static lean_object* _init_l_Lean_instToExprName___closed__1(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_848_ = lean_box(0);
v___x_849_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2));
v___x_850_ = l_Lean_mkConst(v___x_849_, v___x_848_);
return v___x_850_;
}
}
static lean_object* _init_l_Lean_instToExprName___closed__2(void){
_start:
{
lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_851_ = lean_obj_once(&l_Lean_instToExprName___closed__1, &l_Lean_instToExprName___closed__1_once, _init_l_Lean_instToExprName___closed__1);
v___x_852_ = ((lean_object*)(l_Lean_instToExprName___closed__0));
v___x_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_852_);
lean_ctor_set(v___x_853_, 1, v___x_851_);
return v___x_853_;
}
}
static lean_object* _init_l_Lean_instToExprName(void){
_start:
{
lean_object* v___x_854_; 
v___x_854_ = lean_obj_once(&l_Lean_instToExprName___closed__2, &l_Lean_instToExprName___closed__2_once, _init_l_Lean_instToExprName___closed__2);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprOptionOfToLevel___redArg___lam__0(lean_object* v_inst_864_, lean_object* v_toTypeExpr_865_, lean_object* v_toExpr_866_, lean_object* v_o_867_){
_start:
{
if (lean_obj_tag(v_o_867_) == 0)
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
lean_dec_ref(v_toExpr_866_);
v___x_868_ = ((lean_object*)(l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__2));
v___x_869_ = lean_box(0);
v___x_870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_870_, 0, v_inst_864_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
v___x_871_ = l_Lean_mkConst(v___x_868_, v___x_870_);
v___x_872_ = l_Lean_Expr_app___override(v___x_871_, v_toTypeExpr_865_);
return v___x_872_;
}
else
{
lean_object* v_val_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v_val_873_ = lean_ctor_get(v_o_867_, 0);
lean_inc(v_val_873_);
lean_dec_ref(v_o_867_);
v___x_874_ = ((lean_object*)(l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__4));
v___x_875_ = lean_box(0);
v___x_876_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_876_, 0, v_inst_864_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = l_Lean_mkConst(v___x_874_, v___x_876_);
v___x_878_ = lean_apply_1(v_toExpr_866_, v_val_873_);
v___x_879_ = l_Lean_mkAppB(v___x_877_, v_toTypeExpr_865_, v___x_878_);
return v___x_879_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprOptionOfToLevel___redArg(lean_object* v_inst_882_, lean_object* v_inst_883_){
_start:
{
lean_object* v_toExpr_884_; lean_object* v_toTypeExpr_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_898_; 
v_toExpr_884_ = lean_ctor_get(v_inst_883_, 0);
v_toTypeExpr_885_ = lean_ctor_get(v_inst_883_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v_inst_883_);
if (v_isSharedCheck_898_ == 0)
{
v___x_887_ = v_inst_883_;
v_isShared_888_ = v_isSharedCheck_898_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_toTypeExpr_885_);
lean_inc(v_toExpr_884_);
lean_dec(v_inst_883_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_898_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___f_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_896_; 
lean_inc_ref(v_toTypeExpr_885_);
lean_inc(v_inst_882_);
v___f_889_ = lean_alloc_closure((void*)(l_Lean_instToExprOptionOfToLevel___redArg___lam__0), 4, 3);
lean_closure_set(v___f_889_, 0, v_inst_882_);
lean_closure_set(v___f_889_, 1, v_toTypeExpr_885_);
lean_closure_set(v___f_889_, 2, v_toExpr_884_);
v___x_890_ = ((lean_object*)(l_Lean_instToExprOptionOfToLevel___redArg___closed__0));
v___x_891_ = lean_box(0);
v___x_892_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_892_, 0, v_inst_882_);
lean_ctor_set(v___x_892_, 1, v___x_891_);
v___x_893_ = l_Lean_mkConst(v___x_890_, v___x_892_);
v___x_894_ = l_Lean_Expr_app___override(v___x_893_, v_toTypeExpr_885_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 1, v___x_894_);
lean_ctor_set(v___x_887_, 0, v___f_889_);
v___x_896_ = v___x_887_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___f_889_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v___x_894_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprOptionOfToLevel(lean_object* v_00_u03b1_899_, lean_object* v_inst_900_, lean_object* v_inst_901_){
_start:
{
lean_object* v___x_902_; 
v___x_902_ = l_Lean_instToExprOptionOfToLevel___redArg(v_inst_900_, v_inst_901_);
return v___x_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(lean_object* v_inst_903_, lean_object* v_nilFn_904_, lean_object* v_consFn_905_, lean_object* v_x_906_){
_start:
{
if (lean_obj_tag(v_x_906_) == 0)
{
lean_dec_ref(v_consFn_905_);
lean_dec_ref(v_inst_903_);
lean_inc_ref(v_nilFn_904_);
return v_nilFn_904_;
}
else
{
lean_object* v_head_907_; lean_object* v_tail_908_; lean_object* v_toExpr_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
v_head_907_ = lean_ctor_get(v_x_906_, 0);
lean_inc(v_head_907_);
v_tail_908_ = lean_ctor_get(v_x_906_, 1);
lean_inc(v_tail_908_);
lean_dec_ref(v_x_906_);
v_toExpr_909_ = lean_ctor_get(v_inst_903_, 0);
lean_inc_ref(v_toExpr_909_);
v___x_910_ = lean_apply_1(v_toExpr_909_, v_head_907_);
lean_inc_ref(v_consFn_905_);
v___x_911_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(v_inst_903_, v_nilFn_904_, v_consFn_905_, v_tail_908_);
v___x_912_ = l_Lean_mkAppB(v_consFn_905_, v___x_910_, v___x_911_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg___boxed(lean_object* v_inst_913_, lean_object* v_nilFn_914_, lean_object* v_consFn_915_, lean_object* v_x_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(v_inst_913_, v_nilFn_914_, v_consFn_915_, v_x_916_);
lean_dec_ref(v_nilFn_914_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_object* v_00_u03b1_918_, lean_object* v_inst_919_, lean_object* v_nilFn_920_, lean_object* v_consFn_921_, lean_object* v_x_922_){
_start:
{
lean_object* v___x_923_; 
v___x_923_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(v_inst_919_, v_nilFn_920_, v_consFn_921_, v_x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___boxed(lean_object* v_00_u03b1_924_, lean_object* v_inst_925_, lean_object* v_nilFn_926_, lean_object* v_consFn_927_, lean_object* v_x_928_){
_start:
{
lean_object* v_res_929_; 
v_res_929_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(v_00_u03b1_924_, v_inst_925_, v_nilFn_926_, v_consFn_927_, v_x_928_);
lean_dec_ref(v_nilFn_926_);
return v_res_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___private__1___redArg(lean_object* v_inst_930_, lean_object* v_nil_931_, lean_object* v_cons_932_, lean_object* v_a_933_){
_start:
{
lean_object* v___x_934_; 
v___x_934_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(v_inst_930_, v_nil_931_, v_cons_932_, v_a_933_);
return v___x_934_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___private__1___redArg___boxed(lean_object* v_inst_935_, lean_object* v_nil_936_, lean_object* v_cons_937_, lean_object* v_a_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_instToExprListOfToLevel___private__1___redArg(v_inst_935_, v_nil_936_, v_cons_937_, v_a_938_);
lean_dec_ref(v_nil_936_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___private__1(lean_object* v_00_u03b1_940_, lean_object* v_inst_941_, lean_object* v_nil_942_, lean_object* v_cons_943_, lean_object* v_a_944_){
_start:
{
lean_object* v___x_945_; 
v___x_945_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(v_inst_941_, v_nil_942_, v_cons_943_, v_a_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___private__1___boxed(lean_object* v_00_u03b1_946_, lean_object* v_inst_947_, lean_object* v_nil_948_, lean_object* v_cons_949_, lean_object* v_a_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_instToExprListOfToLevel___private__1(v_00_u03b1_946_, v_inst_947_, v_nil_948_, v_cons_949_, v_a_950_);
lean_dec_ref(v_nil_948_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___redArg(lean_object* v_inst_963_, lean_object* v_inst_964_){
_start:
{
lean_object* v_toTypeExpr_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v_nil_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v_cons_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; 
v_toTypeExpr_965_ = lean_ctor_get(v_inst_964_, 1);
lean_inc_ref(v_toTypeExpr_965_);
v___x_966_ = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__2));
v___x_967_ = lean_box(0);
v___x_968_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_968_, 0, v_inst_963_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
lean_inc_ref(v___x_968_);
v___x_969_ = l_Lean_mkConst(v___x_966_, v___x_968_);
lean_inc_ref(v_toTypeExpr_965_);
v_nil_970_ = l_Lean_Expr_app___override(v___x_969_, v_toTypeExpr_965_);
v___x_971_ = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__4));
lean_inc_ref(v___x_968_);
v___x_972_ = l_Lean_mkConst(v___x_971_, v___x_968_);
lean_inc_ref(v_toTypeExpr_965_);
v_cons_973_ = l_Lean_Expr_app___override(v___x_972_, v_toTypeExpr_965_);
v___x_974_ = lean_alloc_closure((void*)(l_Lean_instToExprListOfToLevel___private__1___boxed), 5, 4);
lean_closure_set(v___x_974_, 0, lean_box(0));
lean_closure_set(v___x_974_, 1, v_inst_964_);
lean_closure_set(v___x_974_, 2, v_nil_970_);
lean_closure_set(v___x_974_, 3, v_cons_973_);
v___x_975_ = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__5));
v___x_976_ = l_Lean_mkConst(v___x_975_, v___x_968_);
v___x_977_ = l_Lean_Expr_app___override(v___x_976_, v_toTypeExpr_965_);
v___x_978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_978_, 0, v___x_974_);
lean_ctor_set(v___x_978_, 1, v___x_977_);
return v___x_978_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel(lean_object* v_00_u03b1_979_, lean_object* v_inst_980_, lean_object* v_inst_981_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_instToExprListOfToLevel___redArg(v_inst_980_, v_inst_981_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprArrayOfToLevel___redArg___lam__0(lean_object* v_inst_987_, lean_object* v_toTypeExpr_988_, lean_object* v_inst_989_, lean_object* v_as_990_){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v_nil_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v_cons_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; 
v___x_991_ = ((lean_object*)(l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__1));
v___x_992_ = lean_box(0);
v___x_993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_993_, 0, v_inst_987_);
lean_ctor_set(v___x_993_, 1, v___x_992_);
lean_inc_ref(v___x_993_);
v___x_994_ = l_Lean_mkConst(v___x_991_, v___x_993_);
v___x_995_ = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__2));
lean_inc_ref(v___x_993_);
v___x_996_ = l_Lean_mkConst(v___x_995_, v___x_993_);
lean_inc_ref(v_toTypeExpr_988_);
v_nil_997_ = l_Lean_Expr_app___override(v___x_996_, v_toTypeExpr_988_);
v___x_998_ = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__4));
v___x_999_ = l_Lean_mkConst(v___x_998_, v___x_993_);
lean_inc_ref(v_toTypeExpr_988_);
v_cons_1000_ = l_Lean_Expr_app___override(v___x_999_, v_toTypeExpr_988_);
v___x_1001_ = lean_array_to_list(v_as_990_);
v___x_1002_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(v_inst_989_, v_nil_997_, v_cons_1000_, v___x_1001_);
lean_dec_ref(v_nil_997_);
v___x_1003_ = l_Lean_mkAppB(v___x_994_, v_toTypeExpr_988_, v___x_1002_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprArrayOfToLevel___redArg(lean_object* v_inst_1007_, lean_object* v_inst_1008_){
_start:
{
lean_object* v_toTypeExpr_1009_; lean_object* v___f_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v_toTypeExpr_1009_ = lean_ctor_get(v_inst_1008_, 1);
lean_inc_ref(v_toTypeExpr_1009_);
lean_inc_ref(v_toTypeExpr_1009_);
lean_inc(v_inst_1007_);
v___f_1010_ = lean_alloc_closure((void*)(l_Lean_instToExprArrayOfToLevel___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1010_, 0, v_inst_1007_);
lean_closure_set(v___f_1010_, 1, v_toTypeExpr_1009_);
lean_closure_set(v___f_1010_, 2, v_inst_1008_);
v___x_1011_ = ((lean_object*)(l_Lean_instToExprArrayOfToLevel___redArg___closed__1));
v___x_1012_ = lean_box(0);
v___x_1013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1013_, 0, v_inst_1007_);
lean_ctor_set(v___x_1013_, 1, v___x_1012_);
v___x_1014_ = l_Lean_mkConst(v___x_1011_, v___x_1013_);
v___x_1015_ = l_Lean_Expr_app___override(v___x_1014_, v_toTypeExpr_1009_);
v___x_1016_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___f_1010_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprArrayOfToLevel(lean_object* v_00_u03b1_1017_, lean_object* v_inst_1018_, lean_object* v_inst_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l_Lean_instToExprArrayOfToLevel___redArg(v_inst_1018_, v_inst_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprProdOfToLevel___redArg___lam__0(lean_object* v_inst_1025_, lean_object* v_inst_1026_, lean_object* v_toExpr_1027_, lean_object* v_toExpr_1028_, lean_object* v_toTypeExpr_1029_, lean_object* v_toTypeExpr_1030_, lean_object* v_x_1031_){
_start:
{
lean_object* v_fst_1032_; lean_object* v_snd_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1047_; 
v_fst_1032_ = lean_ctor_get(v_x_1031_, 0);
v_snd_1033_ = lean_ctor_get(v_x_1031_, 1);
v_isSharedCheck_1047_ = !lean_is_exclusive(v_x_1031_);
if (v_isSharedCheck_1047_ == 0)
{
v___x_1035_ = v_x_1031_;
v_isShared_1036_ = v_isSharedCheck_1047_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_snd_1033_);
lean_inc(v_fst_1032_);
lean_dec(v_x_1031_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1047_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1040_; 
v___x_1037_ = ((lean_object*)(l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__1));
v___x_1038_ = lean_box(0);
if (v_isShared_1036_ == 0)
{
lean_ctor_set_tag(v___x_1035_, 1);
lean_ctor_set(v___x_1035_, 1, v___x_1038_);
lean_ctor_set(v___x_1035_, 0, v_inst_1025_);
v___x_1040_ = v___x_1035_;
goto v_reusejp_1039_;
}
else
{
lean_object* v_reuseFailAlloc_1046_; 
v_reuseFailAlloc_1046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_inst_1025_);
lean_ctor_set(v_reuseFailAlloc_1046_, 1, v___x_1038_);
v___x_1040_ = v_reuseFailAlloc_1046_;
goto v_reusejp_1039_;
}
v_reusejp_1039_:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1041_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1041_, 0, v_inst_1026_);
lean_ctor_set(v___x_1041_, 1, v___x_1040_);
v___x_1042_ = l_Lean_mkConst(v___x_1037_, v___x_1041_);
v___x_1043_ = lean_apply_1(v_toExpr_1027_, v_fst_1032_);
v___x_1044_ = lean_apply_1(v_toExpr_1028_, v_snd_1033_);
v___x_1045_ = l_Lean_mkApp4(v___x_1042_, v_toTypeExpr_1029_, v_toTypeExpr_1030_, v___x_1043_, v___x_1044_);
return v___x_1045_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprProdOfToLevel___redArg(lean_object* v_inst_1050_, lean_object* v_inst_1051_, lean_object* v_inst_1052_, lean_object* v_inst_1053_){
_start:
{
lean_object* v_toExpr_1054_; lean_object* v_toTypeExpr_1055_; lean_object* v___x_1057_; uint8_t v_isShared_1058_; uint8_t v_isSharedCheck_1077_; 
v_toExpr_1054_ = lean_ctor_get(v_inst_1052_, 0);
v_toTypeExpr_1055_ = lean_ctor_get(v_inst_1052_, 1);
v_isSharedCheck_1077_ = !lean_is_exclusive(v_inst_1052_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1057_ = v_inst_1052_;
v_isShared_1058_ = v_isSharedCheck_1077_;
goto v_resetjp_1056_;
}
else
{
lean_inc(v_toTypeExpr_1055_);
lean_inc(v_toExpr_1054_);
lean_dec(v_inst_1052_);
v___x_1057_ = lean_box(0);
v_isShared_1058_ = v_isSharedCheck_1077_;
goto v_resetjp_1056_;
}
v_resetjp_1056_:
{
lean_object* v_toExpr_1059_; lean_object* v_toTypeExpr_1060_; lean_object* v___x_1062_; uint8_t v_isShared_1063_; uint8_t v_isSharedCheck_1076_; 
v_toExpr_1059_ = lean_ctor_get(v_inst_1053_, 0);
v_toTypeExpr_1060_ = lean_ctor_get(v_inst_1053_, 1);
v_isSharedCheck_1076_ = !lean_is_exclusive(v_inst_1053_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1062_ = v_inst_1053_;
v_isShared_1063_ = v_isSharedCheck_1076_;
goto v_resetjp_1061_;
}
else
{
lean_inc(v_toTypeExpr_1060_);
lean_inc(v_toExpr_1059_);
lean_dec(v_inst_1053_);
v___x_1062_ = lean_box(0);
v_isShared_1063_ = v_isSharedCheck_1076_;
goto v_resetjp_1061_;
}
v_resetjp_1061_:
{
lean_object* v___f_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1068_; 
lean_inc_ref(v_toTypeExpr_1060_);
lean_inc_ref(v_toTypeExpr_1055_);
lean_inc(v_inst_1050_);
lean_inc(v_inst_1051_);
v___f_1064_ = lean_alloc_closure((void*)(l_Lean_instToExprProdOfToLevel___redArg___lam__0), 7, 6);
lean_closure_set(v___f_1064_, 0, v_inst_1051_);
lean_closure_set(v___f_1064_, 1, v_inst_1050_);
lean_closure_set(v___f_1064_, 2, v_toExpr_1054_);
lean_closure_set(v___f_1064_, 3, v_toExpr_1059_);
lean_closure_set(v___f_1064_, 4, v_toTypeExpr_1055_);
lean_closure_set(v___f_1064_, 5, v_toTypeExpr_1060_);
v___x_1065_ = ((lean_object*)(l_Lean_instToExprProdOfToLevel___redArg___closed__0));
v___x_1066_ = lean_box(0);
if (v_isShared_1058_ == 0)
{
lean_ctor_set_tag(v___x_1057_, 1);
lean_ctor_set(v___x_1057_, 1, v___x_1066_);
lean_ctor_set(v___x_1057_, 0, v_inst_1051_);
v___x_1068_ = v___x_1057_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_inst_1051_);
lean_ctor_set(v_reuseFailAlloc_1075_, 1, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1073_; 
v___x_1069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1069_, 0, v_inst_1050_);
lean_ctor_set(v___x_1069_, 1, v___x_1068_);
v___x_1070_ = l_Lean_mkConst(v___x_1065_, v___x_1069_);
v___x_1071_ = l_Lean_mkAppB(v___x_1070_, v_toTypeExpr_1055_, v_toTypeExpr_1060_);
if (v_isShared_1063_ == 0)
{
lean_ctor_set(v___x_1062_, 1, v___x_1071_);
lean_ctor_set(v___x_1062_, 0, v___f_1064_);
v___x_1073_ = v___x_1062_;
goto v_reusejp_1072_;
}
else
{
lean_object* v_reuseFailAlloc_1074_; 
v_reuseFailAlloc_1074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1074_, 0, v___f_1064_);
lean_ctor_set(v_reuseFailAlloc_1074_, 1, v___x_1071_);
v___x_1073_ = v_reuseFailAlloc_1074_;
goto v_reusejp_1072_;
}
v_reusejp_1072_:
{
return v___x_1073_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprProdOfToLevel(lean_object* v_00_u03b1_1078_, lean_object* v_00_u03b2_1079_, lean_object* v_inst_1080_, lean_object* v_inst_1081_, lean_object* v_inst_1082_, lean_object* v_inst_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_instToExprProdOfToLevel___redArg(v_inst_1080_, v_inst_1081_, v_inst_1082_, v_inst_1083_);
return v___x_1084_;
}
}
static lean_object* _init_l_Lean_instToExprLiteral___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = lean_box(0);
v___x_1092_ = ((lean_object*)(l_Lean_instToExprLiteral___lam__0___closed__2));
v___x_1093_ = l_Lean_mkConst(v___x_1092_, v___x_1091_);
return v___x_1093_;
}
}
static lean_object* _init_l_Lean_instToExprLiteral___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1099_ = lean_box(0);
v___x_1100_ = ((lean_object*)(l_Lean_instToExprLiteral___lam__0___closed__5));
v___x_1101_ = l_Lean_mkConst(v___x_1100_, v___x_1099_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprLiteral___lam__0(lean_object* v_l_1102_){
_start:
{
if (lean_obj_tag(v_l_1102_) == 0)
{
lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; 
v___x_1103_ = lean_obj_once(&l_Lean_instToExprLiteral___lam__0___closed__3, &l_Lean_instToExprLiteral___lam__0___closed__3_once, _init_l_Lean_instToExprLiteral___lam__0___closed__3);
v___x_1104_ = l_Lean_Expr_lit___override(v_l_1102_);
v___x_1105_ = l_Lean_Expr_app___override(v___x_1103_, v___x_1104_);
return v___x_1105_;
}
else
{
lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1106_ = lean_obj_once(&l_Lean_instToExprLiteral___lam__0___closed__6, &l_Lean_instToExprLiteral___lam__0___closed__6_once, _init_l_Lean_instToExprLiteral___lam__0___closed__6);
v___x_1107_ = l_Lean_Expr_lit___override(v_l_1102_);
v___x_1108_ = l_Lean_Expr_app___override(v___x_1106_, v___x_1107_);
return v___x_1108_;
}
}
}
static lean_object* _init_l_Lean_instToExprLiteral___closed__2(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v___x_1113_ = lean_box(0);
v___x_1114_ = ((lean_object*)(l_Lean_instToExprLiteral___closed__1));
v___x_1115_ = l_Lean_mkConst(v___x_1114_, v___x_1113_);
return v___x_1115_;
}
}
static lean_object* _init_l_Lean_instToExprLiteral___closed__3(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___f_1117_; lean_object* v___x_1118_; 
v___x_1116_ = lean_obj_once(&l_Lean_instToExprLiteral___closed__2, &l_Lean_instToExprLiteral___closed__2_once, _init_l_Lean_instToExprLiteral___closed__2);
v___f_1117_ = ((lean_object*)(l_Lean_instToExprLiteral___closed__0));
v___x_1118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1118_, 0, v___f_1117_);
lean_ctor_set(v___x_1118_, 1, v___x_1116_);
return v___x_1118_;
}
}
static lean_object* _init_l_Lean_instToExprLiteral(void){
_start:
{
lean_object* v___x_1119_; 
v___x_1119_ = lean_obj_once(&l_Lean_instToExprLiteral___closed__3, &l_Lean_instToExprLiteral___closed__3_once, _init_l_Lean_instToExprLiteral___closed__3);
return v___x_1119_;
}
}
static lean_object* _init_l_Lean_instToExprFVarId___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v___x_1125_ = lean_box(0);
v___x_1126_ = ((lean_object*)(l_Lean_instToExprFVarId___lam__0___closed__1));
v___x_1127_ = l_Lean_mkConst(v___x_1126_, v___x_1125_);
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprFVarId___lam__0(lean_object* v_fvarId_1128_){
_start:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1129_ = lean_obj_once(&l_Lean_instToExprFVarId___lam__0___closed__2, &l_Lean_instToExprFVarId___lam__0___closed__2_once, _init_l_Lean_instToExprFVarId___lam__0___closed__2);
v___x_1130_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_fvarId_1128_);
v___x_1131_ = l_Lean_Expr_app___override(v___x_1129_, v___x_1130_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lean_instToExprFVarId___closed__2(void){
_start:
{
lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1136_ = lean_box(0);
v___x_1137_ = ((lean_object*)(l_Lean_instToExprFVarId___closed__1));
v___x_1138_ = l_Lean_mkConst(v___x_1137_, v___x_1136_);
return v___x_1138_;
}
}
static lean_object* _init_l_Lean_instToExprFVarId___closed__3(void){
_start:
{
lean_object* v___x_1139_; lean_object* v___f_1140_; lean_object* v___x_1141_; 
v___x_1139_ = lean_obj_once(&l_Lean_instToExprFVarId___closed__2, &l_Lean_instToExprFVarId___closed__2_once, _init_l_Lean_instToExprFVarId___closed__2);
v___f_1140_ = ((lean_object*)(l_Lean_instToExprFVarId___closed__0));
v___x_1141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___f_1140_);
lean_ctor_set(v___x_1141_, 1, v___x_1139_);
return v___x_1141_;
}
}
static lean_object* _init_l_Lean_instToExprFVarId(void){
_start:
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_obj_once(&l_Lean_instToExprFVarId___closed__3, &l_Lean_instToExprFVarId___closed__3_once, _init_l_Lean_instToExprFVarId___closed__3);
return v___x_1142_;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = lean_box(0);
v___x_1152_ = ((lean_object*)(l_Lean_instToExprPreresolved___lam__0___closed__3));
v___x_1153_ = l_Lean_Expr_const___override(v___x_1152_, v___x_1151_);
return v___x_1153_;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1160_ = lean_box(0);
v___x_1161_ = ((lean_object*)(l_Lean_instToExprPreresolved___lam__0___closed__6));
v___x_1162_ = l_Lean_Expr_const___override(v___x_1161_, v___x_1160_);
return v___x_1162_;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = ((lean_object*)(l_Lean_instToExprPreresolved___lam__0___closed__8));
v___x_1167_ = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__2));
v___x_1168_ = l_Lean_mkConst(v___x_1167_, v___x_1166_);
return v___x_1168_;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___lam__0___closed__10(void){
_start:
{
lean_object* v_type_1169_; lean_object* v___x_1170_; lean_object* v_nil_1171_; 
v_type_1169_ = lean_obj_once(&l_Lean_instToExprString___closed__3, &l_Lean_instToExprString___closed__3_once, _init_l_Lean_instToExprString___closed__3);
v___x_1170_ = lean_obj_once(&l_Lean_instToExprPreresolved___lam__0___closed__9, &l_Lean_instToExprPreresolved___lam__0___closed__9_once, _init_l_Lean_instToExprPreresolved___lam__0___closed__9);
v_nil_1171_ = l_Lean_Expr_app___override(v___x_1170_, v_type_1169_);
return v_nil_1171_;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___lam__0___closed__11(void){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; 
v___x_1172_ = ((lean_object*)(l_Lean_instToExprPreresolved___lam__0___closed__8));
v___x_1173_ = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__4));
v___x_1174_ = l_Lean_mkConst(v___x_1173_, v___x_1172_);
return v___x_1174_;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___lam__0___closed__12(void){
_start:
{
lean_object* v_type_1175_; lean_object* v___x_1176_; lean_object* v_cons_1177_; 
v_type_1175_ = lean_obj_once(&l_Lean_instToExprString___closed__3, &l_Lean_instToExprString___closed__3_once, _init_l_Lean_instToExprString___closed__3);
v___x_1176_ = lean_obj_once(&l_Lean_instToExprPreresolved___lam__0___closed__11, &l_Lean_instToExprPreresolved___lam__0___closed__11_once, _init_l_Lean_instToExprPreresolved___lam__0___closed__11);
v_cons_1177_ = l_Lean_Expr_app___override(v___x_1176_, v_type_1175_);
return v_cons_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprPreresolved___lam__0(lean_object* v___x_1178_, lean_object* v_x_1179_){
_start:
{
if (lean_obj_tag(v_x_1179_) == 0)
{
lean_object* v_ns_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; 
lean_dec_ref(v___x_1178_);
v_ns_1180_ = lean_ctor_get(v_x_1179_, 0);
lean_inc(v_ns_1180_);
lean_dec_ref(v_x_1179_);
v___x_1181_ = lean_obj_once(&l_Lean_instToExprPreresolved___lam__0___closed__4, &l_Lean_instToExprPreresolved___lam__0___closed__4_once, _init_l_Lean_instToExprPreresolved___lam__0___closed__4);
v___x_1182_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_ns_1180_);
v___x_1183_ = l_Lean_Expr_app___override(v___x_1181_, v___x_1182_);
return v___x_1183_;
}
else
{
lean_object* v_n_1184_; lean_object* v_fields_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v_nil_1188_; lean_object* v_cons_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v_n_1184_ = lean_ctor_get(v_x_1179_, 0);
lean_inc(v_n_1184_);
v_fields_1185_ = lean_ctor_get(v_x_1179_, 1);
lean_inc(v_fields_1185_);
lean_dec_ref(v_x_1179_);
v___x_1186_ = lean_obj_once(&l_Lean_instToExprPreresolved___lam__0___closed__7, &l_Lean_instToExprPreresolved___lam__0___closed__7_once, _init_l_Lean_instToExprPreresolved___lam__0___closed__7);
v___x_1187_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_n_1184_);
v_nil_1188_ = lean_obj_once(&l_Lean_instToExprPreresolved___lam__0___closed__10, &l_Lean_instToExprPreresolved___lam__0___closed__10_once, _init_l_Lean_instToExprPreresolved___lam__0___closed__10);
v_cons_1189_ = lean_obj_once(&l_Lean_instToExprPreresolved___lam__0___closed__12, &l_Lean_instToExprPreresolved___lam__0___closed__12_once, _init_l_Lean_instToExprPreresolved___lam__0___closed__12);
v___x_1190_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(v___x_1178_, v_nil_1188_, v_cons_1189_, v_fields_1185_);
v___x_1191_ = l_Lean_mkAppB(v___x_1186_, v___x_1187_, v___x_1190_);
return v___x_1191_;
}
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___closed__0(void){
_start:
{
lean_object* v___x_1192_; lean_object* v___f_1193_; 
v___x_1192_ = l_Lean_instToExprString;
v___f_1193_ = lean_alloc_closure((void*)(l_Lean_instToExprPreresolved___lam__0), 2, 1);
lean_closure_set(v___f_1193_, 0, v___x_1192_);
return v___f_1193_;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___closed__2(void){
_start:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = lean_box(0);
v___x_1199_ = ((lean_object*)(l_Lean_instToExprPreresolved___closed__1));
v___x_1200_ = l_Lean_Expr_const___override(v___x_1199_, v___x_1198_);
return v___x_1200_;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___closed__3(void){
_start:
{
lean_object* v___x_1201_; lean_object* v___f_1202_; lean_object* v___x_1203_; 
v___x_1201_ = lean_obj_once(&l_Lean_instToExprPreresolved___closed__2, &l_Lean_instToExprPreresolved___closed__2_once, _init_l_Lean_instToExprPreresolved___closed__2);
v___f_1202_ = lean_obj_once(&l_Lean_instToExprPreresolved___closed__0, &l_Lean_instToExprPreresolved___closed__0_once, _init_l_Lean_instToExprPreresolved___closed__0);
v___x_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1203_, 0, v___f_1202_);
lean_ctor_set(v___x_1203_, 1, v___x_1201_);
return v___x_1203_;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved(void){
_start:
{
lean_object* v___x_1204_; 
v___x_1204_ = lean_obj_once(&l_Lean_instToExprPreresolved___closed__3, &l_Lean_instToExprPreresolved___closed__3_once, _init_l_Lean_instToExprPreresolved___closed__3);
return v___x_1204_;
}
}
lean_object* runtime_initialize_Lean_ToLevel(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Rat_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ToExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_ToLevel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Rat_Basic(builtin);
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
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_ToExpr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
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
res = runtime_initialize_Lean_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_ToExpr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_ToExpr(builtin);
}
#ifdef __cplusplus
}
#endif
