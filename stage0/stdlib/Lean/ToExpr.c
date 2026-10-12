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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
lean_object* l_Lean_instToExprUInt8___lam__0(uint8_t v_a_245_){
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
LEAN_EXPORT void l_Lean_instToExprUInt8___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_a_245_ = stack[0].m_num;
lean_object* v_res_253_;
v_res_253_ = l_Lean_instToExprUInt8___lam__0(v_a_245_);
stack->m_obj
 = v_res_253_;
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt8___lam__0___boxed(lean_object* v_a_254_){
_start:
{
uint8_t v_a_boxed_255_; lean_object* v_res_256_; 
v_a_boxed_255_ = lean_unbox(v_a_254_);
v_res_256_ = l_Lean_instToExprUInt8___lam__0(v_a_boxed_255_);
return v_res_256_;
}
}
static lean_object* _init_l_Lean_instToExprUInt8___closed__1(void){
_start:
{
lean_object* v___x_258_; lean_object* v___f_259_; lean_object* v___x_260_; 
v___x_258_ = lean_obj_once(&l_Lean_instToExprUInt8___lam__0___closed__2, &l_Lean_instToExprUInt8___lam__0___closed__2_once, _init_l_Lean_instToExprUInt8___lam__0___closed__2);
v___f_259_ = ((lean_object*)(l_Lean_instToExprUInt8___closed__0));
v___x_260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_260_, 0, v___f_259_);
lean_ctor_set(v___x_260_, 1, v___x_258_);
return v___x_260_;
}
}
static lean_object* _init_l_Lean_instToExprUInt8(void){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = lean_obj_once(&l_Lean_instToExprUInt8___closed__1, &l_Lean_instToExprUInt8___closed__1_once, _init_l_Lean_instToExprUInt8___closed__1);
return v___x_261_;
}
}
static lean_object* _init_l_Lean_instToExprUInt16___lam__0___closed__2(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; 
v___x_265_ = lean_box(0);
v___x_266_ = ((lean_object*)(l_Lean_instToExprUInt16___lam__0___closed__1));
v___x_267_ = l_Lean_mkConst(v___x_266_, v___x_265_);
return v___x_267_;
}
}
static lean_object* _init_l_Lean_instToExprUInt16___lam__0___closed__4(void){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v___x_271_ = lean_box(0);
v___x_272_ = ((lean_object*)(l_Lean_instToExprUInt16___lam__0___closed__3));
v___x_273_ = l_Lean_Expr_const___override(v___x_272_, v___x_271_);
return v___x_273_;
}
}
lean_object* l_Lean_instToExprUInt16___lam__0(uint16_t v_a_274_){
_start:
{
lean_object* v___x_275_; lean_object* v_r_276_; lean_object* v___x_277_; lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_275_ = lean_uint16_to_nat(v_a_274_);
v_r_276_ = l_Lean_mkRawNatLit(v___x_275_);
v___x_277_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_278_ = lean_obj_once(&l_Lean_instToExprUInt16___lam__0___closed__2, &l_Lean_instToExprUInt16___lam__0___closed__2_once, _init_l_Lean_instToExprUInt16___lam__0___closed__2);
v___x_279_ = lean_obj_once(&l_Lean_instToExprUInt16___lam__0___closed__4, &l_Lean_instToExprUInt16___lam__0___closed__4_once, _init_l_Lean_instToExprUInt16___lam__0___closed__4);
lean_inc_ref(v_r_276_);
v___x_280_ = l_Lean_Expr_app___override(v___x_279_, v_r_276_);
v___x_281_ = l_Lean_mkApp3(v___x_277_, v___x_278_, v_r_276_, v___x_280_);
return v___x_281_;
}
}
LEAN_EXPORT void l_Lean_instToExprUInt16___lam__0_0interp(lean_interpreter_value* stack)
{
uint16_t v_a_274_ = stack[0].m_num;
lean_object* v_res_282_;
v_res_282_ = l_Lean_instToExprUInt16___lam__0(v_a_274_);
stack->m_obj
 = v_res_282_;
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt16___lam__0___boxed(lean_object* v_a_283_){
_start:
{
uint16_t v_a_boxed_284_; lean_object* v_res_285_; 
v_a_boxed_284_ = lean_unbox(v_a_283_);
v_res_285_ = l_Lean_instToExprUInt16___lam__0(v_a_boxed_284_);
return v_res_285_;
}
}
static lean_object* _init_l_Lean_instToExprUInt16___closed__1(void){
_start:
{
lean_object* v___x_287_; lean_object* v___f_288_; lean_object* v___x_289_; 
v___x_287_ = lean_obj_once(&l_Lean_instToExprUInt16___lam__0___closed__2, &l_Lean_instToExprUInt16___lam__0___closed__2_once, _init_l_Lean_instToExprUInt16___lam__0___closed__2);
v___f_288_ = ((lean_object*)(l_Lean_instToExprUInt16___closed__0));
v___x_289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_289_, 0, v___f_288_);
lean_ctor_set(v___x_289_, 1, v___x_287_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_instToExprUInt16(void){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = lean_obj_once(&l_Lean_instToExprUInt16___closed__1, &l_Lean_instToExprUInt16___closed__1_once, _init_l_Lean_instToExprUInt16___closed__1);
return v___x_290_;
}
}
static lean_object* _init_l_Lean_instToExprUInt32___lam__0___closed__2(void){
_start:
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v___x_294_ = lean_box(0);
v___x_295_ = ((lean_object*)(l_Lean_instToExprUInt32___lam__0___closed__1));
v___x_296_ = l_Lean_mkConst(v___x_295_, v___x_294_);
return v___x_296_;
}
}
static lean_object* _init_l_Lean_instToExprUInt32___lam__0___closed__4(void){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_300_ = lean_box(0);
v___x_301_ = ((lean_object*)(l_Lean_instToExprUInt32___lam__0___closed__3));
v___x_302_ = l_Lean_Expr_const___override(v___x_301_, v___x_300_);
return v___x_302_;
}
}
lean_object* l_Lean_instToExprUInt32___lam__0(uint32_t v_a_303_){
_start:
{
lean_object* v___x_304_; lean_object* v_r_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; 
v___x_304_ = lean_uint32_to_nat(v_a_303_);
v_r_305_ = l_Lean_mkRawNatLit(v___x_304_);
v___x_306_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_307_ = lean_obj_once(&l_Lean_instToExprUInt32___lam__0___closed__2, &l_Lean_instToExprUInt32___lam__0___closed__2_once, _init_l_Lean_instToExprUInt32___lam__0___closed__2);
v___x_308_ = lean_obj_once(&l_Lean_instToExprUInt32___lam__0___closed__4, &l_Lean_instToExprUInt32___lam__0___closed__4_once, _init_l_Lean_instToExprUInt32___lam__0___closed__4);
lean_inc_ref(v_r_305_);
v___x_309_ = l_Lean_Expr_app___override(v___x_308_, v_r_305_);
v___x_310_ = l_Lean_mkApp3(v___x_306_, v___x_307_, v_r_305_, v___x_309_);
return v___x_310_;
}
}
LEAN_EXPORT void l_Lean_instToExprUInt32___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_303_ = stack[0].m_num;
lean_object* v_res_311_;
v_res_311_ = l_Lean_instToExprUInt32___lam__0(v_a_303_);
stack->m_obj
 = v_res_311_;
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt32___lam__0___boxed(lean_object* v_a_312_){
_start:
{
uint32_t v_a_boxed_313_; lean_object* v_res_314_; 
v_a_boxed_313_ = lean_unbox_uint32(v_a_312_);
lean_dec(v_a_312_);
v_res_314_ = l_Lean_instToExprUInt32___lam__0(v_a_boxed_313_);
return v_res_314_;
}
}
static lean_object* _init_l_Lean_instToExprUInt32___closed__1(void){
_start:
{
lean_object* v___x_316_; lean_object* v___f_317_; lean_object* v___x_318_; 
v___x_316_ = lean_obj_once(&l_Lean_instToExprUInt32___lam__0___closed__2, &l_Lean_instToExprUInt32___lam__0___closed__2_once, _init_l_Lean_instToExprUInt32___lam__0___closed__2);
v___f_317_ = ((lean_object*)(l_Lean_instToExprUInt32___closed__0));
v___x_318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_318_, 0, v___f_317_);
lean_ctor_set(v___x_318_, 1, v___x_316_);
return v___x_318_;
}
}
static lean_object* _init_l_Lean_instToExprUInt32(void){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = lean_obj_once(&l_Lean_instToExprUInt32___closed__1, &l_Lean_instToExprUInt32___closed__1_once, _init_l_Lean_instToExprUInt32___closed__1);
return v___x_319_;
}
}
static lean_object* _init_l_Lean_instToExprUInt64___lam__0___closed__2(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_323_ = lean_box(0);
v___x_324_ = ((lean_object*)(l_Lean_instToExprUInt64___lam__0___closed__1));
v___x_325_ = l_Lean_mkConst(v___x_324_, v___x_323_);
return v___x_325_;
}
}
static lean_object* _init_l_Lean_instToExprUInt64___lam__0___closed__4(void){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; 
v___x_329_ = lean_box(0);
v___x_330_ = ((lean_object*)(l_Lean_instToExprUInt64___lam__0___closed__3));
v___x_331_ = l_Lean_Expr_const___override(v___x_330_, v___x_329_);
return v___x_331_;
}
}
lean_object* l_Lean_instToExprUInt64___lam__0(uint64_t v_a_332_){
_start:
{
lean_object* v___x_333_; lean_object* v_r_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_333_ = lean_uint64_to_nat(v_a_332_);
v_r_334_ = l_Lean_mkRawNatLit(v___x_333_);
v___x_335_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_336_ = lean_obj_once(&l_Lean_instToExprUInt64___lam__0___closed__2, &l_Lean_instToExprUInt64___lam__0___closed__2_once, _init_l_Lean_instToExprUInt64___lam__0___closed__2);
v___x_337_ = lean_obj_once(&l_Lean_instToExprUInt64___lam__0___closed__4, &l_Lean_instToExprUInt64___lam__0___closed__4_once, _init_l_Lean_instToExprUInt64___lam__0___closed__4);
lean_inc_ref(v_r_334_);
v___x_338_ = l_Lean_Expr_app___override(v___x_337_, v_r_334_);
v___x_339_ = l_Lean_mkApp3(v___x_335_, v___x_336_, v_r_334_, v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT void l_Lean_instToExprUInt64___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_a_332_ = stack[0].m_num;
lean_object* v_res_340_;
v_res_340_ = l_Lean_instToExprUInt64___lam__0(v_a_332_);
stack->m_obj
 = v_res_340_;
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt64___lam__0___boxed(lean_object* v_a_341_){
_start:
{
uint64_t v_a_boxed_342_; lean_object* v_res_343_; 
v_a_boxed_342_ = lean_unbox_uint64(v_a_341_);
lean_dec_ref(v_a_341_);
v_res_343_ = l_Lean_instToExprUInt64___lam__0(v_a_boxed_342_);
return v_res_343_;
}
}
static lean_object* _init_l_Lean_instToExprUInt64___closed__1(void){
_start:
{
lean_object* v___x_345_; lean_object* v___f_346_; lean_object* v___x_347_; 
v___x_345_ = lean_obj_once(&l_Lean_instToExprUInt64___lam__0___closed__2, &l_Lean_instToExprUInt64___lam__0___closed__2_once, _init_l_Lean_instToExprUInt64___lam__0___closed__2);
v___f_346_ = ((lean_object*)(l_Lean_instToExprUInt64___closed__0));
v___x_347_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_347_, 0, v___f_346_);
lean_ctor_set(v___x_347_, 1, v___x_345_);
return v___x_347_;
}
}
static lean_object* _init_l_Lean_instToExprUInt64(void){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = lean_obj_once(&l_Lean_instToExprUInt64___closed__1, &l_Lean_instToExprUInt64___closed__1_once, _init_l_Lean_instToExprUInt64___closed__1);
return v___x_348_;
}
}
static lean_object* _init_l_Lean_instToExprUSize___lam__0___closed__2(void){
_start:
{
lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v___x_352_ = lean_box(0);
v___x_353_ = ((lean_object*)(l_Lean_instToExprUSize___lam__0___closed__1));
v___x_354_ = l_Lean_mkConst(v___x_353_, v___x_352_);
return v___x_354_;
}
}
static lean_object* _init_l_Lean_instToExprUSize___lam__0___closed__4(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_358_ = lean_box(0);
v___x_359_ = ((lean_object*)(l_Lean_instToExprUSize___lam__0___closed__3));
v___x_360_ = l_Lean_Expr_const___override(v___x_359_, v___x_358_);
return v___x_360_;
}
}
lean_object* l_Lean_instToExprUSize___lam__0(size_t v_a_361_){
_start:
{
lean_object* v___x_362_; lean_object* v_r_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_362_ = lean_usize_to_nat(v_a_361_);
v_r_363_ = l_Lean_mkRawNatLit(v___x_362_);
v___x_364_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_365_ = lean_obj_once(&l_Lean_instToExprUSize___lam__0___closed__2, &l_Lean_instToExprUSize___lam__0___closed__2_once, _init_l_Lean_instToExprUSize___lam__0___closed__2);
v___x_366_ = lean_obj_once(&l_Lean_instToExprUSize___lam__0___closed__4, &l_Lean_instToExprUSize___lam__0___closed__4_once, _init_l_Lean_instToExprUSize___lam__0___closed__4);
lean_inc_ref(v_r_363_);
v___x_367_ = l_Lean_Expr_app___override(v___x_366_, v_r_363_);
v___x_368_ = l_Lean_mkApp3(v___x_364_, v___x_365_, v_r_363_, v___x_367_);
return v___x_368_;
}
}
LEAN_EXPORT void l_Lean_instToExprUSize___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_a_361_ = stack[0].m_num;
lean_object* v_res_369_;
v_res_369_ = l_Lean_instToExprUSize___lam__0(v_a_361_);
stack->m_obj
 = v_res_369_;
}
LEAN_EXPORT lean_object* l_Lean_instToExprUSize___lam__0___boxed(lean_object* v_a_370_){
_start:
{
size_t v_a_boxed_371_; lean_object* v_res_372_; 
v_a_boxed_371_ = lean_unbox_usize(v_a_370_);
lean_dec(v_a_370_);
v_res_372_ = l_Lean_instToExprUSize___lam__0(v_a_boxed_371_);
return v_res_372_;
}
}
static lean_object* _init_l_Lean_instToExprUSize___closed__1(void){
_start:
{
lean_object* v___x_374_; lean_object* v___f_375_; lean_object* v___x_376_; 
v___x_374_ = lean_obj_once(&l_Lean_instToExprUSize___lam__0___closed__2, &l_Lean_instToExprUSize___lam__0___closed__2_once, _init_l_Lean_instToExprUSize___lam__0___closed__2);
v___f_375_ = ((lean_object*)(l_Lean_instToExprUSize___closed__0));
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v___f_375_);
lean_ctor_set(v___x_376_, 1, v___x_374_);
return v___x_376_;
}
}
static lean_object* _init_l_Lean_instToExprUSize(void){
_start:
{
lean_object* v___x_377_; 
v___x_377_ = lean_obj_once(&l_Lean_instToExprUSize___closed__1, &l_Lean_instToExprUSize___closed__1_once, _init_l_Lean_instToExprUSize___closed__1);
return v___x_377_;
}
}
static lean_object* _init_l_Lean_instToExprInt8_mkNat___closed__2(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_381_ = lean_box(0);
v___x_382_ = ((lean_object*)(l_Lean_instToExprInt8_mkNat___closed__1));
v___x_383_ = l_Lean_Expr_const___override(v___x_382_, v___x_381_);
return v___x_383_;
}
}
static lean_object* _init_l_Lean_instToExprInt8_mkNat___closed__4(void){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; 
v___x_387_ = lean_box(0);
v___x_388_ = ((lean_object*)(l_Lean_instToExprInt8_mkNat___closed__3));
v___x_389_ = l_Lean_Expr_const___override(v___x_388_, v___x_387_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt8_mkNat(lean_object* v_n_390_){
_start:
{
lean_object* v_r_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_r_391_ = l_Lean_mkRawNatLit(v_n_390_);
v___x_392_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_393_ = lean_obj_once(&l_Lean_instToExprInt8_mkNat___closed__2, &l_Lean_instToExprInt8_mkNat___closed__2_once, _init_l_Lean_instToExprInt8_mkNat___closed__2);
v___x_394_ = lean_obj_once(&l_Lean_instToExprInt8_mkNat___closed__4, &l_Lean_instToExprInt8_mkNat___closed__4_once, _init_l_Lean_instToExprInt8_mkNat___closed__4);
lean_inc_ref(v_r_391_);
v___x_395_ = l_Lean_Expr_app___override(v___x_394_, v_r_391_);
v___x_396_ = l_Lean_mkApp3(v___x_392_, v___x_393_, v_r_391_, v___x_395_);
return v___x_396_;
}
}
static uint8_t _init_l_Lean_instToExprInt8___lam__0___closed__0(void){
_start:
{
lean_object* v___x_397_; uint8_t v___x_398_; 
v___x_397_ = lean_unsigned_to_nat(0u);
v___x_398_ = lean_int8_of_nat(v___x_397_);
return v___x_398_;
}
}
static lean_object* _init_l_Lean_instToExprInt8___lam__0___closed__2(void){
_start:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_402_ = lean_box(0);
v___x_403_ = ((lean_object*)(l_Lean_instToExprInt8___lam__0___closed__1));
v___x_404_ = l_Lean_Expr_const___override(v___x_403_, v___x_402_);
return v___x_404_;
}
}
lean_object* l_Lean_instToExprInt8___lam__0(uint8_t v_i_405_){
_start:
{
uint8_t v___x_406_; uint8_t v___x_407_; 
v___x_406_ = lean_uint8_once(&l_Lean_instToExprInt8___lam__0___closed__0, &l_Lean_instToExprInt8___lam__0___closed__0_once, _init_l_Lean_instToExprInt8___lam__0___closed__0);
v___x_407_ = lean_int8_dec_le(v___x_406_, v_i_405_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_408_ = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__4, &l_Lean_instToExprInt___lam__0___closed__4_once, _init_l_Lean_instToExprInt___lam__0___closed__4);
v___x_409_ = lean_obj_once(&l_Lean_instToExprInt8_mkNat___closed__2, &l_Lean_instToExprInt8_mkNat___closed__2_once, _init_l_Lean_instToExprInt8_mkNat___closed__2);
v___x_410_ = lean_obj_once(&l_Lean_instToExprInt8___lam__0___closed__2, &l_Lean_instToExprInt8___lam__0___closed__2_once, _init_l_Lean_instToExprInt8___lam__0___closed__2);
v___x_411_ = lean_int8_to_int(v_i_405_);
v___x_412_ = lean_int_neg(v___x_411_);
v___x_413_ = l_Int_toNat(v___x_412_);
lean_dec(v___x_412_);
v___x_414_ = l_Lean_instToExprInt8_mkNat(v___x_413_);
v___x_415_ = l_Lean_mkApp3(v___x_408_, v___x_409_, v___x_410_, v___x_414_);
return v___x_415_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
v___x_416_ = lean_int8_to_int(v_i_405_);
v___x_417_ = l_Int_toNat(v___x_416_);
v___x_418_ = l_Lean_instToExprInt8_mkNat(v___x_417_);
return v___x_418_;
}
}
}
LEAN_EXPORT void l_Lean_instToExprInt8___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_i_405_ = stack[0].m_num;
lean_object* v_res_419_;
v_res_419_ = l_Lean_instToExprInt8___lam__0(v_i_405_);
stack->m_obj
 = v_res_419_;
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt8___lam__0___boxed(lean_object* v_i_420_){
_start:
{
uint8_t v_i_boxed_421_; lean_object* v_res_422_; 
v_i_boxed_421_ = lean_unbox(v_i_420_);
v_res_422_ = l_Lean_instToExprInt8___lam__0(v_i_boxed_421_);
return v_res_422_;
}
}
static lean_object* _init_l_Lean_instToExprInt8___closed__1(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_box(0);
v___x_425_ = ((lean_object*)(l_Lean_instToExprInt8_mkNat___closed__1));
v___x_426_ = l_Lean_mkConst(v___x_425_, v___x_424_);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_instToExprInt8___closed__2(void){
_start:
{
lean_object* v___x_427_; lean_object* v___f_428_; lean_object* v___x_429_; 
v___x_427_ = lean_obj_once(&l_Lean_instToExprInt8___closed__1, &l_Lean_instToExprInt8___closed__1_once, _init_l_Lean_instToExprInt8___closed__1);
v___f_428_ = ((lean_object*)(l_Lean_instToExprInt8___closed__0));
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v___f_428_);
lean_ctor_set(v___x_429_, 1, v___x_427_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_instToExprInt8(void){
_start:
{
lean_object* v___x_430_; 
v___x_430_ = lean_obj_once(&l_Lean_instToExprInt8___closed__2, &l_Lean_instToExprInt8___closed__2_once, _init_l_Lean_instToExprInt8___closed__2);
return v___x_430_;
}
}
static lean_object* _init_l_Lean_instToExprInt16_mkNat___closed__2(void){
_start:
{
lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_434_ = lean_box(0);
v___x_435_ = ((lean_object*)(l_Lean_instToExprInt16_mkNat___closed__1));
v___x_436_ = l_Lean_Expr_const___override(v___x_435_, v___x_434_);
return v___x_436_;
}
}
static lean_object* _init_l_Lean_instToExprInt16_mkNat___closed__4(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = lean_box(0);
v___x_441_ = ((lean_object*)(l_Lean_instToExprInt16_mkNat___closed__3));
v___x_442_ = l_Lean_Expr_const___override(v___x_441_, v___x_440_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt16_mkNat(lean_object* v_n_443_){
_start:
{
lean_object* v_r_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v_r_444_ = l_Lean_mkRawNatLit(v_n_443_);
v___x_445_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_446_ = lean_obj_once(&l_Lean_instToExprInt16_mkNat___closed__2, &l_Lean_instToExprInt16_mkNat___closed__2_once, _init_l_Lean_instToExprInt16_mkNat___closed__2);
v___x_447_ = lean_obj_once(&l_Lean_instToExprInt16_mkNat___closed__4, &l_Lean_instToExprInt16_mkNat___closed__4_once, _init_l_Lean_instToExprInt16_mkNat___closed__4);
lean_inc_ref(v_r_444_);
v___x_448_ = l_Lean_Expr_app___override(v___x_447_, v_r_444_);
v___x_449_ = l_Lean_mkApp3(v___x_445_, v___x_446_, v_r_444_, v___x_448_);
return v___x_449_;
}
}
static uint16_t _init_l_Lean_instToExprInt16___lam__0___closed__0(void){
_start:
{
lean_object* v___x_450_; uint16_t v___x_451_; 
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = lean_int16_of_nat(v___x_450_);
return v___x_451_;
}
}
static lean_object* _init_l_Lean_instToExprInt16___lam__0___closed__2(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_455_ = lean_box(0);
v___x_456_ = ((lean_object*)(l_Lean_instToExprInt16___lam__0___closed__1));
v___x_457_ = l_Lean_Expr_const___override(v___x_456_, v___x_455_);
return v___x_457_;
}
}
lean_object* l_Lean_instToExprInt16___lam__0(uint16_t v_i_458_){
_start:
{
uint16_t v___x_459_; uint8_t v___x_460_; 
v___x_459_ = lean_uint16_once(&l_Lean_instToExprInt16___lam__0___closed__0, &l_Lean_instToExprInt16___lam__0___closed__0_once, _init_l_Lean_instToExprInt16___lam__0___closed__0);
v___x_460_ = lean_int16_dec_le(v___x_459_, v_i_458_);
if (v___x_460_ == 0)
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_461_ = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__4, &l_Lean_instToExprInt___lam__0___closed__4_once, _init_l_Lean_instToExprInt___lam__0___closed__4);
v___x_462_ = lean_obj_once(&l_Lean_instToExprInt16_mkNat___closed__2, &l_Lean_instToExprInt16_mkNat___closed__2_once, _init_l_Lean_instToExprInt16_mkNat___closed__2);
v___x_463_ = lean_obj_once(&l_Lean_instToExprInt16___lam__0___closed__2, &l_Lean_instToExprInt16___lam__0___closed__2_once, _init_l_Lean_instToExprInt16___lam__0___closed__2);
v___x_464_ = lean_int16_to_int(v_i_458_);
v___x_465_ = lean_int_neg(v___x_464_);
v___x_466_ = l_Int_toNat(v___x_465_);
lean_dec(v___x_465_);
v___x_467_ = l_Lean_instToExprInt16_mkNat(v___x_466_);
v___x_468_ = l_Lean_mkApp3(v___x_461_, v___x_462_, v___x_463_, v___x_467_);
return v___x_468_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_int16_to_int(v_i_458_);
v___x_470_ = l_Int_toNat(v___x_469_);
v___x_471_ = l_Lean_instToExprInt16_mkNat(v___x_470_);
return v___x_471_;
}
}
}
LEAN_EXPORT void l_Lean_instToExprInt16___lam__0_0interp(lean_interpreter_value* stack)
{
uint16_t v_i_458_ = stack[0].m_num;
lean_object* v_res_472_;
v_res_472_ = l_Lean_instToExprInt16___lam__0(v_i_458_);
stack->m_obj
 = v_res_472_;
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt16___lam__0___boxed(lean_object* v_i_473_){
_start:
{
uint16_t v_i_boxed_474_; lean_object* v_res_475_; 
v_i_boxed_474_ = lean_unbox(v_i_473_);
v_res_475_ = l_Lean_instToExprInt16___lam__0(v_i_boxed_474_);
return v_res_475_;
}
}
static lean_object* _init_l_Lean_instToExprInt16___closed__1(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_477_ = lean_box(0);
v___x_478_ = ((lean_object*)(l_Lean_instToExprInt16_mkNat___closed__1));
v___x_479_ = l_Lean_mkConst(v___x_478_, v___x_477_);
return v___x_479_;
}
}
static lean_object* _init_l_Lean_instToExprInt16___closed__2(void){
_start:
{
lean_object* v___x_480_; lean_object* v___f_481_; lean_object* v___x_482_; 
v___x_480_ = lean_obj_once(&l_Lean_instToExprInt16___closed__1, &l_Lean_instToExprInt16___closed__1_once, _init_l_Lean_instToExprInt16___closed__1);
v___f_481_ = ((lean_object*)(l_Lean_instToExprInt16___closed__0));
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v___f_481_);
lean_ctor_set(v___x_482_, 1, v___x_480_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_instToExprInt16(void){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = lean_obj_once(&l_Lean_instToExprInt16___closed__2, &l_Lean_instToExprInt16___closed__2_once, _init_l_Lean_instToExprInt16___closed__2);
return v___x_483_;
}
}
static lean_object* _init_l_Lean_instToExprInt32_mkNat___closed__2(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_487_ = lean_box(0);
v___x_488_ = ((lean_object*)(l_Lean_instToExprInt32_mkNat___closed__1));
v___x_489_ = l_Lean_Expr_const___override(v___x_488_, v___x_487_);
return v___x_489_;
}
}
static lean_object* _init_l_Lean_instToExprInt32_mkNat___closed__4(void){
_start:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_box(0);
v___x_494_ = ((lean_object*)(l_Lean_instToExprInt32_mkNat___closed__3));
v___x_495_ = l_Lean_Expr_const___override(v___x_494_, v___x_493_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt32_mkNat(lean_object* v_n_496_){
_start:
{
lean_object* v_r_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; 
v_r_497_ = l_Lean_mkRawNatLit(v_n_496_);
v___x_498_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_499_ = lean_obj_once(&l_Lean_instToExprInt32_mkNat___closed__2, &l_Lean_instToExprInt32_mkNat___closed__2_once, _init_l_Lean_instToExprInt32_mkNat___closed__2);
v___x_500_ = lean_obj_once(&l_Lean_instToExprInt32_mkNat___closed__4, &l_Lean_instToExprInt32_mkNat___closed__4_once, _init_l_Lean_instToExprInt32_mkNat___closed__4);
lean_inc_ref(v_r_497_);
v___x_501_ = l_Lean_Expr_app___override(v___x_500_, v_r_497_);
v___x_502_ = l_Lean_mkApp3(v___x_498_, v___x_499_, v_r_497_, v___x_501_);
return v___x_502_;
}
}
static uint32_t _init_l_Lean_instToExprInt32___lam__0___closed__0(void){
_start:
{
lean_object* v___x_503_; uint32_t v___x_504_; 
v___x_503_ = lean_unsigned_to_nat(0u);
v___x_504_ = lean_int32_of_nat(v___x_503_);
return v___x_504_;
}
}
static lean_object* _init_l_Lean_instToExprInt32___lam__0___closed__2(void){
_start:
{
lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; 
v___x_508_ = lean_box(0);
v___x_509_ = ((lean_object*)(l_Lean_instToExprInt32___lam__0___closed__1));
v___x_510_ = l_Lean_Expr_const___override(v___x_509_, v___x_508_);
return v___x_510_;
}
}
lean_object* l_Lean_instToExprInt32___lam__0(uint32_t v_i_511_){
_start:
{
uint32_t v___x_512_; uint8_t v___x_513_; 
v___x_512_ = lean_uint32_once(&l_Lean_instToExprInt32___lam__0___closed__0, &l_Lean_instToExprInt32___lam__0___closed__0_once, _init_l_Lean_instToExprInt32___lam__0___closed__0);
v___x_513_ = lean_int32_dec_le(v___x_512_, v_i_511_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_514_ = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__4, &l_Lean_instToExprInt___lam__0___closed__4_once, _init_l_Lean_instToExprInt___lam__0___closed__4);
v___x_515_ = lean_obj_once(&l_Lean_instToExprInt32_mkNat___closed__2, &l_Lean_instToExprInt32_mkNat___closed__2_once, _init_l_Lean_instToExprInt32_mkNat___closed__2);
v___x_516_ = lean_obj_once(&l_Lean_instToExprInt32___lam__0___closed__2, &l_Lean_instToExprInt32___lam__0___closed__2_once, _init_l_Lean_instToExprInt32___lam__0___closed__2);
v___x_517_ = lean_int32_to_int(v_i_511_);
v___x_518_ = lean_int_neg(v___x_517_);
lean_dec(v___x_517_);
v___x_519_ = l_Int_toNat(v___x_518_);
lean_dec(v___x_518_);
v___x_520_ = l_Lean_instToExprInt32_mkNat(v___x_519_);
v___x_521_ = l_Lean_mkApp3(v___x_514_, v___x_515_, v___x_516_, v___x_520_);
return v___x_521_;
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v___x_522_ = lean_int32_to_int(v_i_511_);
v___x_523_ = l_Int_toNat(v___x_522_);
lean_dec(v___x_522_);
v___x_524_ = l_Lean_instToExprInt32_mkNat(v___x_523_);
return v___x_524_;
}
}
}
LEAN_EXPORT void l_Lean_instToExprInt32___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_i_511_ = stack[0].m_num;
lean_object* v_res_525_;
v_res_525_ = l_Lean_instToExprInt32___lam__0(v_i_511_);
stack->m_obj
 = v_res_525_;
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt32___lam__0___boxed(lean_object* v_i_526_){
_start:
{
uint32_t v_i_boxed_527_; lean_object* v_res_528_; 
v_i_boxed_527_ = lean_unbox_uint32(v_i_526_);
lean_dec(v_i_526_);
v_res_528_ = l_Lean_instToExprInt32___lam__0(v_i_boxed_527_);
return v_res_528_;
}
}
static lean_object* _init_l_Lean_instToExprInt32___closed__1(void){
_start:
{
lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_530_ = lean_box(0);
v___x_531_ = ((lean_object*)(l_Lean_instToExprInt32_mkNat___closed__1));
v___x_532_ = l_Lean_mkConst(v___x_531_, v___x_530_);
return v___x_532_;
}
}
static lean_object* _init_l_Lean_instToExprInt32___closed__2(void){
_start:
{
lean_object* v___x_533_; lean_object* v___f_534_; lean_object* v___x_535_; 
v___x_533_ = lean_obj_once(&l_Lean_instToExprInt32___closed__1, &l_Lean_instToExprInt32___closed__1_once, _init_l_Lean_instToExprInt32___closed__1);
v___f_534_ = ((lean_object*)(l_Lean_instToExprInt32___closed__0));
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v___f_534_);
lean_ctor_set(v___x_535_, 1, v___x_533_);
return v___x_535_;
}
}
static lean_object* _init_l_Lean_instToExprInt32(void){
_start:
{
lean_object* v___x_536_; 
v___x_536_ = lean_obj_once(&l_Lean_instToExprInt32___closed__2, &l_Lean_instToExprInt32___closed__2_once, _init_l_Lean_instToExprInt32___closed__2);
return v___x_536_;
}
}
static lean_object* _init_l_Lean_instToExprInt64_mkNat___closed__2(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_540_ = lean_box(0);
v___x_541_ = ((lean_object*)(l_Lean_instToExprInt64_mkNat___closed__1));
v___x_542_ = l_Lean_Expr_const___override(v___x_541_, v___x_540_);
return v___x_542_;
}
}
static lean_object* _init_l_Lean_instToExprInt64_mkNat___closed__4(void){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_546_ = lean_box(0);
v___x_547_ = ((lean_object*)(l_Lean_instToExprInt64_mkNat___closed__3));
v___x_548_ = l_Lean_Expr_const___override(v___x_547_, v___x_546_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt64_mkNat(lean_object* v_n_549_){
_start:
{
lean_object* v_r_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_r_550_ = l_Lean_mkRawNatLit(v_n_549_);
v___x_551_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_552_ = lean_obj_once(&l_Lean_instToExprInt64_mkNat___closed__2, &l_Lean_instToExprInt64_mkNat___closed__2_once, _init_l_Lean_instToExprInt64_mkNat___closed__2);
v___x_553_ = lean_obj_once(&l_Lean_instToExprInt64_mkNat___closed__4, &l_Lean_instToExprInt64_mkNat___closed__4_once, _init_l_Lean_instToExprInt64_mkNat___closed__4);
lean_inc_ref(v_r_550_);
v___x_554_ = l_Lean_Expr_app___override(v___x_553_, v_r_550_);
v___x_555_ = l_Lean_mkApp3(v___x_551_, v___x_552_, v_r_550_, v___x_554_);
return v___x_555_;
}
}
static uint64_t _init_l_Lean_instToExprInt64___lam__0___closed__0(void){
_start:
{
lean_object* v___x_556_; uint64_t v___x_557_; 
v___x_556_ = lean_unsigned_to_nat(0u);
v___x_557_ = lean_int64_of_nat(v___x_556_);
return v___x_557_;
}
}
static lean_object* _init_l_Lean_instToExprInt64___lam__0___closed__2(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_561_ = lean_box(0);
v___x_562_ = ((lean_object*)(l_Lean_instToExprInt64___lam__0___closed__1));
v___x_563_ = l_Lean_Expr_const___override(v___x_562_, v___x_561_);
return v___x_563_;
}
}
lean_object* l_Lean_instToExprInt64___lam__0(uint64_t v_i_564_){
_start:
{
uint64_t v___x_565_; uint8_t v___x_566_; 
v___x_565_ = lean_uint64_once(&l_Lean_instToExprInt64___lam__0___closed__0, &l_Lean_instToExprInt64___lam__0___closed__0_once, _init_l_Lean_instToExprInt64___lam__0___closed__0);
v___x_566_ = lean_int64_dec_le(v___x_565_, v_i_564_);
if (v___x_566_ == 0)
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___x_567_ = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__4, &l_Lean_instToExprInt___lam__0___closed__4_once, _init_l_Lean_instToExprInt___lam__0___closed__4);
v___x_568_ = lean_obj_once(&l_Lean_instToExprInt64_mkNat___closed__2, &l_Lean_instToExprInt64_mkNat___closed__2_once, _init_l_Lean_instToExprInt64_mkNat___closed__2);
v___x_569_ = lean_obj_once(&l_Lean_instToExprInt64___lam__0___closed__2, &l_Lean_instToExprInt64___lam__0___closed__2_once, _init_l_Lean_instToExprInt64___lam__0___closed__2);
v___x_570_ = lean_int64_to_int_sint(v_i_564_);
v___x_571_ = lean_int_neg(v___x_570_);
lean_dec(v___x_570_);
v___x_572_ = l_Int_toNat(v___x_571_);
lean_dec(v___x_571_);
v___x_573_ = l_Lean_instToExprInt64_mkNat(v___x_572_);
v___x_574_ = l_Lean_mkApp3(v___x_567_, v___x_568_, v___x_569_, v___x_573_);
return v___x_574_;
}
else
{
lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_575_ = lean_int64_to_int_sint(v_i_564_);
v___x_576_ = l_Int_toNat(v___x_575_);
lean_dec(v___x_575_);
v___x_577_ = l_Lean_instToExprInt64_mkNat(v___x_576_);
return v___x_577_;
}
}
}
LEAN_EXPORT void l_Lean_instToExprInt64___lam__0_0interp(lean_interpreter_value* stack)
{
uint64_t v_i_564_ = stack[0].m_num;
lean_object* v_res_578_;
v_res_578_ = l_Lean_instToExprInt64___lam__0(v_i_564_);
stack->m_obj
 = v_res_578_;
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt64___lam__0___boxed(lean_object* v_i_579_){
_start:
{
uint64_t v_i_boxed_580_; lean_object* v_res_581_; 
v_i_boxed_580_ = lean_unbox_uint64(v_i_579_);
lean_dec_ref(v_i_579_);
v_res_581_ = l_Lean_instToExprInt64___lam__0(v_i_boxed_580_);
return v_res_581_;
}
}
static lean_object* _init_l_Lean_instToExprInt64___closed__1(void){
_start:
{
lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; 
v___x_583_ = lean_box(0);
v___x_584_ = ((lean_object*)(l_Lean_instToExprInt64_mkNat___closed__1));
v___x_585_ = l_Lean_mkConst(v___x_584_, v___x_583_);
return v___x_585_;
}
}
static lean_object* _init_l_Lean_instToExprInt64___closed__2(void){
_start:
{
lean_object* v___x_586_; lean_object* v___f_587_; lean_object* v___x_588_; 
v___x_586_ = lean_obj_once(&l_Lean_instToExprInt64___closed__1, &l_Lean_instToExprInt64___closed__1_once, _init_l_Lean_instToExprInt64___closed__1);
v___f_587_ = ((lean_object*)(l_Lean_instToExprInt64___closed__0));
v___x_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_588_, 0, v___f_587_);
lean_ctor_set(v___x_588_, 1, v___x_586_);
return v___x_588_;
}
}
static lean_object* _init_l_Lean_instToExprInt64(void){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = lean_obj_once(&l_Lean_instToExprInt64___closed__2, &l_Lean_instToExprInt64___closed__2_once, _init_l_Lean_instToExprInt64___closed__2);
return v___x_589_;
}
}
static lean_object* _init_l_Lean_instToExprISize_mkNat___closed__2(void){
_start:
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_593_ = lean_box(0);
v___x_594_ = ((lean_object*)(l_Lean_instToExprISize_mkNat___closed__1));
v___x_595_ = l_Lean_Expr_const___override(v___x_594_, v___x_593_);
return v___x_595_;
}
}
static lean_object* _init_l_Lean_instToExprISize_mkNat___closed__4(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_599_ = lean_box(0);
v___x_600_ = ((lean_object*)(l_Lean_instToExprISize_mkNat___closed__3));
v___x_601_ = l_Lean_Expr_const___override(v___x_600_, v___x_599_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprISize_mkNat(lean_object* v_n_602_){
_start:
{
lean_object* v_r_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
v_r_603_ = l_Lean_mkRawNatLit(v_n_602_);
v___x_604_ = lean_obj_once(&l_Lean_instToExprInt_mkNat___closed__5, &l_Lean_instToExprInt_mkNat___closed__5_once, _init_l_Lean_instToExprInt_mkNat___closed__5);
v___x_605_ = lean_obj_once(&l_Lean_instToExprISize_mkNat___closed__2, &l_Lean_instToExprISize_mkNat___closed__2_once, _init_l_Lean_instToExprISize_mkNat___closed__2);
v___x_606_ = lean_obj_once(&l_Lean_instToExprISize_mkNat___closed__4, &l_Lean_instToExprISize_mkNat___closed__4_once, _init_l_Lean_instToExprISize_mkNat___closed__4);
lean_inc_ref(v_r_603_);
v___x_607_ = l_Lean_Expr_app___override(v___x_606_, v_r_603_);
v___x_608_ = l_Lean_mkApp3(v___x_604_, v___x_605_, v_r_603_, v___x_607_);
return v___x_608_;
}
}
static size_t _init_l_Lean_instToExprISize___lam__0___closed__0(void){
_start:
{
lean_object* v___x_609_; size_t v___x_610_; 
v___x_609_ = lean_unsigned_to_nat(0u);
v___x_610_ = lean_isize_of_nat(v___x_609_);
return v___x_610_;
}
}
static lean_object* _init_l_Lean_instToExprISize___lam__0___closed__2(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; 
v___x_614_ = lean_box(0);
v___x_615_ = ((lean_object*)(l_Lean_instToExprISize___lam__0___closed__1));
v___x_616_ = l_Lean_Expr_const___override(v___x_615_, v___x_614_);
return v___x_616_;
}
}
lean_object* l_Lean_instToExprISize___lam__0(size_t v_i_617_){
_start:
{
size_t v___x_618_; uint8_t v___x_619_; 
v___x_618_ = lean_usize_once(&l_Lean_instToExprISize___lam__0___closed__0, &l_Lean_instToExprISize___lam__0___closed__0_once, _init_l_Lean_instToExprISize___lam__0___closed__0);
v___x_619_ = lean_isize_dec_le(v___x_618_, v_i_617_);
if (v___x_619_ == 0)
{
lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_620_ = lean_obj_once(&l_Lean_instToExprInt___lam__0___closed__4, &l_Lean_instToExprInt___lam__0___closed__4_once, _init_l_Lean_instToExprInt___lam__0___closed__4);
v___x_621_ = lean_obj_once(&l_Lean_instToExprISize_mkNat___closed__2, &l_Lean_instToExprISize_mkNat___closed__2_once, _init_l_Lean_instToExprISize_mkNat___closed__2);
v___x_622_ = lean_obj_once(&l_Lean_instToExprISize___lam__0___closed__2, &l_Lean_instToExprISize___lam__0___closed__2_once, _init_l_Lean_instToExprISize___lam__0___closed__2);
v___x_623_ = lean_isize_to_int(v_i_617_);
v___x_624_ = lean_int_neg(v___x_623_);
lean_dec(v___x_623_);
v___x_625_ = l_Int_toNat(v___x_624_);
lean_dec(v___x_624_);
v___x_626_ = l_Lean_instToExprISize_mkNat(v___x_625_);
v___x_627_ = l_Lean_mkApp3(v___x_620_, v___x_621_, v___x_622_, v___x_626_);
return v___x_627_;
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = lean_isize_to_int(v_i_617_);
v___x_629_ = l_Int_toNat(v___x_628_);
lean_dec(v___x_628_);
v___x_630_ = l_Lean_instToExprISize_mkNat(v___x_629_);
return v___x_630_;
}
}
}
LEAN_EXPORT void l_Lean_instToExprISize___lam__0_0interp(lean_interpreter_value* stack)
{
size_t v_i_617_ = stack[0].m_num;
lean_object* v_res_631_;
v_res_631_ = l_Lean_instToExprISize___lam__0(v_i_617_);
stack->m_obj
 = v_res_631_;
}
LEAN_EXPORT lean_object* l_Lean_instToExprISize___lam__0___boxed(lean_object* v_i_632_){
_start:
{
size_t v_i_boxed_633_; lean_object* v_res_634_; 
v_i_boxed_633_ = lean_unbox_usize(v_i_632_);
lean_dec(v_i_632_);
v_res_634_ = l_Lean_instToExprISize___lam__0(v_i_boxed_633_);
return v_res_634_;
}
}
static lean_object* _init_l_Lean_instToExprISize___closed__1(void){
_start:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v___x_636_ = lean_box(0);
v___x_637_ = ((lean_object*)(l_Lean_instToExprISize_mkNat___closed__1));
v___x_638_ = l_Lean_mkConst(v___x_637_, v___x_636_);
return v___x_638_;
}
}
static lean_object* _init_l_Lean_instToExprISize___closed__2(void){
_start:
{
lean_object* v___x_639_; lean_object* v___f_640_; lean_object* v___x_641_; 
v___x_639_ = lean_obj_once(&l_Lean_instToExprISize___closed__1, &l_Lean_instToExprISize___closed__1_once, _init_l_Lean_instToExprISize___closed__1);
v___f_640_ = ((lean_object*)(l_Lean_instToExprISize___closed__0));
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v___f_640_);
lean_ctor_set(v___x_641_, 1, v___x_639_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_instToExprISize(void){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = lean_obj_once(&l_Lean_instToExprISize___closed__2, &l_Lean_instToExprISize___closed__2_once, _init_l_Lean_instToExprISize___closed__2);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_instToExprBool___lam__0___closed__3(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v___x_648_ = lean_box(0);
v___x_649_ = ((lean_object*)(l_Lean_instToExprBool___lam__0___closed__2));
v___x_650_ = l_Lean_mkConst(v___x_649_, v___x_648_);
return v___x_650_;
}
}
static lean_object* _init_l_Lean_instToExprBool___lam__0___closed__6(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_655_ = lean_box(0);
v___x_656_ = ((lean_object*)(l_Lean_instToExprBool___lam__0___closed__5));
v___x_657_ = l_Lean_mkConst(v___x_656_, v___x_655_);
return v___x_657_;
}
}
lean_object* l_Lean_instToExprBool___lam__0(uint8_t v_b_658_){
_start:
{
if (v_b_658_ == 0)
{
lean_object* v___x_659_; 
v___x_659_ = lean_obj_once(&l_Lean_instToExprBool___lam__0___closed__3, &l_Lean_instToExprBool___lam__0___closed__3_once, _init_l_Lean_instToExprBool___lam__0___closed__3);
return v___x_659_;
}
else
{
lean_object* v___x_660_; 
v___x_660_ = lean_obj_once(&l_Lean_instToExprBool___lam__0___closed__6, &l_Lean_instToExprBool___lam__0___closed__6_once, _init_l_Lean_instToExprBool___lam__0___closed__6);
return v___x_660_;
}
}
}
LEAN_EXPORT void l_Lean_instToExprBool___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_658_ = stack[0].m_num;
lean_object* v_res_661_;
v_res_661_ = l_Lean_instToExprBool___lam__0(v_b_658_);
stack->m_obj
 = v_res_661_;
}
LEAN_EXPORT lean_object* l_Lean_instToExprBool___lam__0___boxed(lean_object* v_b_662_){
_start:
{
uint8_t v_b_boxed_663_; lean_object* v_res_664_; 
v_b_boxed_663_ = lean_unbox(v_b_662_);
v_res_664_ = l_Lean_instToExprBool___lam__0(v_b_boxed_663_);
return v_res_664_;
}
}
static lean_object* _init_l_Lean_instToExprBool___closed__2(void){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_668_ = lean_box(0);
v___x_669_ = ((lean_object*)(l_Lean_instToExprBool___closed__1));
v___x_670_ = l_Lean_mkConst(v___x_669_, v___x_668_);
return v___x_670_;
}
}
static lean_object* _init_l_Lean_instToExprBool___closed__3(void){
_start:
{
lean_object* v___x_671_; lean_object* v___f_672_; lean_object* v___x_673_; 
v___x_671_ = lean_obj_once(&l_Lean_instToExprBool___closed__2, &l_Lean_instToExprBool___closed__2_once, _init_l_Lean_instToExprBool___closed__2);
v___f_672_ = ((lean_object*)(l_Lean_instToExprBool___closed__0));
v___x_673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_673_, 0, v___f_672_);
lean_ctor_set(v___x_673_, 1, v___x_671_);
return v___x_673_;
}
}
static lean_object* _init_l_Lean_instToExprBool(void){
_start:
{
lean_object* v___x_674_; 
v___x_674_ = lean_obj_once(&l_Lean_instToExprBool___closed__3, &l_Lean_instToExprBool___closed__3_once, _init_l_Lean_instToExprBool___closed__3);
return v___x_674_;
}
}
static lean_object* _init_l_Lean_instToExprChar___lam__0___closed__2(void){
_start:
{
lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_679_ = lean_box(0);
v___x_680_ = ((lean_object*)(l_Lean_instToExprChar___lam__0___closed__1));
v___x_681_ = l_Lean_mkConst(v___x_680_, v___x_679_);
return v___x_681_;
}
}
lean_object* l_Lean_instToExprChar___lam__0(uint32_t v_c_682_){
_start:
{
lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_683_ = lean_obj_once(&l_Lean_instToExprChar___lam__0___closed__2, &l_Lean_instToExprChar___lam__0___closed__2_once, _init_l_Lean_instToExprChar___lam__0___closed__2);
v___x_684_ = lean_uint32_to_nat(v_c_682_);
v___x_685_ = l_Lean_mkRawNatLit(v___x_684_);
v___x_686_ = l_Lean_Expr_app___override(v___x_683_, v___x_685_);
return v___x_686_;
}
}
LEAN_EXPORT void l_Lean_instToExprChar___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_682_ = stack[0].m_num;
lean_object* v_res_687_;
v_res_687_ = l_Lean_instToExprChar___lam__0(v_c_682_);
stack->m_obj
 = v_res_687_;
}
LEAN_EXPORT lean_object* l_Lean_instToExprChar___lam__0___boxed(lean_object* v_c_688_){
_start:
{
uint32_t v_c_boxed_689_; lean_object* v_res_690_; 
v_c_boxed_689_ = lean_unbox_uint32(v_c_688_);
lean_dec(v_c_688_);
v_res_690_ = l_Lean_instToExprChar___lam__0(v_c_boxed_689_);
return v_res_690_;
}
}
static lean_object* _init_l_Lean_instToExprChar___closed__2(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_694_ = lean_box(0);
v___x_695_ = ((lean_object*)(l_Lean_instToExprChar___closed__1));
v___x_696_ = l_Lean_mkConst(v___x_695_, v___x_694_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_instToExprChar___closed__3(void){
_start:
{
lean_object* v___x_697_; lean_object* v___f_698_; lean_object* v___x_699_; 
v___x_697_ = lean_obj_once(&l_Lean_instToExprChar___closed__2, &l_Lean_instToExprChar___closed__2_once, _init_l_Lean_instToExprChar___closed__2);
v___f_698_ = ((lean_object*)(l_Lean_instToExprChar___closed__0));
v___x_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_699_, 0, v___f_698_);
lean_ctor_set(v___x_699_, 1, v___x_697_);
return v___x_699_;
}
}
static lean_object* _init_l_Lean_instToExprChar(void){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = lean_obj_once(&l_Lean_instToExprChar___closed__3, &l_Lean_instToExprChar___closed__3_once, _init_l_Lean_instToExprChar___closed__3);
return v___x_700_;
}
}
static lean_object* _init_l_Lean_instToExprString___closed__3(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = lean_box(0);
v___x_706_ = ((lean_object*)(l_Lean_instToExprString___closed__2));
v___x_707_ = l_Lean_mkConst(v___x_706_, v___x_705_);
return v___x_707_;
}
}
static lean_object* _init_l_Lean_instToExprString___closed__4(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_708_ = lean_obj_once(&l_Lean_instToExprString___closed__3, &l_Lean_instToExprString___closed__3_once, _init_l_Lean_instToExprString___closed__3);
v___x_709_ = ((lean_object*)(l_Lean_instToExprString___closed__0));
v___x_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_709_);
lean_ctor_set(v___x_710_, 1, v___x_708_);
return v___x_710_;
}
}
static lean_object* _init_l_Lean_instToExprString(void){
_start:
{
lean_object* v___x_711_; 
v___x_711_ = lean_obj_once(&l_Lean_instToExprString___closed__4, &l_Lean_instToExprString___closed__4_once, _init_l_Lean_instToExprString___closed__4);
return v___x_711_;
}
}
static lean_object* _init_l_Lean_instToExprUnit___lam__0___closed__3(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = lean_box(0);
v___x_718_ = ((lean_object*)(l_Lean_instToExprUnit___lam__0___closed__2));
v___x_719_ = l_Lean_mkConst(v___x_718_, v___x_717_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUnit___lam__0(lean_object* v_x_720_){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = lean_obj_once(&l_Lean_instToExprUnit___lam__0___closed__3, &l_Lean_instToExprUnit___lam__0___closed__3_once, _init_l_Lean_instToExprUnit___lam__0___closed__3);
return v___x_721_;
}
}
static lean_object* _init_l_Lean_instToExprUnit___closed__2(void){
_start:
{
lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; 
v___x_725_ = lean_box(0);
v___x_726_ = ((lean_object*)(l_Lean_instToExprUnit___closed__1));
v___x_727_ = l_Lean_mkConst(v___x_726_, v___x_725_);
return v___x_727_;
}
}
static lean_object* _init_l_Lean_instToExprUnit___closed__3(void){
_start:
{
lean_object* v___x_728_; lean_object* v___f_729_; lean_object* v___x_730_; 
v___x_728_ = lean_obj_once(&l_Lean_instToExprUnit___closed__2, &l_Lean_instToExprUnit___closed__2_once, _init_l_Lean_instToExprUnit___closed__2);
v___f_729_ = ((lean_object*)(l_Lean_instToExprUnit___closed__0));
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v___f_729_);
lean_ctor_set(v___x_730_, 1, v___x_728_);
return v___x_730_;
}
}
static lean_object* _init_l_Lean_instToExprUnit(void){
_start:
{
lean_object* v___x_731_; 
v___x_731_ = lean_obj_once(&l_Lean_instToExprUnit___closed__3, &l_Lean_instToExprUnit___closed__3_once, _init_l_Lean_instToExprUnit___closed__3);
return v___x_731_;
}
}
static lean_object* _init_l_Lean_instToExprFilePath___lam__0___closed__4(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_box(0);
v___x_740_ = ((lean_object*)(l_Lean_instToExprFilePath___lam__0___closed__3));
v___x_741_ = l_Lean_mkConst(v___x_740_, v___x_739_);
return v___x_741_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprFilePath___lam__0(lean_object* v_p_742_){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = lean_obj_once(&l_Lean_instToExprFilePath___lam__0___closed__4, &l_Lean_instToExprFilePath___lam__0___closed__4_once, _init_l_Lean_instToExprFilePath___lam__0___closed__4);
v___x_744_ = l_Lean_mkStrLit(v_p_742_);
v___x_745_ = l_Lean_Expr_app___override(v___x_743_, v___x_744_);
return v___x_745_;
}
}
static lean_object* _init_l_Lean_instToExprFilePath___closed__2(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
v___x_750_ = lean_box(0);
v___x_751_ = ((lean_object*)(l_Lean_instToExprFilePath___closed__1));
v___x_752_ = l_Lean_mkConst(v___x_751_, v___x_750_);
return v___x_752_;
}
}
static lean_object* _init_l_Lean_instToExprFilePath___closed__3(void){
_start:
{
lean_object* v___x_753_; lean_object* v___f_754_; lean_object* v___x_755_; 
v___x_753_ = lean_obj_once(&l_Lean_instToExprFilePath___closed__2, &l_Lean_instToExprFilePath___closed__2_once, _init_l_Lean_instToExprFilePath___closed__2);
v___f_754_ = ((lean_object*)(l_Lean_instToExprFilePath___closed__0));
v___x_755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_755_, 0, v___f_754_);
lean_ctor_set(v___x_755_, 1, v___x_753_);
return v___x_755_;
}
}
static lean_object* _init_l_Lean_instToExprFilePath(void){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = lean_obj_once(&l_Lean_instToExprFilePath___closed__3, &l_Lean_instToExprFilePath___closed__3_once, _init_l_Lean_instToExprFilePath___closed__3);
return v___x_756_;
}
}
uint8_t l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(lean_object* v_n_757_, lean_object* v_sz_758_){
_start:
{
switch(lean_obj_tag(v_n_757_))
{
case 0:
{
lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_759_ = lean_unsigned_to_nat(0u);
v___x_760_ = lean_nat_dec_lt(v___x_759_, v_sz_758_);
if (v___x_760_ == 0)
{
lean_dec(v_sz_758_);
return v___x_760_;
}
else
{
lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_761_ = lean_unsigned_to_nat(8u);
v___x_762_ = lean_nat_dec_le(v_sz_758_, v___x_761_);
lean_dec(v_sz_758_);
return v___x_762_;
}
}
case 1:
{
lean_object* v_pre_763_; lean_object* v___x_764_; lean_object* v___x_765_; 
v_pre_763_ = lean_ctor_get(v_n_757_, 0);
v___x_764_ = lean_unsigned_to_nat(1u);
v___x_765_ = lean_nat_add(v_sz_758_, v___x_764_);
lean_dec(v_sz_758_);
v_n_757_ = v_pre_763_;
v_sz_758_ = v___x_765_;
goto _start;
}
default: 
{
uint8_t v___x_767_; 
lean_dec(v_sz_758_);
v___x_767_ = 0;
return v___x_767_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_757_ = stack[0].m_obj;
lean_object* v_sz_758_ = stack[1].m_obj;
uint8_t v_res_768_;
v_res_768_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(v_n_757_, v_sz_758_);
stack->m_num = v_res_768_;
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple___boxed(lean_object* v_n_769_, lean_object* v_sz_770_){
_start:
{
uint8_t v_res_771_; lean_object* v_r_772_; 
v_res_771_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(v_n_769_, v_sz_770_);
lean_dec(v_n_769_);
v_r_772_ = lean_box(v_res_771_);
return v_r_772_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr_spec__0(lean_object* v_msg_773_){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_774_ = l_Lean_instInhabitedExpr;
v___x_775_ = lean_panic_fn_borrowed(v___x_774_, v_msg_773_);
return v___x_775_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_785_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__6));
v___x_786_ = lean_unsigned_to_nat(11u);
v___x_787_ = lean_unsigned_to_nat(221u);
v___x_788_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__5));
v___x_789_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__4));
v___x_790_ = l_mkPanicMessageWithDecl(v___x_789_, v___x_788_, v___x_787_, v___x_786_, v___x_785_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr(lean_object* v_n_791_, lean_object* v_sz_792_, lean_object* v_args_793_){
_start:
{
switch(lean_obj_tag(v_n_791_))
{
case 0:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_794_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2));
v___x_795_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__3));
v___x_796_ = l_Nat_reprFast(v_sz_792_);
v___x_797_ = lean_string_append(v___x_795_, v___x_796_);
lean_dec_ref(v___x_796_);
v___x_798_ = l_Lean_Name_str___override(v___x_794_, v___x_797_);
v___x_799_ = lean_box(0);
v___x_800_ = l_Lean_mkConst(v___x_798_, v___x_799_);
v___x_801_ = l_Array_reverse___redArg(v_args_793_);
v___x_802_ = l_Lean_mkAppN(v___x_800_, v___x_801_);
lean_dec_ref(v___x_801_);
return v___x_802_;
}
case 1:
{
lean_object* v_pre_803_; lean_object* v_str_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; 
v_pre_803_ = lean_ctor_get(v_n_791_, 0);
lean_inc(v_pre_803_);
v_str_804_ = lean_ctor_get(v_n_791_, 1);
lean_inc_ref(v_str_804_);
lean_dec_ref_known(v_n_791_, 2);
v___x_805_ = lean_unsigned_to_nat(1u);
v___x_806_ = lean_nat_add(v_sz_792_, v___x_805_);
lean_dec(v_sz_792_);
v___x_807_ = l_Lean_mkStrLit(v_str_804_);
v___x_808_ = lean_array_push(v_args_793_, v___x_807_);
v_n_791_ = v_pre_803_;
v_sz_792_ = v___x_806_;
v_args_793_ = v___x_808_;
goto _start;
}
default: 
{
lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec_ref(v_args_793_);
lean_dec(v_sz_792_);
lean_dec(v_n_791_);
v___x_810_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7, &l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7_once, _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__7);
v___x_811_ = l_panic___at___00__private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr_spec__0(v___x_810_);
return v___x_811_;
}
}
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2(void){
_start:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = lean_box(0);
v___x_818_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__1));
v___x_819_ = l_Lean_mkConst(v___x_818_, v___x_817_);
return v___x_819_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_825_ = lean_box(0);
v___x_826_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__4));
v___x_827_ = l_Lean_mkConst(v___x_826_, v___x_825_);
return v___x_827_;
}
}
static lean_object* _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8(void){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v___x_833_ = lean_box(0);
v___x_834_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__7));
v___x_835_ = l_Lean_mkConst(v___x_834_, v___x_833_);
return v___x_835_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(lean_object* v_a_836_){
_start:
{
switch(lean_obj_tag(v_a_836_))
{
case 0:
{
lean_object* v___x_837_; 
v___x_837_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2, &l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2_once, _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__2);
return v___x_837_;
}
case 1:
{
lean_object* v_pre_838_; lean_object* v_str_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; 
v_pre_838_ = lean_ctor_get(v_a_836_, 0);
lean_inc(v_pre_838_);
v_str_839_ = lean_ctor_get(v_a_836_, 1);
lean_inc_ref(v_str_839_);
lean_dec_ref_known(v_a_836_, 2);
v___x_840_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5, &l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5_once, _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__5);
v___x_841_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(v_pre_838_);
v___x_842_ = l_Lean_mkStrLit(v_str_839_);
v___x_843_ = l_Lean_mkAppB(v___x_840_, v___x_841_, v___x_842_);
return v___x_843_;
}
default: 
{
lean_object* v_pre_844_; lean_object* v_i_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_pre_844_ = lean_ctor_get(v_a_836_, 0);
lean_inc(v_pre_844_);
v_i_845_ = lean_ctor_get(v_a_836_, 1);
lean_inc(v_i_845_);
lean_dec_ref_known(v_a_836_, 2);
v___x_846_ = lean_obj_once(&l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8, &l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8_once, _init_l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go___closed__8);
v___x_847_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(v_pre_844_);
v___x_848_ = l_Lean_mkNatLit(v_i_845_);
v___x_849_ = l_Lean_mkAppB(v___x_846_, v___x_847_, v___x_848_);
return v___x_849_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object* v_n_852_){
_start:
{
lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_853_ = lean_unsigned_to_nat(0u);
v___x_854_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(v_n_852_, v___x_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; 
v___x_855_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(v_n_852_);
return v___x_855_;
}
else
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux___closed__0));
v___x_857_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr(v_n_852_, v___x_853_, v___x_856_);
return v___x_857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprName___private__1(lean_object* v_n_858_){
_start:
{
lean_object* v___x_859_; 
v___x_859_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_n_858_);
return v___x_859_;
}
}
static lean_object* _init_l_Lean_instToExprName___closed__1(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
v___x_861_ = lean_box(0);
v___x_862_ = ((lean_object*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr___closed__2));
v___x_863_ = l_Lean_mkConst(v___x_862_, v___x_861_);
return v___x_863_;
}
}
static lean_object* _init_l_Lean_instToExprName___closed__2(void){
_start:
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; 
v___x_864_ = lean_obj_once(&l_Lean_instToExprName___closed__1, &l_Lean_instToExprName___closed__1_once, _init_l_Lean_instToExprName___closed__1);
v___x_865_ = ((lean_object*)(l_Lean_instToExprName___closed__0));
v___x_866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_865_);
lean_ctor_set(v___x_866_, 1, v___x_864_);
return v___x_866_;
}
}
static lean_object* _init_l_Lean_instToExprName(void){
_start:
{
lean_object* v___x_867_; 
v___x_867_ = lean_obj_once(&l_Lean_instToExprName___closed__2, &l_Lean_instToExprName___closed__2_once, _init_l_Lean_instToExprName___closed__2);
return v___x_867_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprOptionOfToLevel___redArg___lam__0(lean_object* v_inst_877_, lean_object* v_toTypeExpr_878_, lean_object* v_toExpr_879_, lean_object* v_o_880_){
_start:
{
if (lean_obj_tag(v_o_880_) == 0)
{
lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
lean_dec_ref(v_toExpr_879_);
v___x_881_ = ((lean_object*)(l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__2));
v___x_882_ = lean_box(0);
v___x_883_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_883_, 0, v_inst_877_);
lean_ctor_set(v___x_883_, 1, v___x_882_);
v___x_884_ = l_Lean_mkConst(v___x_881_, v___x_883_);
v___x_885_ = l_Lean_Expr_app___override(v___x_884_, v_toTypeExpr_878_);
return v___x_885_;
}
else
{
lean_object* v_val_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
v_val_886_ = lean_ctor_get(v_o_880_, 0);
lean_inc(v_val_886_);
lean_dec_ref_known(v_o_880_, 1);
v___x_887_ = ((lean_object*)(l_Lean_instToExprOptionOfToLevel___redArg___lam__0___closed__4));
v___x_888_ = lean_box(0);
v___x_889_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_889_, 0, v_inst_877_);
lean_ctor_set(v___x_889_, 1, v___x_888_);
v___x_890_ = l_Lean_mkConst(v___x_887_, v___x_889_);
v___x_891_ = lean_apply_1(v_toExpr_879_, v_val_886_);
v___x_892_ = l_Lean_mkAppB(v___x_890_, v_toTypeExpr_878_, v___x_891_);
return v___x_892_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprOptionOfToLevel___redArg(lean_object* v_inst_895_, lean_object* v_inst_896_){
_start:
{
lean_object* v_toExpr_897_; lean_object* v_toTypeExpr_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_911_; 
v_toExpr_897_ = lean_ctor_get(v_inst_896_, 0);
v_toTypeExpr_898_ = lean_ctor_get(v_inst_896_, 1);
v_isSharedCheck_911_ = !lean_is_exclusive(v_inst_896_);
if (v_isSharedCheck_911_ == 0)
{
v___x_900_ = v_inst_896_;
v_isShared_901_ = v_isSharedCheck_911_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_toTypeExpr_898_);
lean_inc(v_toExpr_897_);
lean_dec(v_inst_896_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_911_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___f_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
lean_inc_ref(v_toTypeExpr_898_);
lean_inc(v_inst_895_);
v___f_902_ = lean_alloc_closure((void*)(l_Lean_instToExprOptionOfToLevel___redArg___lam__0), 4, 3);
lean_closure_set(v___f_902_, 0, v_inst_895_);
lean_closure_set(v___f_902_, 1, v_toTypeExpr_898_);
lean_closure_set(v___f_902_, 2, v_toExpr_897_);
v___x_903_ = ((lean_object*)(l_Lean_instToExprOptionOfToLevel___redArg___closed__0));
v___x_904_ = lean_box(0);
v___x_905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_905_, 0, v_inst_895_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = l_Lean_mkConst(v___x_903_, v___x_905_);
v___x_907_ = l_Lean_Expr_app___override(v___x_906_, v_toTypeExpr_898_);
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 1, v___x_907_);
lean_ctor_set(v___x_900_, 0, v___f_902_);
v___x_909_ = v___x_900_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___f_902_);
lean_ctor_set(v_reuseFailAlloc_910_, 1, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprOptionOfToLevel(lean_object* v_00_u03b1_912_, lean_object* v_inst_913_, lean_object* v_inst_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_instToExprOptionOfToLevel___redArg(v_inst_913_, v_inst_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(lean_object* v_inst_916_, lean_object* v_nilFn_917_, lean_object* v_consFn_918_, lean_object* v_x_919_){
_start:
{
if (lean_obj_tag(v_x_919_) == 0)
{
lean_dec_ref(v_consFn_918_);
lean_dec_ref(v_inst_916_);
lean_inc_ref(v_nilFn_917_);
return v_nilFn_917_;
}
else
{
lean_object* v_head_920_; lean_object* v_tail_921_; lean_object* v_toExpr_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v_head_920_ = lean_ctor_get(v_x_919_, 0);
lean_inc(v_head_920_);
v_tail_921_ = lean_ctor_get(v_x_919_, 1);
lean_inc(v_tail_921_);
lean_dec_ref_known(v_x_919_, 2);
v_toExpr_922_ = lean_ctor_get(v_inst_916_, 0);
lean_inc_ref(v_toExpr_922_);
v___x_923_ = lean_apply_1(v_toExpr_922_, v_head_920_);
lean_inc_ref(v_consFn_918_);
v___x_924_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(v_inst_916_, v_nilFn_917_, v_consFn_918_, v_tail_921_);
v___x_925_ = l_Lean_mkAppB(v_consFn_918_, v___x_923_, v___x_924_);
return v___x_925_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg___boxed(lean_object* v_inst_926_, lean_object* v_nilFn_927_, lean_object* v_consFn_928_, lean_object* v_x_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(v_inst_926_, v_nilFn_927_, v_consFn_928_, v_x_929_);
lean_dec_ref(v_nilFn_927_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_object* v_00_u03b1_931_, lean_object* v_inst_932_, lean_object* v_nilFn_933_, lean_object* v_consFn_934_, lean_object* v_x_935_){
_start:
{
lean_object* v___x_936_; 
v___x_936_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(v_inst_932_, v_nilFn_933_, v_consFn_934_, v_x_935_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___boxed(lean_object* v_00_u03b1_937_, lean_object* v_inst_938_, lean_object* v_nilFn_939_, lean_object* v_consFn_940_, lean_object* v_x_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux(v_00_u03b1_937_, v_inst_938_, v_nilFn_939_, v_consFn_940_, v_x_941_);
lean_dec_ref(v_nilFn_939_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___private__1___redArg(lean_object* v_inst_943_, lean_object* v_nil_944_, lean_object* v_cons_945_, lean_object* v_a_946_){
_start:
{
lean_object* v___x_947_; 
v___x_947_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(v_inst_943_, v_nil_944_, v_cons_945_, v_a_946_);
return v___x_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___private__1___redArg___boxed(lean_object* v_inst_948_, lean_object* v_nil_949_, lean_object* v_cons_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_instToExprListOfToLevel___private__1___redArg(v_inst_948_, v_nil_949_, v_cons_950_, v_a_951_);
lean_dec_ref(v_nil_949_);
return v_res_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___private__1(lean_object* v_00_u03b1_953_, lean_object* v_inst_954_, lean_object* v_nil_955_, lean_object* v_cons_956_, lean_object* v_a_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(v_inst_954_, v_nil_955_, v_cons_956_, v_a_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___private__1___boxed(lean_object* v_00_u03b1_959_, lean_object* v_inst_960_, lean_object* v_nil_961_, lean_object* v_cons_962_, lean_object* v_a_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_instToExprListOfToLevel___private__1(v_00_u03b1_959_, v_inst_960_, v_nil_961_, v_cons_962_, v_a_963_);
lean_dec_ref(v_nil_961_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___redArg(lean_object* v_inst_976_, lean_object* v_inst_977_){
_start:
{
lean_object* v_toTypeExpr_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v_nil_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v_cons_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
v_toTypeExpr_978_ = lean_ctor_get(v_inst_977_, 1);
lean_inc_ref_n(v_toTypeExpr_978_, 3);
v___x_979_ = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__2));
v___x_980_ = lean_box(0);
v___x_981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_981_, 0, v_inst_976_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
lean_inc_ref_n(v___x_981_, 2);
v___x_982_ = l_Lean_mkConst(v___x_979_, v___x_981_);
v_nil_983_ = l_Lean_Expr_app___override(v___x_982_, v_toTypeExpr_978_);
v___x_984_ = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__4));
v___x_985_ = l_Lean_mkConst(v___x_984_, v___x_981_);
v_cons_986_ = l_Lean_Expr_app___override(v___x_985_, v_toTypeExpr_978_);
v___x_987_ = lean_alloc_closure((void*)(l_Lean_instToExprListOfToLevel___private__1___boxed), 5, 4);
lean_closure_set(v___x_987_, 0, lean_box(0));
lean_closure_set(v___x_987_, 1, v_inst_977_);
lean_closure_set(v___x_987_, 2, v_nil_983_);
lean_closure_set(v___x_987_, 3, v_cons_986_);
v___x_988_ = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__5));
v___x_989_ = l_Lean_mkConst(v___x_988_, v___x_981_);
v___x_990_ = l_Lean_Expr_app___override(v___x_989_, v_toTypeExpr_978_);
v___x_991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_991_, 0, v___x_987_);
lean_ctor_set(v___x_991_, 1, v___x_990_);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel(lean_object* v_00_u03b1_992_, lean_object* v_inst_993_, lean_object* v_inst_994_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l_Lean_instToExprListOfToLevel___redArg(v_inst_993_, v_inst_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprArrayOfToLevel___redArg___lam__0(lean_object* v_inst_1000_, lean_object* v_toTypeExpr_1001_, lean_object* v_inst_1002_, lean_object* v_as_1003_){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v_nil_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v_cons_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1004_ = ((lean_object*)(l_Lean_instToExprArrayOfToLevel___redArg___lam__0___closed__1));
v___x_1005_ = lean_box(0);
v___x_1006_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1006_, 0, v_inst_1000_);
lean_ctor_set(v___x_1006_, 1, v___x_1005_);
lean_inc_ref_n(v___x_1006_, 2);
v___x_1007_ = l_Lean_mkConst(v___x_1004_, v___x_1006_);
v___x_1008_ = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__2));
v___x_1009_ = l_Lean_mkConst(v___x_1008_, v___x_1006_);
lean_inc_ref_n(v_toTypeExpr_1001_, 2);
v_nil_1010_ = l_Lean_Expr_app___override(v___x_1009_, v_toTypeExpr_1001_);
v___x_1011_ = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__4));
v___x_1012_ = l_Lean_mkConst(v___x_1011_, v___x_1006_);
v_cons_1013_ = l_Lean_Expr_app___override(v___x_1012_, v_toTypeExpr_1001_);
v___x_1014_ = lean_array_to_list(v_as_1003_);
v___x_1015_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(v_inst_1002_, v_nil_1010_, v_cons_1013_, v___x_1014_);
lean_dec_ref(v_nil_1010_);
v___x_1016_ = l_Lean_mkAppB(v___x_1007_, v_toTypeExpr_1001_, v___x_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprArrayOfToLevel___redArg(lean_object* v_inst_1020_, lean_object* v_inst_1021_){
_start:
{
lean_object* v_toTypeExpr_1022_; lean_object* v___f_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v_toTypeExpr_1022_ = lean_ctor_get(v_inst_1021_, 1);
lean_inc_ref_n(v_toTypeExpr_1022_, 2);
lean_inc(v_inst_1020_);
v___f_1023_ = lean_alloc_closure((void*)(l_Lean_instToExprArrayOfToLevel___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1023_, 0, v_inst_1020_);
lean_closure_set(v___f_1023_, 1, v_toTypeExpr_1022_);
lean_closure_set(v___f_1023_, 2, v_inst_1021_);
v___x_1024_ = ((lean_object*)(l_Lean_instToExprArrayOfToLevel___redArg___closed__1));
v___x_1025_ = lean_box(0);
v___x_1026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1026_, 0, v_inst_1020_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = l_Lean_mkConst(v___x_1024_, v___x_1026_);
v___x_1028_ = l_Lean_Expr_app___override(v___x_1027_, v_toTypeExpr_1022_);
v___x_1029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___f_1023_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprArrayOfToLevel(lean_object* v_00_u03b1_1030_, lean_object* v_inst_1031_, lean_object* v_inst_1032_){
_start:
{
lean_object* v___x_1033_; 
v___x_1033_ = l_Lean_instToExprArrayOfToLevel___redArg(v_inst_1031_, v_inst_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprProdOfToLevel___redArg___lam__0(lean_object* v_inst_1038_, lean_object* v_inst_1039_, lean_object* v_toExpr_1040_, lean_object* v_toExpr_1041_, lean_object* v_toTypeExpr_1042_, lean_object* v_toTypeExpr_1043_, lean_object* v_x_1044_){
_start:
{
lean_object* v_fst_1045_; lean_object* v_snd_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1060_; 
v_fst_1045_ = lean_ctor_get(v_x_1044_, 0);
v_snd_1046_ = lean_ctor_get(v_x_1044_, 1);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_x_1044_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1048_ = v_x_1044_;
v_isShared_1049_ = v_isSharedCheck_1060_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_snd_1046_);
lean_inc(v_fst_1045_);
lean_dec(v_x_1044_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1060_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1053_; 
v___x_1050_ = ((lean_object*)(l_Lean_instToExprProdOfToLevel___redArg___lam__0___closed__1));
v___x_1051_ = lean_box(0);
if (v_isShared_1049_ == 0)
{
lean_ctor_set_tag(v___x_1048_, 1);
lean_ctor_set(v___x_1048_, 1, v___x_1051_);
lean_ctor_set(v___x_1048_, 0, v_inst_1038_);
v___x_1053_ = v___x_1048_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_inst_1038_);
lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___x_1051_);
v___x_1053_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1054_, 0, v_inst_1039_);
lean_ctor_set(v___x_1054_, 1, v___x_1053_);
v___x_1055_ = l_Lean_mkConst(v___x_1050_, v___x_1054_);
v___x_1056_ = lean_apply_1(v_toExpr_1040_, v_fst_1045_);
v___x_1057_ = lean_apply_1(v_toExpr_1041_, v_snd_1046_);
v___x_1058_ = l_Lean_mkApp4(v___x_1055_, v_toTypeExpr_1042_, v_toTypeExpr_1043_, v___x_1056_, v___x_1057_);
return v___x_1058_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprProdOfToLevel___redArg(lean_object* v_inst_1063_, lean_object* v_inst_1064_, lean_object* v_inst_1065_, lean_object* v_inst_1066_){
_start:
{
lean_object* v_toExpr_1067_; lean_object* v_toTypeExpr_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1090_; 
v_toExpr_1067_ = lean_ctor_get(v_inst_1065_, 0);
v_toTypeExpr_1068_ = lean_ctor_get(v_inst_1065_, 1);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_inst_1065_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1070_ = v_inst_1065_;
v_isShared_1071_ = v_isSharedCheck_1090_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_toTypeExpr_1068_);
lean_inc(v_toExpr_1067_);
lean_dec(v_inst_1065_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1090_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v_toExpr_1072_; lean_object* v_toTypeExpr_1073_; lean_object* v___x_1075_; uint8_t v_isShared_1076_; uint8_t v_isSharedCheck_1089_; 
v_toExpr_1072_ = lean_ctor_get(v_inst_1066_, 0);
v_toTypeExpr_1073_ = lean_ctor_get(v_inst_1066_, 1);
v_isSharedCheck_1089_ = !lean_is_exclusive(v_inst_1066_);
if (v_isSharedCheck_1089_ == 0)
{
v___x_1075_ = v_inst_1066_;
v_isShared_1076_ = v_isSharedCheck_1089_;
goto v_resetjp_1074_;
}
else
{
lean_inc(v_toTypeExpr_1073_);
lean_inc(v_toExpr_1072_);
lean_dec(v_inst_1066_);
v___x_1075_ = lean_box(0);
v_isShared_1076_ = v_isSharedCheck_1089_;
goto v_resetjp_1074_;
}
v_resetjp_1074_:
{
lean_object* v___f_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1081_; 
lean_inc_ref(v_toTypeExpr_1073_);
lean_inc_ref(v_toTypeExpr_1068_);
lean_inc(v_inst_1063_);
lean_inc(v_inst_1064_);
v___f_1077_ = lean_alloc_closure((void*)(l_Lean_instToExprProdOfToLevel___redArg___lam__0), 7, 6);
lean_closure_set(v___f_1077_, 0, v_inst_1064_);
lean_closure_set(v___f_1077_, 1, v_inst_1063_);
lean_closure_set(v___f_1077_, 2, v_toExpr_1067_);
lean_closure_set(v___f_1077_, 3, v_toExpr_1072_);
lean_closure_set(v___f_1077_, 4, v_toTypeExpr_1068_);
lean_closure_set(v___f_1077_, 5, v_toTypeExpr_1073_);
v___x_1078_ = ((lean_object*)(l_Lean_instToExprProdOfToLevel___redArg___closed__0));
v___x_1079_ = lean_box(0);
if (v_isShared_1071_ == 0)
{
lean_ctor_set_tag(v___x_1070_, 1);
lean_ctor_set(v___x_1070_, 1, v___x_1079_);
lean_ctor_set(v___x_1070_, 0, v_inst_1064_);
v___x_1081_ = v___x_1070_;
goto v_reusejp_1080_;
}
else
{
lean_object* v_reuseFailAlloc_1088_; 
v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1088_, 0, v_inst_1064_);
lean_ctor_set(v_reuseFailAlloc_1088_, 1, v___x_1079_);
v___x_1081_ = v_reuseFailAlloc_1088_;
goto v_reusejp_1080_;
}
v_reusejp_1080_:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
v___x_1082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1082_, 0, v_inst_1063_);
lean_ctor_set(v___x_1082_, 1, v___x_1081_);
v___x_1083_ = l_Lean_mkConst(v___x_1078_, v___x_1082_);
v___x_1084_ = l_Lean_mkAppB(v___x_1083_, v_toTypeExpr_1068_, v_toTypeExpr_1073_);
if (v_isShared_1076_ == 0)
{
lean_ctor_set(v___x_1075_, 1, v___x_1084_);
lean_ctor_set(v___x_1075_, 0, v___f_1077_);
v___x_1086_ = v___x_1075_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v___f_1077_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprProdOfToLevel(lean_object* v_00_u03b1_1091_, lean_object* v_00_u03b2_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_inst_1095_, lean_object* v_inst_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_instToExprProdOfToLevel___redArg(v_inst_1093_, v_inst_1094_, v_inst_1095_, v_inst_1096_);
return v___x_1097_;
}
}
static lean_object* _init_l_Lean_instToExprLiteral___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1104_ = lean_box(0);
v___x_1105_ = ((lean_object*)(l_Lean_instToExprLiteral___lam__0___closed__2));
v___x_1106_ = l_Lean_mkConst(v___x_1105_, v___x_1104_);
return v___x_1106_;
}
}
static lean_object* _init_l_Lean_instToExprLiteral___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1112_ = lean_box(0);
v___x_1113_ = ((lean_object*)(l_Lean_instToExprLiteral___lam__0___closed__5));
v___x_1114_ = l_Lean_mkConst(v___x_1113_, v___x_1112_);
return v___x_1114_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprLiteral___lam__0(lean_object* v_l_1115_){
_start:
{
if (lean_obj_tag(v_l_1115_) == 0)
{
lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = lean_obj_once(&l_Lean_instToExprLiteral___lam__0___closed__3, &l_Lean_instToExprLiteral___lam__0___closed__3_once, _init_l_Lean_instToExprLiteral___lam__0___closed__3);
v___x_1117_ = l_Lean_Expr_lit___override(v_l_1115_);
v___x_1118_ = l_Lean_Expr_app___override(v___x_1116_, v___x_1117_);
return v___x_1118_;
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1119_ = lean_obj_once(&l_Lean_instToExprLiteral___lam__0___closed__6, &l_Lean_instToExprLiteral___lam__0___closed__6_once, _init_l_Lean_instToExprLiteral___lam__0___closed__6);
v___x_1120_ = l_Lean_Expr_lit___override(v_l_1115_);
v___x_1121_ = l_Lean_Expr_app___override(v___x_1119_, v___x_1120_);
return v___x_1121_;
}
}
}
static lean_object* _init_l_Lean_instToExprLiteral___closed__2(void){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v___x_1126_ = lean_box(0);
v___x_1127_ = ((lean_object*)(l_Lean_instToExprLiteral___closed__1));
v___x_1128_ = l_Lean_mkConst(v___x_1127_, v___x_1126_);
return v___x_1128_;
}
}
static lean_object* _init_l_Lean_instToExprLiteral___closed__3(void){
_start:
{
lean_object* v___x_1129_; lean_object* v___f_1130_; lean_object* v___x_1131_; 
v___x_1129_ = lean_obj_once(&l_Lean_instToExprLiteral___closed__2, &l_Lean_instToExprLiteral___closed__2_once, _init_l_Lean_instToExprLiteral___closed__2);
v___f_1130_ = ((lean_object*)(l_Lean_instToExprLiteral___closed__0));
v___x_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___f_1130_);
lean_ctor_set(v___x_1131_, 1, v___x_1129_);
return v___x_1131_;
}
}
static lean_object* _init_l_Lean_instToExprLiteral(void){
_start:
{
lean_object* v___x_1132_; 
v___x_1132_ = lean_obj_once(&l_Lean_instToExprLiteral___closed__3, &l_Lean_instToExprLiteral___closed__3_once, _init_l_Lean_instToExprLiteral___closed__3);
return v___x_1132_;
}
}
static lean_object* _init_l_Lean_instToExprFVarId___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1138_ = lean_box(0);
v___x_1139_ = ((lean_object*)(l_Lean_instToExprFVarId___lam__0___closed__1));
v___x_1140_ = l_Lean_mkConst(v___x_1139_, v___x_1138_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprFVarId___lam__0(lean_object* v_fvarId_1141_){
_start:
{
lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1142_ = lean_obj_once(&l_Lean_instToExprFVarId___lam__0___closed__2, &l_Lean_instToExprFVarId___lam__0___closed__2_once, _init_l_Lean_instToExprFVarId___lam__0___closed__2);
v___x_1143_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_fvarId_1141_);
v___x_1144_ = l_Lean_Expr_app___override(v___x_1142_, v___x_1143_);
return v___x_1144_;
}
}
static lean_object* _init_l_Lean_instToExprFVarId___closed__2(void){
_start:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = lean_box(0);
v___x_1150_ = ((lean_object*)(l_Lean_instToExprFVarId___closed__1));
v___x_1151_ = l_Lean_mkConst(v___x_1150_, v___x_1149_);
return v___x_1151_;
}
}
static lean_object* _init_l_Lean_instToExprFVarId___closed__3(void){
_start:
{
lean_object* v___x_1152_; lean_object* v___f_1153_; lean_object* v___x_1154_; 
v___x_1152_ = lean_obj_once(&l_Lean_instToExprFVarId___closed__2, &l_Lean_instToExprFVarId___closed__2_once, _init_l_Lean_instToExprFVarId___closed__2);
v___f_1153_ = ((lean_object*)(l_Lean_instToExprFVarId___closed__0));
v___x_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1154_, 0, v___f_1153_);
lean_ctor_set(v___x_1154_, 1, v___x_1152_);
return v___x_1154_;
}
}
static lean_object* _init_l_Lean_instToExprFVarId(void){
_start:
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_obj_once(&l_Lean_instToExprFVarId___closed__3, &l_Lean_instToExprFVarId___closed__3_once, _init_l_Lean_instToExprFVarId___closed__3);
return v___x_1155_;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1164_ = lean_box(0);
v___x_1165_ = ((lean_object*)(l_Lean_instToExprPreresolved___lam__0___closed__3));
v___x_1166_ = l_Lean_Expr_const___override(v___x_1165_, v___x_1164_);
return v___x_1166_;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1173_ = lean_box(0);
v___x_1174_ = ((lean_object*)(l_Lean_instToExprPreresolved___lam__0___closed__6));
v___x_1175_ = l_Lean_Expr_const___override(v___x_1174_, v___x_1173_);
return v___x_1175_;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___lam__0___closed__9(void){
_start:
{
lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1179_ = ((lean_object*)(l_Lean_instToExprPreresolved___lam__0___closed__8));
v___x_1180_ = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__2));
v___x_1181_ = l_Lean_mkConst(v___x_1180_, v___x_1179_);
return v___x_1181_;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___lam__0___closed__10(void){
_start:
{
lean_object* v_type_1182_; lean_object* v___x_1183_; lean_object* v_nil_1184_; 
v_type_1182_ = lean_obj_once(&l_Lean_instToExprString___closed__3, &l_Lean_instToExprString___closed__3_once, _init_l_Lean_instToExprString___closed__3);
v___x_1183_ = lean_obj_once(&l_Lean_instToExprPreresolved___lam__0___closed__9, &l_Lean_instToExprPreresolved___lam__0___closed__9_once, _init_l_Lean_instToExprPreresolved___lam__0___closed__9);
v_nil_1184_ = l_Lean_Expr_app___override(v___x_1183_, v_type_1182_);
return v_nil_1184_;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___lam__0___closed__11(void){
_start:
{
lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1185_ = ((lean_object*)(l_Lean_instToExprPreresolved___lam__0___closed__8));
v___x_1186_ = ((lean_object*)(l_Lean_instToExprListOfToLevel___redArg___closed__4));
v___x_1187_ = l_Lean_mkConst(v___x_1186_, v___x_1185_);
return v___x_1187_;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___lam__0___closed__12(void){
_start:
{
lean_object* v_type_1188_; lean_object* v___x_1189_; lean_object* v_cons_1190_; 
v_type_1188_ = lean_obj_once(&l_Lean_instToExprString___closed__3, &l_Lean_instToExprString___closed__3_once, _init_l_Lean_instToExprString___closed__3);
v___x_1189_ = lean_obj_once(&l_Lean_instToExprPreresolved___lam__0___closed__11, &l_Lean_instToExprPreresolved___lam__0___closed__11_once, _init_l_Lean_instToExprPreresolved___lam__0___closed__11);
v_cons_1190_ = l_Lean_Expr_app___override(v___x_1189_, v_type_1188_);
return v_cons_1190_;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprPreresolved___lam__0(lean_object* v___x_1191_, lean_object* v_x_1192_){
_start:
{
if (lean_obj_tag(v_x_1192_) == 0)
{
lean_object* v_ns_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
lean_dec_ref(v___x_1191_);
v_ns_1193_ = lean_ctor_get(v_x_1192_, 0);
lean_inc(v_ns_1193_);
lean_dec_ref_known(v_x_1192_, 1);
v___x_1194_ = lean_obj_once(&l_Lean_instToExprPreresolved___lam__0___closed__4, &l_Lean_instToExprPreresolved___lam__0___closed__4_once, _init_l_Lean_instToExprPreresolved___lam__0___closed__4);
v___x_1195_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_ns_1193_);
v___x_1196_ = l_Lean_Expr_app___override(v___x_1194_, v___x_1195_);
return v___x_1196_;
}
else
{
lean_object* v_n_1197_; lean_object* v_fields_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v_nil_1201_; lean_object* v_cons_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v_n_1197_ = lean_ctor_get(v_x_1192_, 0);
lean_inc(v_n_1197_);
v_fields_1198_ = lean_ctor_get(v_x_1192_, 1);
lean_inc(v_fields_1198_);
lean_dec_ref_known(v_x_1192_, 2);
v___x_1199_ = lean_obj_once(&l_Lean_instToExprPreresolved___lam__0___closed__7, &l_Lean_instToExprPreresolved___lam__0___closed__7_once, _init_l_Lean_instToExprPreresolved___lam__0___closed__7);
v___x_1200_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_n_1197_);
v_nil_1201_ = lean_obj_once(&l_Lean_instToExprPreresolved___lam__0___closed__10, &l_Lean_instToExprPreresolved___lam__0___closed__10_once, _init_l_Lean_instToExprPreresolved___lam__0___closed__10);
v_cons_1202_ = lean_obj_once(&l_Lean_instToExprPreresolved___lam__0___closed__12, &l_Lean_instToExprPreresolved___lam__0___closed__12_once, _init_l_Lean_instToExprPreresolved___lam__0___closed__12);
v___x_1203_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(v___x_1191_, v_nil_1201_, v_cons_1202_, v_fields_1198_);
v___x_1204_ = l_Lean_mkAppB(v___x_1199_, v___x_1200_, v___x_1203_);
return v___x_1204_;
}
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___closed__0(void){
_start:
{
lean_object* v___x_1205_; lean_object* v___f_1206_; 
v___x_1205_ = l_Lean_instToExprString;
v___f_1206_ = lean_alloc_closure((void*)(l_Lean_instToExprPreresolved___lam__0), 2, 1);
lean_closure_set(v___f_1206_, 0, v___x_1205_);
return v___f_1206_;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___closed__2(void){
_start:
{
lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v___x_1211_ = lean_box(0);
v___x_1212_ = ((lean_object*)(l_Lean_instToExprPreresolved___closed__1));
v___x_1213_ = l_Lean_Expr_const___override(v___x_1212_, v___x_1211_);
return v___x_1213_;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved___closed__3(void){
_start:
{
lean_object* v___x_1214_; lean_object* v___f_1215_; lean_object* v___x_1216_; 
v___x_1214_ = lean_obj_once(&l_Lean_instToExprPreresolved___closed__2, &l_Lean_instToExprPreresolved___closed__2_once, _init_l_Lean_instToExprPreresolved___closed__2);
v___f_1215_ = lean_obj_once(&l_Lean_instToExprPreresolved___closed__0, &l_Lean_instToExprPreresolved___closed__0_once, _init_l_Lean_instToExprPreresolved___closed__0);
v___x_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1216_, 0, v___f_1215_);
lean_ctor_set(v___x_1216_, 1, v___x_1214_);
return v___x_1216_;
}
}
static lean_object* _init_l_Lean_instToExprPreresolved(void){
_start:
{
lean_object* v___x_1217_; 
v___x_1217_ = lean_obj_once(&l_Lean_instToExprPreresolved___closed__3, &l_Lean_instToExprPreresolved___closed__3_once, _init_l_Lean_instToExprPreresolved___closed__3);
return v___x_1217_;
}
}
lean_object* runtime_initialize_Lean_ToLevel(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Rat_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ToExpr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
